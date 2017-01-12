"use strict";

// TODO
//  - relooper multiloop self

// https://github.com/curiousdannii/ifvms.js/blob/83b9dca1a62b2f99ce6e2478c9e17cb52f0f8401/src/zvm/disassembler.js
// https://github.com/curiousdannii/ifvms.js/blob/83b9dca1a62b2f99ce6e2478c9e17cb52f0f8401/src/zvm/opcodes.js

// http://inform-fiction.org/zmachine/standards/z1point1/sect14.html


///
/// CodeBuilder indenter thing
///

function CodeBuilder() {
  this._code = [];
  this._indent = "";
}
CodeBuilder.prototype.add = function (c, /*opt*/noline) {
  if (noline && this._code.length > 0) {
    this._code[this._code.length-1] += c;
  } else {
    this._code.push(this._indent + c);
  }
  return this;
};
CodeBuilder.prototype.indent = function (/*opt*/c) {
  if (c !== void 0) {
    this.add(c);
  }
  this._indent = this._indent + "  ";
  return this;
};
CodeBuilder.prototype.dedent = function (/*opt*/c) {
  this._indent = this._indent.slice(0, -2);
  if (c !== void 0) {
    this.add(c);
  }
  return this;
};
CodeBuilder.prototype.toString = function () {
  return this._code.join('\n');
};

///
/// Utilities
///

function hexByte(b) {
  var s = (b&0xFF).toString(16);
  return "00".slice(s.length) + s;
}

function hexWord(w) {
  var s = w.toString(16);
  return "0000".slice(s.length) + s;
}

function gensym() {
  return "G_" +(++gensym.index);
}
gensym.index = 0;

function op_gensym() {
  return "tmp_" + (++op_gensym.index);
}
function reset_op_gensym() {
  op_gensym.index = 0;
}
reset_op_gensym();

///
/// Main memory
///

var coreData = null;

function loadData(encoding, data) {
  switch (encoding) {
  case "base64": {
    var raw = window.atob(data);
    var array = new Uint8Array(new ArrayBuffer(raw.length));
    for (var i = 0; i < raw.length; i++) {
      array[i] = raw.charCodeAt(i);
    }
    coreData = array;
    break;
  }
  default:
    throw new Error("Unknown encoding " + encoding);
  }
}


///
/// Disassembly
///

function Disassembler(zmach) {
  this.zmach = zmach;
  this.opcodes = {};
  this.string_addrs = new Set;
  this.routine_addrs = new Set;
  this.new_routine_addrs = new Set;
  this._pause = false;
  this._indcall = false;
}
Disassembler.prototype.add_string = function (addr) {
  this.string_addrs.add(addr);
};
Disassembler.prototype.add_routine = function (addr) {
  this.routine_addrs.add(addr);
  this.new_routine_addrs.add(addr);
};
Disassembler.prototype.get_new_routines = function () {
  var rs = Array.from(this.new_routine_addrs);
  this.new_routine_addrs.clear();
  return rs;
};
Disassembler.prototype.mark_pause = function () {
  this._pause = true;
};
Disassembler.prototype.mark_indcall = function () {
  this._indcall = true;
};
Disassembler.prototype.get_pause = function () {
  var p = this._pause;
  this._pause = false;
  return p;
};
Disassembler.prototype.get_indcall = function () {
  var ic = this._indcall;
  this._indcall = false;
  return ic;
};
Disassembler.prototype.disassemble = function (pc) {
  var offset, temp, code, opcode_class, operands_type, operands, store=null, branch=null;
  var zmach = this.zmach, opcodes = this.opcodes;
  
  function get_var_operand_types(operands_byte, operands_type) {
    for (var i = 0; i < 4; i++) {
      var op = (operands_byte & 0xC0) >> 6;
      if (op === 0x3) break;
      operands_type.push(op);
      operands_byte <<= 2;
    }
  }

  offset = pc;
  code = zmach.getU8(pc++);
  
  if (code === 0xBE) { // Extended instructions
    operands_type = null;
    code = zmach.getU8(pc++) + 1000;
  } else if ((code & 0xC0) === 0xC0) { // Variable form instructions
    operands_type = null;
    // 2OP instruction with VAR parameters
    if (!(code & 0x20)) code &= 0x1F;
  } else if ((code & 0xC0) === 0x80) { // short form instructions
    operands_type = [(code & 0x30) >> 4];
    // Clear the operand type if 1OP, keep for 0OPs
    if (operands_type[0] < 3) code &= 0xCF;
  } else { // Long form instructions
    operands_type = [code & 0x40 ? 2 : 1, code & 0x20 ? 2 : 1];
    code &= 0x1F;
  }

  if (!opcodes[code]) {
    throw new Error("Unknown opcode " + code + " at $" + hexWord(offset));
  }

  // Variable form operand types
  if (operands_type === null) {
    operands_type = [];
    get_var_operand_types(zmach.getU8(pc++), operands_type);
    // "double var" opcodes
    if (code == 236 || code == 250) {
      get_var_operand_types(zmach.getU8(pc++), operands_type);
    }
  }

  // Load the operands
  operands = [];
  for (temp = 0; temp < operands_type.length; temp++) {
    
    if (operands_type[temp] === 0) { // Large constant
      operands.push(["operand", zmach.getU16(pc)]);
      pc += 2;
    } else if (operands_type[temp] === 1) { // Small constant
      operands.push(["operand", zmach.getU8(pc++)]);
    } else if (operands_type[temp] === 2) { // Variable operand
      operands.push(["variable", zmach.getU8(pc++)]);
    }
  }

  opcode_class = opcodes[code].opts;

  if (opcode_class.store) {
    store = ["variable", zmach.getU8(pc++)];
  }
  if (opcode_class.branch) {
    temp = zmach.getU8(pc++);
    branch = ["branch",
              !!(temp & 0x80), // iftrue
              temp & 0x40 ?
              // 6-bit offset
              temp & 0x3F
              // sign-extended 14-bit offset
              : (temp << 8 | zmach.getU8(pc++)) << 18 >> 18
             ];
  }

  // Check for a text literal
  if (opcode_class.print) {
    operands.push(["string", pc, zmach.unicodeFromZSCII(zmach.getZSCII(pc))]);
    do {
      temp = zmach.getU16(pc);
      pc += 2;
    } while(!(temp & 0x8000) // stop bit
            && pc < coreData.length);
  }

  return {
    code:code, operands:operands, store:store, branch:branch,
    offset:offset, pc:pc,
    stop:!!opcode_class.stop,
    pause:!!opcode_class.pause
  };
};

function trans_branches(tr) {
  /* Gets addresses the instruction branches to */
  switch (tr[0]) {
  case "branch":
    return tr.slice(2).filter(function (br) {
      return !(br instanceof Array);
    });
  default:
    return null;
  }
}

Disassembler.prototype.trans = function (addr) {
  /* Translate basic blocks starting from addr */
  var opcodes = this.opcodes;

  this._pause = false;
  this._indcall = false;

  function simple_pop_remove(block) {
    var block2 = [];
    for (var i = 0; i + 1 < block.length; i++) {
      if (block[i][0] === "push"
          && block[i+1][0] === "pop") {
        block2.push(["set", block[i+1][1], block[i][1]]);
        i++;
      } else if (block[i][0] === "contstack" && block[i][2] === null
                 && block[i+1][0] === "pop") {
        block2.push(["contstack", block[i][1], block[i+1][1], block[i][3]]);
        i++;
      } else {
        block2.push(block[i]);
      }
    }
    block2.push(block[block.length-1]);
    return block2;
  }
  
  var code = {};
  var entries = new Set([addr]);
  var next = {};
  var to_visit = [addr];
  while (to_visit.length > 0) {
    var pc = to_visit.shift();
    if (code[pc]) continue;
    var inst = this.disassemble(pc);
    var translator = opcodes[inst.code].trans;
    if (!translator) throw new Error;
    reset_op_gensym();
    var tr = translator(inst);
    if (tr.val) debugger; //throw new Error;
    var last = tr.setup[tr.setup.length-1];
    var branches = trans_branches(last);
    if (branches !== null) {
      branches.forEach(function (br) { entries.add(br); });
      to_visit = to_visit.concat(branches);
    } else if (!inst.stop) {
      to_visit.push(inst.pc);
      next[pc] = inst.pc;
    }
    code[pc] = tr.setup;
  }

  var blocks = new Map;

  entries.forEach(function (addr) {
    var block = code[addr].slice();
    var pc = addr;
    while (next[pc]) {
      pc = next[pc];
      if (entries.has(pc)) {
        block.push(["branch", null, pc]);
        break;
      }
      block = block.concat(code[pc]);
    }
    blocks.set(addr, simple_pop_remove(block));
  });

  return blocks;
};

// configures a Disassembler with all opcodes
function attachOpcodes(disassembler) {
    // s1 >> s2
  function cc(s1, s2) {
    var setup = (s1.setup || []);
    if (s1.val) {
      setup = setup.concat(["ignore", s1.val]);
    }
    setup = setup.concat(s2.setup || []);
    return {setup:setup, val:s2.val};
  }
  // s1 >>= f
  function cbind(s1, f) {
    if (!s1.val) throw new Error;
    var s2 = f(s1.val);
    return {setup:(s1.setup||[]).concat(s2.setup||[]),
            val:s2.val};
  }
  // sequence ss >>= apply f
  function cbinds(ss, f) {
    var setup = [];
    var vals = [];
    for (var i = 0; i < ss.length; i++) {
      if (!ss[i].val) throw new Error;
      setup = setup.concat(ss[i].setup||[]);
      vals.push(ss[i].val);
    }
    var s2 = f.apply(null, vals);
    return {setup:setup.concat(s2.setup||[]),
            val:s2.val};
  }
  
  function op_trans(op) {
    var v;
    switch (op[0]) {
    case "operand":
      return {val:["lit", op[1]]};
    case "variable":
      if (op[1] === 0) {
        v = op_gensym();
        return {setup:[["pop", ["var", v]]],
                val:["var", v]};
      } else if (op[1] < 16) {
        return {val:["local", op[1]-1]};
      } else {
        return {val:["global", op[1]-16]};
      }
    case "string":
      disassembler.add_string(op[1]);
      return {val:["string", op[1], op[2]]};
    default:
      throw new Error;
    }
  }
  function op_indir_trans(v) {
    /* v is val */
    var g;
    switch (v[0]) {
    case "lit":
      return op_trans(["variable", v[1]]);
    default:
      g = op_gensym();
      return {setup:[["get_var", ["var", g], v]],
              val:["var", g]};
    }
  }
  function mk_set_indir(v, val, ignore) {
    var setup, upval;
    if (v[0] === "lit") {
      return mk_set(v[1], val, ignore);
    }
    if (ignore === "ignore") {
      return {setup:[["set_var", v, val]]};
    } else {
      upval = ["var",  op_gensym()];
      setup = [["set", upval, val],
               ["set_var", v, upval]];
      return {setup:setup,val:upval};
    }
  }
  
  function mk_set(varnum, val, ignore) {
    var setup, upval;
    if (varnum === 0) {
      setup = [["push", val]];
      upval = ["peek"];
    } else if (varnum < 16) {
      upval = ["local", varnum-1];
      setup = [["set", upval, val]];
    } else {
      upval = ["global", varnum-16];
      setup = [["set", upval, val]];
    }
    if (ignore === "ignore") {
      return {setup:setup};
    } else {
      return {setup:setup,val:upval};
    }
  }
  
  function mk_branch(inst, test) {
    var fallthrough = inst.pc, branch = inst.branch;
    var jumpaddr;
    if (branch[2] === 0 || branch[2] === 1) {
      jumpaddr = ["return", ["lit", branch[2]]];
    } else {
      jumpaddr = inst.pc + branch[2] - 2;
    }
    if (jumpaddr === fallthrough) {
      return {setup:[["ignore", test],
                     ["branch", null, jumpaddr]]};
    }
    if (branch[1]) {
      return {setup:[["branch", test, jumpaddr, fallthrough]]};
    } else {
      return {setup:[["branch", test, fallthrough, jumpaddr]]};
    }
  }
  
  function mk_j(_op) {
    var op = _op;
    if (typeof _op === "string") {
      op = function (a, b) { return [_op, a, b]; };
    }
    return function (inst) {
      var args = inst.operands.map(op_trans);
      return cbinds(args, function () {
        var test = op(arguments[0], arguments[arguments.length-1]);
        for (var i = arguments.length-2; i >= 1; i--) {
          test = ["or", op(arguments[0], arguments[i]), test];
        }
        return mk_branch(inst, test);
      });
    };
  }
  
  
  function mk_incdec(isinc) {
    return function (inst) {
      return cbinds(inst.operands.map(op_trans), function (a, v) {
        return cbind(op_indir_trans(a), function (aval) {
          var up = [isinc?"+":"-", aval, ["lit", 1]];
          if (inst.branch) {
            return cbind(mk_set_indir(a, up), function (newv) {
              return mk_branch(inst, [isinc?">":"<", newv, v]);
            });
          } else {
            return mk_set_indir(a, up, "ignore");
          }
        });
      });
    };
  }
  function mk_store(inst) { // for pull/store
    return cbinds([op_trans(inst.operands[0]),
                   op_trans(inst.operands[1] || ["variable", 0])],
                  function (a, v) {
                    return mk_set_indir(a, v, "ignore");
                  });
  }
  function mk_load(inst) {
    return cbind(op_trans(inst.operands[0]), function (a) {
      return cbind(op_indir_trans(a), function (aval) {
        return mk_set(inst.store[1], aval, "ignore");
      });
    });
  }

  function mk_op(_op, /*opt*/_brtest) {
    var op = _op;
    if (typeof _op === "string") {
      op = function () {
        var v = [_op];
        for (var i = 0; i < arguments.length; i++) v.push(arguments[i]);
        return v;
      };
    }
    var brtest = _brtest || function (t) { return ["!==", ["lit", 0], t]; };
    return function (inst) {
      return cbinds(inst.operands.map(op_trans), function () {
        var arglist = [];
        for (var i = 0; i < arguments.length; i++) arglist.push(arguments[i]);
        var v = op.apply(null, arglist);
        if (inst.store && inst.branch) {
          if (inst.pause) throw new Error;
          return cbind(mk_set(inst.store[1], v), function (t) {
            return mk_branch(inst, brtest(t));
          });
        } else if (inst.store) {
          if (inst.pause) {
            disassembler.mark_pause();
            if (inst.store[1] === 0) {
              return {setup: [["contstack", inst.pc, null, v]]};
            } else if (inst.store[1] < 16) {
              return {setup: [["cont", inst.pc, ["local", inst.store[1]-1], v]]};
            } else {
              return {setup: [["cont", inst.pc, ["global", inst.store[1]-16], v]]};
            }
          } else {
            return mk_set(inst.store[1], v, "ignore");
          }
        } else {
          if (inst.pause) {
            disassembler.mark_pause();
            return {setup: [["cont", inst.pc, null, v]]};
          } else {
            return {setup:[["ignore", v]]};
          }
        }
      });
    };
  }

  function mk_spec(name) {
    return function (inst) {
      if (opcodes[inst.code].opts.store) throw new Error;
      return cbinds(inst.operands.map(op_trans), function () {
        var v = [name];
        for (var i = 0; i < arguments.length; i++) {
          v.push(arguments[i]);
        }
        return {setup:[v]};
      });
    };
  }

  function mk_extern(ext) {
    return mk_op(function () {
      var v = ["extern", ext];
      for (var i = 0; i < arguments.length; i++) v.push(arguments[i]);
      return v;
    });
  }

  function mk_call(inst) {
    return cbinds(inst.operands.map(op_trans), function () {
      var v;
      var routine = arguments[0];
      switch (routine[0]) {
      case "lit":
        disassembler.add_routine(4*routine[1]);
        v = ["call", 4*routine[1]];
        break;
      default:
        disassembler.mark_indcall();
        v = ["indcall", routine];
      }
      for (var i = 1; i < arguments.length; i++) {
        v.push(arguments[i]);
      }
      if (inst.store) {
        if (inst.store[1] === 0) {
          return {setup: [["contstack", inst.pc, null, v]]};
        } if (inst.store[1] < 16) {
          return {setup: [["cont", inst.pc, ["local", inst.store[1]-1], v]]};
        } else {
          return {setup: [["cont", inst.pc, ["global", inst.store[1]-16], v]]};
        }
      } else {
        return {setup: [["cont", inst.pc, null, v]]};
      }
    });
  }

  function mk_jump(inst) {
    return cbind(op_trans(inst.operands[0]), function (off) {
      var ab;
      switch (off[0]) {
      case "lit":
        ab = (off[1] << 16 >> 16) + inst.pc - 2;
        return {setup:[["branch", null, ab]]};
      default:
        disassembler.mark_pause();
        return {setup:[["indjump", off]]};
      }
    });
  }

  var opcodes = disassembler.opcodes;

  function op(num, name, opts, trans) {
    var o = {num:num,
             name:name,
             opts:opts,
             trans:trans};
    opcodes[num] = o;
  }

  op(1, "je", {branch:1}, mk_j("==="));
  op(2, "jl", {branch:1}, mk_j("<"));
  op(3, "jg", {branch:1}, mk_j(">"));
  op(4, "dec_chk", {branch:1}, mk_incdec(false));
  op(5, "inc_chk", {branch:1}, mk_incdec(true));
  op(6, "jin", {branch:1}, mk_j(function (a, b) { return ["extern", "child_of", a, b];}));
  op(7, "test", {branch:1}, mk_j(function (a, b) { return ["===", ["&", a, b], b]; }));
  op(8, "or", {store:1}, mk_op("|"));
  op(9, "and", {store:1}, mk_op("&"));
  op(10, "test_attr", {branch:1}, mk_j(function (o, at) { return ["extern", "test_attr", o, at]; }));
  op(11, "set_attr", {}, mk_extern("set_attr"));
  op(12, "clear_attr", {}, mk_extern("clear_attr"));
  op(13, "store", {}, mk_store);
  op(14, "insert_obj", {}, mk_extern("insert_obj"));
  op(15, "loadw", {store:1}, mk_extern("getU16Elt"));
  op(16, "loadb", {store:1}, mk_extern("getU8Elt"));
  op(17, "get_prop", {store:1}, mk_extern("get_prop"));
  op(18, "get_prop_addr", {store:1}, mk_extern("get_prop_addr"));
  op(19, "get_next_prop", {store:1}, mk_extern("get_next_prop"));
  op(20, "add", {store:1}, mk_op("+"));
  op(21, "sub", {store:1}, mk_op("-"));
  op(22, "mul", {store:1}, mk_op("*"));
  op(23, "div", {store:1}, mk_op("div"));
  op(24, "mod", {store:1}, mk_op("mod"));
  op(25, "call_2s", {call:1,store:1}, mk_call);
  op(26, "call_2n", {call:1}, mk_call);
  op(27, "set_colour", {}, mk_extern("set_colour"));
  op(28, "throw", {stop:1}, mk_spec("throw")); // intentionally no pause
  op(128, "jz", {branch:1}, mk_j(function (a) { return ["===", ["lit", 0], a]; }));
  op(129, "get_sibling", {branch:1,store:1}, mk_extern("get_sibling"));
  op(130, "get_child", {branch:1,store:1}, mk_extern("get_child"));
  op(131, "get_parent", {store:1}, mk_extern("get_parent"));
  op(132, "get_prop_length", {store:1}, mk_extern("get_prop_length"));
  op(133, "inc", {}, mk_incdec(true));
  op(134, "dec", {}, mk_incdec(false));
  op(135, "print_addr", {}, mk_extern("print"));
  op(136, "call_1s", {call:1,store:1}, mk_call);
  op(137, "remove_obj", {}, mk_extern("remove_obj"));
  op(138, "print_obj", {}, mk_extern("print_obj"));
  op(139, "ret", {stop:1}, mk_spec("return"));
  op(140, "jump", {stop:1,jump:1}, mk_jump);
  op(141, "print_paddr", {}, mk_extern("print_paddr"));
  op(142, "load", {store:1}, mk_load);
  op(143, "call_1n", {call:1}, mk_call);
  op(176, "rtrue", {stop:1}, function () { return {setup:[["return", ["lit", 1]]]};});
  op(177, "rfalse", {stop:1}, function () { return {setup:[["return", ["lit", 0]]]};});
  op(178, "print", {print:1}, mk_extern("print"));
  op(179, "print_ret", {stop:1,print:1}, function (inst) {
    return cc(mk_extern("print")(inst), {setup:[["ignore", ["extern", "newline"]],
                                                ["return", ["lit", 1]]]});
  });
  op(180, "nop", {}, function () { return {}; });
  op(183, "restart", {stop:1}, mk_spec("restart"));
  op(184, "ret_popped", {stop:1}, function () {
    var g = ["var", op_gensym()];
    return {setup:[["pop", g],
                   ["return", g]]};});
  op(185, "catch", {store:1}, mk_op("catch"));
  op(186, "quit", {stop:1}, mk_spec("quit"));
  op(187, "new_line", {}, mk_extern("newline"));
  op(189, "verify", {stop:1,branch:1}, function (inst) { return mk_branch(inst, ["lit", 1]); });
  op(191, "piracy", {stop:1,branch:1}, function (inst) { return mk_branch(inst, ["lit", 1]); });
  op(224, "call_vs", {call:1,store:1}, mk_call);
  op(225, "storew", {}, mk_extern("setU16Elt"));
  op(226, "storeb", {}, mk_extern("setU8Elt"));
  op(227, "put_prop", {}, mk_extern("put_prop"));
  op(228, "aread", {pause:1,store:1}, mk_extern("aread")); // TODO
  op(229, "print_char", {}, mk_extern("print_char"));
  op(230, "print_num", {}, mk_extern("print_num"));
  op(231, "random", {store:1}, mk_extern("random"));
  op(232, "push", {}, mk_spec("push"));
  op(233, "pull", {}, mk_store);
  op(234, "split_window", {}, mk_extern("split_window"));
  op(235, "set_window", {}, mk_extern("set_window"));
  op(236, "call_vs2", {call:1,store:1}, mk_call);
  op(237, "erase_window", {}, mk_extern("erase_window"));
  op(238, "erase_line", {}, mk_extern("erase_line"));
  op(239, "set_cursor", {}, mk_extern("set_cursor"));
  op(240, "get_cursor", {pause:1}, mk_extern("get_cursor")); // TODO
  op(241, "set_text_style", {}, mk_extern("set_text_style"));
  op(242, "buffer_mode", {}, mk_extern("buffer_mode"));
  op(243, "output_stream", {}, mk_extern("output_stream"));
  op(244, "input_stream", {}, mk_extern("input_stream"));
  op(245, "sound_effect", {}, mk_extern("sound_effect"));
  op(246, "read_char", {pause:1,store:1}, mk_extern("read_char")); // TODO
  op(247, "scan_table", {branch:1,store:1}, mk_extern("scan_table"));
  op(248, "not", {store:1}, mk_op("not"));
  op(249, "call_vn", {call:1}, mk_call);
  op(250, "call_vn2", {call:1}, mk_call);
  op(251, "tokenise", {}, mk_extern("tokenise"));
  op(252, "encode_text", {}, mk_extern("encode_text"));
  op(253, "copy_table", {}, mk_extern("copy_table"));
  op(254, "print_table", {}, mk_extern("print_table"));
  op(255, "check_arg_count", {branch:1}, function (inst) {
    return cbind(op_trans(inst.operands[0]), function (an) {
      return mk_branch(inst, ["<=", an, ["var", "__numargs__"]]);
    });
  });
  op(1000, "save", {pause:1,store:1}, mk_extern("save")); // TODO
  op(1001, "restore", {pause:1,store:1}, mk_extern("restore")); // TODO
  op(1002, "log_shift", {store:1}, mk_op("log_shift"));
  op(1003, "art_shift", {store:1}, mk_op("art_shift"));
  op(1004, "set_font", {store:1}, mk_extern("set_font"));
  op(1009, "save_undo", {pause:1,store:1}, mk_extern("save_undo")); // TODO
  op(1010, "restore_undo", {pause:1,store:1}, mk_extern("restore_undo")); // TODO
  op(1011, "print_unicode", {}, mk_extern("print_unicode"));
  op(1012, "check_unicode", {store:1}, mk_extern("check_unicode"));
  op(1013, "set_true_colour", {}, mk_extern("set_true_colour"));
}

///
/// Higher-level restructuring
///

function block_branches(block) {
  return trans_branches(block[block.length-1]) || [];
}

// (relooper is in relooper.js)

function br_is_break(br) { return br instanceof Array && br[0] === "break"; }
function br_is_continue(br) { return br instanceof Array && br[0] === "continue"; }
function br_is_return(br) { return br instanceof Array && br[0] === "return"; }
function br_is_addr(br) { return !(br instanceof Array); }

// converts relooped code to IR
function build_code(b) {
  return blockify(_build_code(b, []));

  // hard to eliminate labels while generating code because of scavenging
  function _build_code(b) {
    function proc_label(code, br) {
      if (br_is_addr(br)) {
        return [["set", ["var", "__label__"], ["lit", br]]];
      } else if (br_is_continue(br) || br_is_break(br)) {
        return [["set", ["var", "__label__"], ["lit", br[2]]],
                [br[0], br[1]]];
      } else if (br_is_return(br)) {
        return [br];
      } else throw new Error;
    }
    function scavenge(label) {
      var h;
      if (br_is_addr(label)
          && next && next instanceof Multiple) {
        var idx = next.handled.findIndex(function (h) {
          return -1 !== h.entries().indexOf(label);
        });
        if (idx !== -1) {
          h = next.handled[idx];
          var handled = next.handled.slice();
          handled.splice(idx, 1);
          next = new Multiple(next.name, handled, next.next);
          return [["block", next.name, _build_code(h)]];
        }
      }
      if (br_is_addr(label)
          && next && next instanceof Simple && next.label === label) {
        // ASSUMPTION: in a branch, the labels are different
        // (next block can only be simple if return/break/continue other branch)
        h = next;
        next = null;
        return _build_code(h);
      }
      return proc_label([], label);
    }
    var code, next, last;

    if (!b) {
      return [];
    } else if (b instanceof Simple) {
      code = [["comment", b.label]].concat(b.block.slice(0, -1));
      next = b.next;
      last = b.block[b.block.length-1];
      if (last[0] !== "branch") {
        code.push(last);
      } else {
        var test = last[1],
            iftrue = last[2],
            iffalse = last[3];
        if (test === null) {
          code = code.concat(scavenge(iftrue));
        } else {
          code.push(["if", test, scavenge(iftrue), scavenge(iffalse)]);
        }
      }
      if (next) {
        code = code.concat(_build_code(next));
      }
      return code;
    } else if (b instanceof Loop) {
      return [["loop", b.name, _build_code(b.inner)]].concat(_build_code(b.next));
    } else if (b instanceof Multiple) {
      if (b.handled.length === 0) {
        return _build_code(b.next);
      }
      var entries = b.handled.map(function (h) { return [h.entries(), _build_code(h)];});
      return [["switch", b.name, ["var", "__label__"], entries]].concat(_build_code(b.next));
    } else {
      throw new Error;
    }
  }
}

// takes a list of instructions and sequences them (using "block" if
// plural).
function blockify(codes) {
  if (codes.length === 1) {
    return codes[0];
  } else {
    return ["block", null, codes];
  }
}

///
/// IR to javascript
///

function convert_routine_to_js(zmach, rname, locals, code, pauseable, is_cont) {
  var local_variables = new Set;
  function variable(v) {
    switch (v[0]) {
    case "local":
      return "arg_" + v[1];
    case "global":
      return "e.getGlobal(" + v[1] + ")";
    case "var":
      local_variables.add(v[1]);
      return v[1];
    default:
      throw new Error(v[0]);
    }
  }
  function setVariable(v, val) {
    switch (v[0]) {
    case "local":
      return "arg_" + v[1] + " = " + val;
    case "global":
      return "e.setGlobal(" + v[1] + ", " + val + ")";
    case "var":
      local_variables.add(v[1]);
      return v[1] + " = " + val;
    default:
      throw new Error(v[0]);
    }
  }
  function convert_seq(codes, cb) {
    for (var i = 0; i < codes.length; i++) {
      convert_statement(codes[i], cb);
    }
  }
  function convert_statement(code, cb) {
    switch(code[0]) {
    case "block":
      if (code[1] !== null) {
        cb.indent(code[1] + ": {");
      }
      convert_seq(code[2], cb);
      if (code[1] !== null) {
        cb.dedent("}");
      }
      break;
    case "switch":
      if (code[1]) {
        cb.add(code[1] + ":");
      }
      cb.add("switch (" + convert_expr(code[2]) + ") {");
      code[3].forEach(function (entry) {
        entry[0].forEach(function (addr) {
          cb.add("case " + addr + ":");
        });
        cb.indent();
        convert_seq(entry[1], cb);
        cb.add("break;");
        cb.dedent();
      });
      cb.add("}");
      break;
    case "loop":
      if (code[1]) {
        cb.add(code[1] + ":");
      }
      cb.indent("while (true) {");
      convert_seq(code[2], cb);
      cb.dedent("}");
      break;
    case "if":
      function check_only_if(cons) {
        if (cons.length === 1 && cons[0][0] === "if") return cons[0];
        else if (cons.length === 2 && cons[0][0] === "comment" && cons[1][0] === "if") return cons[1];
        else return null;
      }
      cb.indent("if (" + convert_expr(code[1]) + ") {");
      convert_seq(code[2], cb);
      var alt = check_only_if(code[3]);
      while (alt) {
        code = alt;
        cb.dedent();
        cb.indent("} else if (" + convert_expr(code[1]) + ") {");
        convert_seq(code[2], cb);
        alt = check_only_if(code[3]);
      }
      if (code[3].length === 0) {
        cb.dedent("}");
      } else {
        cb.dedent();
        cb.indent("} else {");
        convert_seq(code[3], cb);
        cb.dedent("}");
      }
      break;
    case "break":
      if (code[1] !== null) {
        cb.add("break " + code[1] + ";");
      } else {
        cb.add("break;");
      }
      break;
    case "continue":
      if (code[1] !== null) {
        cb.add("continue " + code[1] + ";");
      } else {
        cb.add("continue;");
      }
      break;
    case "return":
      cb.add("return " + convert_expr(code[1]) + ";");
      break;
    case "quit":
      cb.add("e.abort();");
      break;
    case "cont":
      var routine = zmach.routines.get(code[3][1]);
      if (code[3][0] === "call" && routine && !routine.pauseable) {
        // TODO move this to separate optimization pass
        if (code[2] === null) {
          cb.add(convert_expr(code[3]) + ";");
        } else {
          cb.add(setVariable(code[2], convert_expr(code[3])) + ";");
        }
        break;
      }
      local_variables.add("__cont__");
      if (code[2] === null) {
        cb.add("__cont__ = " + code[1] + "<<9|0<<8|0;");
        cb.add(convert_expr(code[3]) + ";");
      } else {
        var varnum;
        if (code[2][0] === "local") varnum = code[2][1] + 1;
        else if (code[2][0] === "global") varnum = code[2][1] + 16;
        else throw new Error;

        cb.add("__cont__ = " + code[1] + "<<9|0<<8|"+varnum+";");
        cb.add(setVariable(code[2], convert_expr(code[3])) + ";");
      }
      break;
    case "contstack":
      local_variables.add("__cont__");
      cb.add("__cont__ = " + code[1] + "<<9|1<<8|0;");
      if (code[2] === null) {
        local_variables.add("__stack__");
        cb.add("__stack__.push(" + convert_expr(code[3]) + ");");
      } else {
        cb.add(setVariable(code[2], convert_expr(code[3])) + ";");
      }
      break;
    case "push":
      local_variables.add("__stack__");
      cb.add("__stack__.push(" + convert_expr(code[1]) + ");");
      break;
    case "pop":
      local_variables.add("__stack__");
      cb.add(setVariable(code[1], "__stack__.pop()") + ";");
      break;
    case "set":
      cb.add(setVariable(code[1], convert_expr(code[2])) + ";");
      break;
    case "get_var":
      local_variables.add("__stack__");
      var tmp = gensym();
      cb.add(setVariable(["var", tmp], convert_expr(code[2])) + ";");
      cb.add("switch ("+tmp+") {");
      cb.indent("case 0:"); {
        cb.add(setVariable(code[1], "__stack__[__stack__.length-1]") + ";");
        cb.add("break;");
        cb.dedent(); }
      for (var i = 0; i < locals; i++) {
        cb.indent("case "+(i+1)+":"); {
          cb.add(setVariable(code[1], variable(["local", i])) + ";");
          cb.add("break;");
          cb.dedent(); }
      }
      if (i < 15) {
        for (; i < 15; i++) {
          cb.add("case "+(i+1)+":");
        }
        cb.indent();
        cb.add("throw new Error('invalid get_var',"+tmp+");");
        cb.dedent();
      }
      cb.indent("default:"); {
        cb.add(setVariable(code[1], "e.getGlobal("+tmp+" - 16)")+";");
        cb.dedent(); }
      cb.add("}");
      break;
    case "ignore":
      cb.add(convert_expr(code[1]) + ";");
      break;
    case "comment":
//      cb.add("// $" + hexWord(code[1]));
      break;
    case "restart":
      cb.add("throw new Error('Game wants to restart');");
      break;
    default:
      throw new Error(code[0]);
    }
  }
  function convert_expr(_code) {
    var litprec = 20;
    var stack = [];
    var vstack = [];
    stack.push({code:_code, i:0});
    while (stack.length > 0) {
      var state = stack.pop();
      if (optable.has(state.code[0])) {
        if (1 + state.i < state.code.length) {
          stack.push({code:state.code, i:state.i+1});
          stack.push({code:state.code[state.i+1], i:0});
        } else {
          var op = optable.get(state.code[0]);
          var args = vstack.splice(-state.code.length+1,state.code.length-1);
          vstack.push(op.f.apply(null, [op].concat(args)));
        }
        continue;
      }
      switch (state.code[0]) {
      case "lit":
        vstack.push({js:""+state.code[1], prec:litprec});
        break;
      case "string":
        vstack.push({js:"/* " + JSON.stringify(state.code[2]) + " */ " + state.code[1],
                     prec:litprec});
        break;
      case "global":
      case "local":
      case "var":
        vstack.push({js:variable(state.code), prec:litprec});
        break;
      case "peek":
        local_variables.add("__stack__");
        vstack.push({js:"__stack__[__stack__.length-1]", prec:litprec});
        break;
      case "call":
        var numargs = state.code.length-2;
        if (state.i<numargs) {
          stack.push({code:state.code, i:state.i+1});
          stack.push({code:state.code[state.i+2], i:0});
          break;
        } else {
          var args = vstack.splice(-numargs,numargs);
          vstack.push({js:"e.r$"+hexWord(state.code[1])+"("+op_join_comma(args)+")",
                       prec:17});
          break;
        }
      case "indcall":
        var numargs = state.code.length-1;
        if (state.i<numargs) {
          stack.push({code:state.code, i:state.i+1});
          stack.push({code:state.code[state.i+1], i:0});
          break;
        } else {
          var args = vstack.splice(-numargs,numargs);
          vstack.push({js:"e.pindcall("+op_join_comma(args)+")",
                       prec:17});
          break;
        }
      case "extern":
        var numargs = state.code.length-2;
        if (state.i<numargs) {
          stack.push({code:state.code, i:state.i+1});
          stack.push({code:state.code[state.i+2], i:0});
          break;
        } else {
          var args = vstack.splice(-numargs,numargs);
          vstack.push({js:"e."+state.code[1]+"("+op_join_comma(args)+")",
                       prec:17});
          break;
        }
      case "resumeframe":
        vstack.push({js:"__frame__.child === null ? (() => {/*debugger;*/ return __contval__;})() : e.resume(__frame__.child, __contval__)",
                     prec:4});
        break;
      default:
        debugger;
        throw new Error(state.code[0]);
      }
    }
    if (vstack.length !== 1) throw new Error;
    return vstack[0].js;
  }

  var arglist = [];
  for (var i = 0; i < locals; i++) {
    arglist.push("arg_" + i);
  }

  var cb = new CodeBuilder();
  // deferring function header and local variable definitions
  cb.indent();
  if (pauseable) {
    cb.indent("try {");
  }
  convert_statement(code, cb);
  if (pauseable) {
/*    if (!local_variables.has("__cont__")) {
      throw new Error;
    }*/
    cb.dedent();
    cb.indent("} catch (x) {");
    cb.indent("if (x instanceof PauseException) {");
    var localsarg = '['+arglist.join(',')+']';
    var stackarg = local_variables.has("__stack__")?"Array.from(__stack__)":"[]";
    local_variables.add("__numargs__");
    var makeframe = "new CallFrame(__numargs__, "+localsarg+", "+stackarg+", __cont__, x.frame)";
    cb.add("throw new PauseException(x.action, x.args, "+makeframe+");");
    cb.dedent();
    cb.indent("} else {");
    cb.add("console.error(__cont__);");
    cb.add("throw x;");
    cb.dedent("}");
    cb.dedent("}");
  }
  cb.add("throw new Error('fell off end of routine');");
  cb.dedent("}");

  var vardefs = "";
  if (local_variables.size > 0) {
    var varstrings = Array.from(local_variables);
    varstrings.sort();
    vardefs += "  var " + varstrings.join(", ") + ";\n";
  }
  if (local_variables.has("__numargs__")) {
    if (is_cont) {
      vardefs += "  __numargs__ = __frame__.numargs;\n";
    } else {
      vardefs += "  __numargs__ = arguments.length;\n";
    }
  }
  if (local_variables.has("__stack__")) {
    if (is_cont) {
      vardefs += "  __stack__ = __frame__.stack.slice();\n";
    } else {
      vardefs += "  __stack__ = [];\n";
    }
  }

  if (is_cont) {
    for (var i = 0; i < arglist.length; i++) {
      vardefs += "  var "+arglist[i]+" = __frame__.locals["+i+"];\n";
    }
  } else {
    if (locals > 0) {
      vardefs += "  " + arglist.slice(0,8).map(function (v) { return v+" |= 0;"; }).join(" ") + "\n";
      if (locals > 8) {
        vardefs += "  " + arglist.slice(8).map(function (v) { return v+" |= 0;"; }).join(" ") + "\n";
      }
    }
  }
  //vardefs = "console.log('trace "+rname+"');\n"+vardefs;

  var arglist2 = arglist;
  if (is_cont) {
    arglist2 = ["__frame__", "__contval__"];
  }

  return ("function " + rname + "(" + arglist2.join(", ") + ") {\n"
          +"  \"use strict\";\n"
          + vardefs + cb.toString());
}

function parens(oprec, a) {
  if (oprec < a.prec) {
    return a.js;
  } else {
    return "(" + a.js + ")";
  }
}
function to_signed(a) {
  return {js:parens(12, a)+" << 16 >> 16", prec:12};
}
function to_unsigned(a) {
  return {js:parens(9, a)+" & 0xFFFF", prec:9};
}
function arith_unsigned_op(op, a, b) {
  return to_unsigned({js:parens(op.prec, a)+" "+op.op+" "+parens(op.prec, b),
                      prec:op.prec});
}
function arith_signed_op(op, a, b) {
  return to_unsigned({js:parens(op.prec, to_signed(a))
                      +" "+op.op+" "+parens(op.prec, to_signed(b)),
                      prec:op.prec});
}
function arith_cmp_op(op, a, b) {
  return {js:parens(op.prec, to_signed(a))+" "+op.op+" "+parens(op.prec, to_signed(b)),
          prec:op.prec};
}
function plain_op(op, a, b) {
  return {js:parens(op.prec, a)+" "+op.op+" "+parens(op.prec, b),
          prec:op.prec};
}
function plain_prefix_op(op, a) {
  return {js:op.op+parens(op.prec, a),
          prec:op.prec};
}
// https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Operators/Operator_Precedence
var optable = new Map;
optable.set("or", {prec:5, op:"||", f:plain_op});
optable.set("and", {prec:6, op:"&&", f:plain_op});
optable.set("|", {prec:7, op:"|", f:plain_op});
optable.set("&", {prec:9, op:"&", f:plain_op});
optable.set("===", {prec:10, op:"===", f:plain_op});
optable.set("!==", {prec:10, op:"!==", f:plain_op});
optable.set("<", {prec:11, op:"<", f:arith_cmp_op});
optable.set(">", {prec:11, op:">", f:arith_cmp_op});
optable.set("<=", {prec:11, op:"<=", f:arith_cmp_op});
optable.set(">=", {prec:11, op:">=", f:arith_cmp_op});
optable.set("+", {prec:13, op:"+", f:arith_unsigned_op});
optable.set("-", {prec:13, op:"-", f:arith_unsigned_op});
optable.set("*", {prec:14, op:"*", f:arith_unsigned_op});
optable.set("div", {prec:14, op:"/", f:arith_signed_op});
optable.set("mod", {prec:14, op:"%", f:arith_signed_op});
optable.set("not", {prec:15, op:"!", f:plain_prefix_op});
function op_join_comma(vals) {
  return vals.map(function (a) { return parens(0, a); }).join(", ");
}

function optimize_code(code) {
  code = remove_breaks(code);
  code = remove_labelsets(code);
  code = simplify_ifs(code);
  //code = eliminate_stack(code);
  return code;
}

function Routine(addr, locals, code) {
  this.addr = addr;
  this.locals = locals;
  this.code = code;

  this.pauseable = null;
  this.compiled = null;
  this.temporary = false;
}

///
/// Printing routines for debugging
///

function sexp(l) {
  if (l instanceof Array) {
    if (l[0] === "string" && window.zmach) {
      var zmach = window.zmach;
      var s = zmach.unicodeFromZSCII(zmach.getZSCII(l[1]))
      return JSON.stringify(s);
    }
    return "(" + l.map(sexp).join(" ") + ")";
  } else if (typeof l === "number") {
    return "$" + hexWord(l);
  } else {
    return ''+l;
  }
}

function pp(l) {
  var cb = new CodeBuilder;
  function _pp(l) {
    if (l instanceof Array) {
      switch (l[0]) {
      case "if":
        cb.indent("(if " + sexp(l[1]));
        cb.indent("(then");
        l[2].forEach(_pp);
        cb.add(")", true); cb.dedent();
        if (l[3].length > 0) {
          cb.indent("(else");
          l[3].forEach(_pp);
          cb.add(")", true); cb.dedent();
        }
        cb.add(")", true);
        cb.dedent();
        break;
      case "block":
        cb.indent("(block " + l[1]);
        l[2].forEach(_pp);
        cb.add(")", true); cb.dedent();
        break;
      case "switch":
        cb.indent("(switch " + l[1] + " " + sexp(l[2]));
        if (l[3] === void 0) debugger;
        l[3].forEach(function (ent) {
          cb.indent("(" + sexp(ent[0]));
          ent[1].forEach(_pp);
          cb.add(")", true); cb.dedent();
        });
        cb.add(")", true); cb.dedent();
        break;
      case "loop":
        cb.indent("(loop " + l[1]);
        l[2].forEach(_pp);
        cb.add(")", true); cb.dedent();
        break;
      case "comment":
        cb.add("; $" + hexWord(l[1]));
        break;
      default:
        cb.add(sexp(l));
      }
    } else {
      cb.add(sexp(l));
    }
  }
  _pp(l);
  return cb.toString();
}


///
/// The Z-Machine runtime (with recompilation-based interpreter)
///

function ZMachine(data) {
  if (!(data instanceof Uint8Array)) throw new Error("data must be Uint8Array");

  this.pristine_data = data;
  this.data = data.slice(0);
  this.dv = new DataView(this.data.buffer);

  this.dis = new Disassembler(this);
  attachOpcodes(this.dis);
  this.routines = new Map;
  this.conts = new Map;

  if (this.getU8(0) !== 5)
    throw new Error("can only zupport z5");

  this.entry = this.getU16(0x06);
  this.staticStart = this.getU16(0x0E);
  this.highStart = this.getU16(0x04);
  this.extension = this.getU16(0x36);
  if (this.extension !== 0) {
    this.numExtensions = this.getU16(this.extension);
  }
  this.dict = this.getU16(0x08);

  this.objTable = this.getU16(0x0a);

  if (this.staticStart < 64) throw new Error("consistency error");
  // spec says this.highStart >= this.staticStart, but Zork is a counterexample!
  
  this.globalBase = this.getU16(0x0C);

  this.checkpoints = [];

  var alphabets_addr = this.getU16(0x34);
  if (alphabets_addr !== 0) {
    this.alphabets = new Uint8Array(this.data.subarray(alphabets_addr, alphabets_addr+78));
  } else {
    this.alphabets = new Uint8Array(new ArrayBuffer(78));
    var std_alphabets = [
      "abcdefghijklmnopqrstuvwxyz",
      "ABCDEFGHIJKLMNOPQRSTUVWXYZ",
      " \r0123456789.,!?_#'\"/\\-:()"
    ];
    for (var i = 0; i < 3; i++) {
      for (var j = 0; j < 26; j++) {
        this.alphabets[i*26+j] = std_alphabets[i].charCodeAt(j);
      }
    }
  }

  if (this.hasExtension(3)) {
    var unicode_base = this.getExtension(3);
    var unicode_length = this.getU8(unicode_base);
    this.unicode = [];
    for (var i = 0; i < unicode_length; i++) {
      this.unicode[i] = this.getU16Elt(unicode_base+1, i);
    }
  } else {
    // default unicode table for 155--223
    this.unicode =
      [0xe4,0xf6,0xfc,0xc4,0xd6,0xdc,0xdf,0xbb,0xab,0xeb,0xef,0xff,0xcb,0xcf,0xe1,0xe9,0xed,0xf3,0xfa,
       0xfd,0xc1,0xc9,0xcd,0xd3,0xda,0xdd,0xe0,0xe8,0xec,0xf2,0xf9,0xc0,0xc8,0xcc,0xd2,0xd9,0xe2,0xea,
       0xee,0xf4,0xfb,0xc2,0xca,0xce,0xd4,0xdb,0xe5,0xc5,0xf8,0xd8,0xe3,0xf1,0xf5,0xc3,0xd1,0xd5,0xe6,
       0xc6,0xe7,0xc7,0xfe,0xf0,0xde,0xd0,0xa3,0x153,0x152,0xa1,0xbf];
  }

  this.true_colors = [
    -2, -1, // current, default
    0x0000, 0x001D, 0x0340, 0x03BD, // black, red, green, yellow,
    0x59A0, 0x7C1F, 0x77A0, 0x7FFF, // blue, magenta, cyan, white,
    0x5AD6, 0x4631, 0x2D6B, // light grey, medium grey, dark grey,
    null, null, -4, // reserved, reserved, transparent
  ];

  this.screen = null;

  this._scheduled_compiles = [];
  this._compilation_task_timeout = null;
}
// Initialization
ZMachine.prototype.reset = function () {
  var flags1 = this.getU8(0x1);
  flags1 |= ZMachine.FLAGS1_COLORS;
  flags1 |= ZMachine.FLAGS1_BOLDFACE;
  flags1 |= ZMachine.FLAGS1_ITALIC;
  flags1 |= ZMachine.FLAGS1_FIXEDSPACE;
  flags1 &= ~ZMachine.FLAGS1_TIMEDINPUT;
  this.setU8(0x1, flags1);

  var flags2 = this.getU16(0x10);
  flags2 &=~ZMachine.FLAGS2_PICTURES;
  flags2 &=~ZMachine.FLAGS2_SOUND;
  this.setU16(0x10, flags2);

  this.setU8(0x1E, 6/* IBM PC */); // Interpreter number
  this.setU8(0x1F, 'J'.charCodeAt(0)); // Interpreter version

  this.setDim(this.screen.lines, this.screen.cols);

  this.setU8(0x2C, 9/*white*/); // default background color
  this.setU8(0x2D, 2/*black*/); // default foreground color
  
  this.setU16(0x32, 0x0101); // standard version number

  //var flags3 = this.getExtension(4); // only v6

  this.setExtension(5, this.true_colors[9]);
  this.setExtension(6, this.true_colors[2]);

  this.screen.setBackground(this.true_colors[9]);
  this.screen.setForeground(this.true_colors[2]);

  this.stream3 = [];
};
ZMachine.prototype.set_screen = function (screen) {
  this.screen = screen;
};
ZMachine.prototype.setDim = function (height, width) {
  this.setU8(0x20, height);
  this.setU8(0x21, width);
  this.setU16(0x22, 800); // pixel width
  this.setU16(0x24, 400); // pixel height
  this.setU8(0x26, 10); // font width in pixels (for '0')
  this.setU8(0x27, 16); // font height in pixels (for '0')
};

// Interpreter
ZMachine.prototype.run = function () {
  this.reset();
  try {
    this.get_routine(this.entry-1);
    this.indcall(this.entry-1);
  } catch (x) {
    if (x instanceof PauseException) {
      this.handle_pause(x);
    } else {
      this.screen.error(x.toString());
      throw x;
    }
  }
};
ZMachine.prototype.resume = function (frame, ret) {
  return this.get_cont(frame)(frame, ret);
//  frame.describe();
};
ZMachine.prototype.outer_resume = function (frame, ret) {
  try {
    this.resume(frame, ret);
  } catch (x) {
    if (x instanceof PauseException) {
      this.handle_pause(x);
    } else {
      this.screen.error(x.toString());
      throw x;
    }
  }
};
ZMachine.prototype.handle_pause = function (pause, nosave) {
  var self = this;
  switch (pause.action) {
  case "aread":
    if (!nosave) {
      this.save_state("aread", pause);
    }
    var read_buffer = pause.args[0];
    var init = this.data.subarray(read_buffer+2, read_buffer+2+this.getU8(1+read_buffer));
    this.screen.read(this.unicodeFromZSCII(init), function (str) {
      self.do_aread(read_buffer, pause.args[1], str);
      self.outer_resume(pause.frame, 13);
    });
//      console.log(pause);
//    pause.frame.describe();

    break;
  case "read_char":
    var read_char_timer;
    if (pause.args[0] !== 0 && pause.args[1] !== 0) {
      read_char_timer = window.setInterval(function () {
        var res;
        try {
          res = self.pindcall(pause.args[1]);
        } catch(x) {
          throw new Error('Exception thrown in read_char time routine');
        }
        if (res) {
          window.clearInterval(read_char_timer);
          self.screen.cancel_read_char();
          self.outer_resume(pause.frame, 0);
        }
      }, pause.args[0] * 100);
    }
    this.screen.read_char(function (c) {
      window.clearInterval(read_char_timer);
      self.outer_resume(pause.frame, c);
    });
    break;
  case "save_undo":
    this.save_state("save_undo", pause);
    this._undo = this.checkpoints[this.checkpoints.length-1];
    this.outer_resume(pause.frame, 1);
    break;
  case "restore_undo":
    if (this._undo) {
      var undo = this._undo;
      this._undo = null;
      this.data.set(undo.dynamic);
      this.outer_resume(undo.pause.frame, 2);
    } else {
      this.outer_resume(pause.frame, 0);
    }
    break;
  default:
    throw new Error("Unhandled pause action: " + pause.action);
  }
};
ZMachine.prototype.pindcall = function (paddr) {
  var args = new Array(arguments.length-1);
  for (var i = 1; i < arguments.length; i++) {
    args[i-1] = arguments[i];
  }
  //console.log("pindcall", hexWord(4*paddr));
  var routine = this.get_routine(4*paddr);
  return routine.compiled.apply(null, args);
};
ZMachine.prototype.indcall = function (addr) {
  var args = new Array(arguments.length-1);
  for (var i = 1; i < arguments.length; i++) {
    args[i-1] = arguments[i];
  }
  var routine = this.get_routine(addr);
  return routine.compiled.apply(null, args);
};
ZMachine.prototype.debug = function (addr) {
  debugger;
  return this.indcall(addr);
};
ZMachine.prototype.make_routine_stub = function (addr) {
  if (!this.routines.has(addr)) {
    var self = this;
    this['r$'+hexWord(addr)] = function stub() {
      return self.get_routine(addr).compiled.apply(null, arguments);
    };
  }
};
ZMachine.prototype.schedule_compilation_task = function () {
  if (this._compilation_task_timeout === null) {
    var self = this;
    this._compilation_task_timeout = window.setTimeout(function () {
      self._compilation_task_timeout = null;
      self.compilation_task();
    }, 0);
  }
};
ZMachine.prototype.compilation_task = function () {
  /* compiles things in this._scheduled_compiles */

  if (this._scheduled_compiles.length === 0) {
    return;
  }
  var raddrs = [];
  var addrs_to_see = [this._scheduled_compiles.pop()];
  var routine;
  while (addrs_to_see.length > 0) {
    var raddr = addrs_to_see.pop();
    if (-1 !== raddrs.indexOf(raddr))
      continue;
    routine = this.routines.get(raddr);
    if (routine && !routine.temporary)
      continue;
    raddrs.push(raddr);
    var numlocals = this.getU8(raddr);
    var code;
    if (raddr === 0) {
      code = ["return", ["lit", 0]];
    } else {
      var blocks = this.dis.trans(raddr+1);
      code = build_code(reloop(blocks, [raddr+1]));
    }
    routine = new Routine(raddr, numlocals, code);
    this.routines.set(raddr, routine);
    var r_addresses = this.dis.get_new_routines();
    routine.calls = r_addresses;
    routine.pause = this.dis.get_pause();
    routine.indcall = this.dis.get_indcall();
    r_addresses.forEach(function (raddr) {
      addrs_to_see.push(raddr);
    });
  }
  this.resolve_pauseable(raddrs);

  for (var i = 0; i < raddrs.length; i++) {
    var rout = this.routines.get(raddrs[i]);
    rout.code = optimize_code(rout.code);
    var js = convert_routine_to_js(this,
                                   "r$"+rout.addr.toString(16),
                                   rout.locals, rout.code, rout.pauseable, false);
    try {
      var fun = (new Function("e", "return ("+js+");"))(this);
    } catch (x) {
      console.log(js);
      throw x;
    }
    rout.compiled = fun;
    this["r$"+hexWord(rout.addr)] = fun;
  }

  $("#debug_messages").text(this.routines.size + " routines");

  for (var i = this._scheduled_compiles.length-1; i >= 0; i--) {
    var routine = this.routines.get(this._scheduled_compiles[i]);
    if (routine && !routine.temporary) {
      this._scheduled_compiles.splice(i, 1);
    }
  }

  this.schedule_compilation_task();
};
ZMachine.prototype.get_routine = function (raddr) {
  if (this.routines.has(raddr)) {
    return this.routines.get(raddr);
  }
  this._scheduled_compiles.push(raddr);
  this.schedule_compilation_task();
  var numlocals = this.getU8(raddr);
  var code;
  if (raddr === 0) {
    code = ["return", ["lit", 0]];
  } else {
    var blocks = this.dis.trans(raddr+1);
    code = build_code(reloop(blocks, [raddr+1]));
  }
  var rout = new Routine(raddr, numlocals, code);
  this.routines.set(raddr, rout);
  var r_addresses = this.dis.get_new_routines();
  rout.temporary = true; // that is, should be recompiled
  rout.calls = r_addresses;
  rout.pause = this.dis.get_pause();
  rout.indcall = this.dis.get_indcall();
  r_addresses.forEach(function (addr) {
    if (!this.routines.has(addr)) {
      this.make_routine_stub(addr);
    }
  }, this);
  rout.code = optimize_code(rout.code);
  var js = convert_routine_to_js(this,
                                 "r$"+rout.addr.toString(16),
                                 rout.locals, rout.code, true, false);
  try {
    var fun = (new Function("e", "return ("+js+");"))(this);
  } catch (x) {
    console.log(js);
    throw x;
  }
  rout.compiled = fun;
  this["r$"+hexWord(rout.addr)] = fun;
  return rout;
};
ZMachine.prototype.get_cont = function (frame) {
  if (this.conts.has(frame.cont)) {
    return this.conts.get(frame.cont);
  }

  var code = build_code(reloop(this.dis.trans(frame.nextPC()), [frame.nextPC()]));
  this.dis.get_new_routines().forEach(function (raddr) {
    this.get_routine(raddr); // ensure all called routines are loaded
  }, this);

  if (frame.shouldPush()) {
    code = ["block", null,
            [["contstack", frame.nextPC(), null, ["resumeframe"]],
             code]];
  } else if (frame.storeVar() === 0) {
    code = ["block", null,
            [["cont", frame.nextPC(), null, ["resumeframe"]],
             code]];
  } else if (frame.storeVar() < 16) {
    code = ["block", null,
            [["cont", frame.nextPC(), ["local", frame.storeVar()-1], ["resumeframe"]],
             code]];
  } else {
    code = ["block", null,
            [["cont", frame.nextPC(), ["global", frame.storeVar()-16], ["resumeframe"]],
             code]];
  }
  //code = optimize_code(code);

  var js = convert_routine_to_js(this,
                                 "cont$"+frame.nextPC().toString(16)+"_"+(frame.shouldPush()?"stack":frame.storeVar()),
                                 frame.locals.length, code, true, true);

  try {
    var fun = (new Function("e", "return ("+js+");"))(this);
  } catch (x) {
    console.log(js);
    throw x;
  }

  this.conts.set(frame.cont, fun);
//  console.log(pp(code));
  //  console.log(js);
  return fun;
};
ZMachine.prototype.resolve_pauseable = function (addrs) {
  var pauseable_lat = new Set; // contained means pauseable
  var changed;
  var i, j;
  var routines = this.routines;
  function get_pauseable(addr) {
    if (routines.has(addr)
        && !routines.get(addr).temporary
        && routines.get(addr).pauseable !== null) {
      return routines.get(addr).pauseable;
    }
    return pauseable_lat.has(addr);
  }
  function set_pauseable(addr, val) {
    if (!val) return;
    if (!pauseable_lat.has(addr)) {
      changed = true;
      pauseable_lat.add(addr);
    }
  }
  do {
    changed = false;
    for (i = 0; i < addrs.length; i++) {
      var routine = this.routines.get(addrs[i]);
      set_pauseable(routine.addr, routine.pause || routine.indcall);
      for (j = 0; j < routine.calls.length; j++) {
        set_pauseable(routine.addr, get_pauseable(routine.calls[j]));
      }
    }
  } while (changed);

  for (i = 0; i < addrs.length; i++) {
    this.routines.get(addrs[i]).pauseable = get_pauseable(addrs[i]);
  }
};
ZMachine.prototype.save_state = function (type, pause) {
  var dynamicData = this.data.slice(0, this.staticStart);
  this.checkpoints.push({type:type,
                         screen:this.screen.save_state(),
                         dynamic:dynamicData,
                         pause:pause});
};
ZMachine.prototype.restore_state = function (state) {
  this.data.set(state.dynamic, 0);
  this.handle_pause(state.pause, true);
};
// Memory
ZMachine.prototype.getU8 = function (n) {
  return this.data[n];
};
ZMachine.prototype.setU8 = function (n, val) {
  this.data[n] = val;
};
ZMachine.prototype.setU16 = function (n, val) {
  this.dv.setUint16(n, val, false);
//  this.data[n] = val>>8;
//  this.data[n+1] = val;
};
ZMachine.prototype.getU16 = function (n) {
  return this.dv.getUint16(n, false);
  //return (this.data[n]<<8)|this.data[n+1];
};
ZMachine.prototype.getU8Elt = function (arr, n) {
  return this.data[arr + n &0xFFFF];
};
ZMachine.prototype.getU16Elt = function (arr, n) {
  return this.dv.getUint16(arr+2*n &0xFFFF, false);
//  var i = (arr + 2*n)|0;
//  return (this.data[i]<<8)|this.data[i+1];
};
ZMachine.prototype.setU8Elt = function (arr, n, a) {
  this.data[arr + n &0xFFFF] = a;
};
ZMachine.prototype.setU16Elt = function (arr, n, a) {
  this.dv.setUint16(arr+2*n &0xFFFF, a, false);
//  var i = (arr + 2*n)|0;
//  this.data[i] = a >> 8;
//  this.data[i+1] = a;
};
ZMachine.prototype.getGlobal = function (n) {
  return this.getU16Elt(this.globalBase, n);
};
ZMachine.prototype.setGlobal = function (n, v) {
  this.setU16Elt(this.globalBase, n, v);
};
ZMachine.prototype.hasExtension = function (word) {
  return this.extension !== 0 && word < this.numExtensions;
};
ZMachine.prototype.getExtension = function (word) {
  return this.getU16Elt(this.extension, word);
};
ZMachine.prototype.setExtension = function (word, val) {
  if (this.hasExtension(word)) {
    this.setU16Elt(this.extension, word, val);
  }
};
ZMachine.prototype.scan_table = function (x, table, len, form) {
  if (arguments.length < 4) {
    form = 0x82;
  }
  var size = form & 0x3F;
  for (var i = 0; i < len; i++) {
    var e;
    var addr = table + size * i;
    if (form & 0x80) {
      e = this.getU16(addr);
    } else {
      e = this.getU8(addr);
    }
    if (e === x) {
      return addr;
    }
  }
  return 0;
};
// Strings
ZMachine.prototype.getZSCII = function (addr, s) {
  /* Gets ZSCII for a string from the game memory */
  return this.toZSCII(this.data, addr, s);
};
ZMachine.prototype.toZSCII = function (bytes, addr, s) {
  var s = s || []; // in ZSCII
  var alpha = 0;
  var abbrev = -1;
  var c2;

  do {
    var c = (bytes[addr]<<8)|bytes[addr+1];
    addr += 2;
    var stop = c & 0x8000;
    for (var i = 0; i < 3; i++) {
      var z = (c >> 10) & 0x1F;
      c <<= 5;
      if (abbrev === -3) {
        c2 = z << 5;
        abbrev = -2;
        continue;
      } else if (abbrev === -2) {
        s.push(c2 | z);
        abbrev = -1;
      } else if (abbrev >= 0) {
        this.toZSCII(bytes, 2*this.getU16(this.getU16(0x18) + 2*(32*abbrev+z)), s);
        abbrev = -1;
      } else if (0 === z) {
        s.push(32); // space
      } else if (z <= 3) {
        abbrev = z - 1;
      } else if (z <= 5) {
        alpha = (z - 3);
        continue;
      } else if (alpha === 2 && z === 6) {
        abbrev = -3;
        continue;
      } else {
        s.push(this.alphabets[26*alpha+(z-6)]);
      }
      alpha = 0;
    }
  } while (!stop);
  return s;  
};
ZMachine.prototype.fromZSCII = function (padding, chars) {
  var out = [];
  var resolution = 3; // 9 characters
  for (var i = 0; out.length < resolution * 3 && i < chars.length; i++) {
    var c = chars[i];
    var set, ind;
    find_char: {
      for (set = 0; set < 3; set++) {
        for (ind = 0; ind < 26; ind++) {
          if (c === this.alphabets[26*set+ind]) {
            break find_char;
          }
        }
      }
      // just ZSCII
      out.push(5, 6, c >> 5, c & 0x1f);
      continue;
    }
    if (set != 0) {
      out.push(3 + set);
    }
    out.push(ind + 6);
  }
  while (out.length < resolution * 3) {
    out.push(padding);
  }
  var buffer = new ArrayBuffer(2*resolution);
  var encoded = new Uint8Array(buffer);
  for (i = 0; i < resolution; i++) {
    var word = ((out[3*i+0]<<10)
                |(out[3*i+1]<<5)
                |(out[3*i+2]));
    encoded[2*i] = word >> 8;
    encoded[2*i+1] = word;
  }
  encoded[2*resolution - 2] |= 0x80;
  return encoded;
};
ZMachine.prototype.unicodeFromZSCII = function (zscii) {
  var str = [];
  for (var i = 0; i < zscii.length; i++) {
    var c = zscii[i];
    if (32 <= c && c <= 126) {
      str.push(String.fromCharCode(c));
    } else if (155 <= c && c <= 251) {
      if (c - 155 < this.unicode.length) {
        str.push(String.fromCodePoint(this.unicode[c-155]));
      }
    } else {
      switch (c) {
      case ZMachine.Z_NULL:
        break;
      case ZMachine.Z_TAB:
        str.push('\t');
        break;
      case ZMachine.Z_NEWLINE:
        str.push('\n');
        break;
      case ZMachine.Z_SENTENCE_SPACE:
        str.push('\u2003'); // em space
        break;
      default:
        break;
      }
    }
  }
  return str.join('');
};
ZMachine.prototype.unicodeToZSCII = function (str) {
  var zscii = [], idx;
  for (var i = 0; i < str.length; i++) {
    var c = str.codePointAt(i);
    if (32 <= c && c <= 126) {
      zscii.push(c);
    } else if (c === '\t') {
      zscii.push(ZMachine.Z_TAB);
    } else if (c === '\n' || c === '\r') {
      zscii.push(ZMachine.Z_NEWLINE);
    } else if ((idx = this.unicode.indexOf(c)) !== -1) {
      zscii.push(155 + idx);
    }
  }
  return zscii;
};
// Parsing
ZMachine.prototype.lex = function (textaddr, parseaddr) {
  var len = this.getU8(textaddr+1);
  var maxparse = this.getU8(parseaddr);

  var i;

  var seps = [];
  var numseps = this.getU8(this.dict);
  for (i = 0; i < numseps; i++) {
    seps[i] = this.getU8(this.dict + 1 + i);
  }

  var entry_length = this.getU8(this.dict + 1 + numseps);
  var num_entries = this.getU16(this.dict + 1 + numseps + 1);
  var dict_start = this.dict + 1 + numseps + 3;

  function encodedToInt(encoded) {
    return ((((encoded[0] << 8)
              |encoded[1]) * 4 * (1<<30))
            +(encoded[2] << 24)
            +(encoded[3] << 16)
            +(encoded[4] << 8)
            +encoded[5]);
  }

  var self = this;
  function find_word(wordnum, chars) {
    var word = encodedToInt(self.fromZSCII(0x5, chars));
    var lo = 0;
    var hi = num_entries-1;
    while (lo <= hi) {
      var mid = lo + ((hi - lo) >> 1);
      var entry = dict_start + entry_length * mid;
      var entryWord =
            (self.dv.getUint16(entry, false) * 4 * (1<<30))
            + self.dv.getUint32(entry + 2, false);
      if (word === entryWord) {
        return entry;
      } else if (word < entryWord) {
        hi = mid - 1;
      } else if (word > entryWord) {
        lo = mid + 1;
      }
    }
    if (wordnum === 1 && chars.length === 1 && chars[0] === 'x'.charCodeAt(0)) {
      // Zork I doesn't supply this synonym.
      return find_word(-1, self.unicodeToZSCII("examine"));
    }
    return 0;
  }
  function record(parseidx, word, length, offset) {
    var p = parseaddr + 2 + 4*parseidx;
    self.setU16(p, word);
    self.setU8(p+2, length);
    self.setU8(p+3, offset);
  }

  var word = [];
  var parseidx = 0;
  for (i = 0; i < len && parseidx < maxparse; i++) {
    var c = this.getU8(textaddr + 2 + i);
    var sepidx = seps.indexOf(c);
    if (c === 32 && word.length === 0) {
      continue;
    } else if (c !== 32 && sepidx === -1) {
      word.push(c);
    } else if (word.length > 0) {
      record(parseidx++, find_word(i, word), word.length, i+2-word.length);
      word.length = 0;
      i--;
    } else { // then separator
      record(parseidx++, find_word(i, [c]), 1, i+2);
    }
  }
  if (parseidx < maxparse && word.length > 0) {
    record(parseidx++, find_word(i, word), word.length, i+2-word.length);
  }
  this.setU8(parseaddr+1, parseidx);
};
// Objects
ZMachine.prototype.obj_entry = function (obj) {
  return this.objTable + (2*63-14)+14*obj; // obj starts at 1
};
ZMachine.prototype.test_attr = function (obj, attr) {
  var objEntry = this.obj_entry(obj);
  var flagByte = this.getU8(objEntry + (attr >> 3));
  if (0 != (flagByte & (0x80 >> (attr & 0x7)))) {
    return true;
  } else {
    return false;
  }
};
ZMachine.prototype.set_attr = function (obj, attr) {
  var objEntry = this.obj_entry(obj);
  var bytenum = objEntry + (attr >> 3);
  var flagByte = this.getU8(bytenum);
  flagByte |= (0x80 >> (attr & 0x7));
  this.setU8(bytenum, flagByte);
};
ZMachine.prototype.clear_attr = function (obj, attr) {
  var objEntry = this.obj_entry(obj);
  var bytenum = objEntry + (attr >> 3);
  var flagByte = this.getU8(bytenum);
  flagByte &= ~(0x80 >> (attr & 0x7));
  this.setU8(bytenum, flagByte);
};
ZMachine.prototype.get_parent = function (obj) {
  return this.getU16(this.obj_entry(obj)+6);
};
ZMachine.prototype.get_sibling = function (obj) {
  return this.getU16(this.obj_entry(obj)+8);
};
ZMachine.prototype.get_child = function (obj) {
  return this.getU16(this.obj_entry(obj)+10);
};
ZMachine.prototype.remove_obj = function (obj) {
  /* detaches object from parent */
  var parent = this.get_parent(obj);
  if (parent === 0)
    return;
  var child = this.get_child(parent);
  if (child === obj) {
    // move siblings of obj to children of parent
    this.setU16(this.obj_entry(parent)+10, this.get_sibling(obj));
  } else {
    var next_child = this.get_sibling(child);
    while (next_child !== obj) {
      child = next_child;
      next_child = this.get_sibling(next_child);
    }
    // move siblings of obj to siblings of left-sibling of obj
    this.setU16(this.obj_entry(child)+8, this.get_sibling(obj));
  }
  // remove parent from obj
  this.setU16(this.obj_entry(obj)+6, 0);
  // remove siblings from obj
  this.setU16(this.obj_entry(obj)+8, 0);
};
ZMachine.prototype.insert_obj = function (obj, dest) {
  this.remove_obj(obj);
  // assign parent to obj
  this.setU16(this.obj_entry(obj)+6, dest);
  // assign siblings to obj
  this.setU16(this.obj_entry(obj)+8, this.get_child(dest));
  // assign child to dest
  this.setU16(this.obj_entry(dest)+10, obj);
};
ZMachine.prototype.child_of = function (obj, par) {
  var child = this.get_child(par);
  while (child !== 0) {
    if (child === obj)
      return true;
    child = this.get_sibling(child);
  }
  return false;
};
ZMachine.prototype.get_prop = function (obj, prop) {
  var props = this.getU16(this.obj_entry(obj) + 12);
  var nameLength = this.getU8(props);
  var propStart = props + 1 + 2*nameLength;
  while (true) {
    var desc = this.getU8(propStart++);
    var curProp = desc & 0x3F;
    if (curProp < prop)
      break;
    var size;
    if (desc & 0x80) {
      size = this.getU8(propStart++)&0x3F;
      if (size === 0) {
        size = 64;
      }
    } else if (desc & 0x40) {
      size = 2;
    } else {
      size = 1;
    }

    if (curProp === prop) {
      if (size === 1) {
        return this.getU8(propStart);
      } else {
        return this.getU16(propStart);
      }
    }

    propStart += size;
  }
  return this.getU16(this.objTable + 2*prop - 2);
};
ZMachine.prototype.get_prop_addr = function (obj, prop) {
  var props = this.getU16(this.obj_entry(obj) + 12);
  var nameLength = this.getU8(props);
  var propStart = props + 1 + 2*nameLength;
  while (true) {
    var desc = this.getU8(propStart++);
    var curProp = desc & 0x3F;
    if (curProp < prop)
      break;
    var size;
    if (desc & 0x80) {
      size = this.getU8(propStart++)&0x3F;
      if (size === 0) {
        size = 64;
      }
    } else if (desc & 0x40) {
      size = 2;
    } else {
      size = 1;
    }

    if (curProp === prop) {
      return propStart;
    }

    propStart += size;
  }
  return 0;
};
ZMachine.prototype.get_next_prop = function (obj, prop) {
  if (prop === 0) {
    prop = 0xFFFF; // sentinel to get first
  }
  var props = this.getU16(this.obj_entry(obj) + 12);
  var nameLength = this.getU8(props);
  var propStart = props + 1 + 2*nameLength;
  while (true) {
    var desc = this.getU8(propStart++);
    var curProp = desc & 0x3F;
    if (curProp < prop)
      return curProp;
    var size;
    if (desc & 0x80) {
      size = this.getU8(propStart++)&0x3F;
      if (size === 0) {
        size = 64;
      }
    } else if (desc & 0x40) {
      size = 2;
    } else {
      size = 1;
    }
    propStart += size;
  }
};
ZMachine.prototype.get_prop_length = function (propStart) {
  if (propStart === 0) {
    return 0;
  }
  var b = this.getU8(propStart-1);
  if (b & 0x80) {
    var len = b & 0x3F;
    return len === 0 ? 64 : len;
  } else if (b & 0x40) {
    return 2;
  } else {
    return 1;
  }
};
ZMachine.prototype.put_prop = function (obj, prop, val) {
  var props = this.getU16(this.obj_entry(obj) + 12);
  var nameLength = this.getU8(props);
  var propStart = props + 1 + 2*nameLength;
  while (true) {
    var desc = this.getU8(propStart++);
    var curProp = desc & 0x3F;
    if (curProp < prop)
      break;
    var size;
    if (desc & 0x80) {
      size = this.getU8(propStart++)&0x3F;
      if (size === 0) {
        size = 64;
      }
    } else if (desc & 0x40) {
      size = 2;
    } else {
      size = 1;
    }

    if (curProp === prop) {
      if (size === 1) {
        this.setU8(propStart, val);
      } else {
        this.setU16(propStart, val);
      }
      return;
    }

    propStart += size;
  }
  throw new Error("property does not exist for object");
};
// The screen
ZMachine.prototype.erase_window = function (num) {
  num = num << 16 >> 16;
  if (num === -1) {
    this.screen.init();
  } else if (num === -2) {
    this.screen.eraseAll();
  } else {
    this.screen.erase(num);
  }
};
ZMachine.prototype.split_window = function (lines) {
  this.screen.split_window(lines);
};
ZMachine.prototype.set_window = function (num) {
  this.screen.set_window(num);
};
ZMachine.prototype.set_text_style = function (style) {
  if (style === 0) {
    this.screen.clearStyle();
  } else {
    if (style & 1) {
      this.screen.setReverseVideo();
    }
    if (style & 2) {
      this.screen.setBold();
    }
    if (style & 4) {
      this.screen.setItalic();
    }
    if (style & 8) {
      this.screen.setFixed();
    }
  }
};
ZMachine.prototype.set_cursor = function (line, column) {
  this.screen.setCursor(line, column);
};
ZMachine.prototype.print_char = function (zscii_char) {
  if (this.stream3.length > 0) {
    this.stream3[this.stream3.length - 1][1].push([zscii_char]);
  } else {
    this.screen.print(this.unicodeFromZSCII([zscii_char]));
  }
};
ZMachine.prototype.print = function (addr) {
  this.dis.add_string(addr);
  var z = this.getZSCII(addr);
  if (this.stream3.length > 0) {
    this.stream3[this.stream3.length - 1][1].push(z);
  } else {
    this.screen.print(this.unicodeFromZSCII(z));
  }
};
ZMachine.prototype.print_paddr = function (paddr) {
  this.print(4*paddr);
};
ZMachine.prototype.newline = function () {
  this.print_char(ZMachine.Z_NEWLINE);
};
ZMachine.prototype.print_num = function (num) {
  var snum = num << 16 >> 16;

  if (this.stream3.length > 0) {
    this.stream3[this.stream3.length - 1][1].push(this.unicodeToZSCII(''+snum));
  } else {
    this.screen.print('' + snum);
  }
};
ZMachine.prototype.print_obj = function (obj) {
  var props = this.getU16(this.obj_entry(obj) + 12);
  if (this.getU8(props) !== 0) { // this check prevents "The xc ec
                                 // knwall munz doesn't lead
                                 // downward."
    this.print(props + 1);
  }
};
ZMachine.prototype.aread = function (text, parse, time, routine) {
  //console.log("aread request", text, parse, time, routine);
  var skein = window.skein;
  if (skein && skein.length > 0) {
    var str = skein.shift();
    this.screen.print(str + "\n");
    this.do_aread(text, parse, str);
    return 13;
  }
  throw new PauseException("aread", [text, parse, time|0, routine|0], null);
};
ZMachine.prototype.do_aread = function (text_buffer, parse_buffer, str) {
  var text_buffer_len = this.getU8(text_buffer);
  var zscii = this.unicodeToZSCII(str.toLowerCase());
  for (var i = 0; i < zscii.length && i < text_buffer_len; i++) {
    this.setU8(text_buffer + 2 + i, zscii[i]);
  }
  this.setU8(text_buffer + 1, i);
  if (parse_buffer !== 0) {
    this.lex(text_buffer, parse_buffer);
    //console.log("parse_buffer " + Array.from(this.data.subarray(parse_buffer, parse_buffer + 20)).join(' '));
  }
};
ZMachine.prototype.read_char = function (one, time, routine) {
  if (one !== 1)
    throw new Error("first argument must be 1");
  throw new PauseException("read_char", [time|0, routine|0], null);
};
ZMachine.prototype.output_stream = function (number, table) {
  number = number << 16 >> 16;
  if (number === 3) {
    this.stream3.push([table, []]);
  } else if (number === -3) {
    var entry = this.stream3.pop();
    var len = 0;
    for (var i = 0; i < entry[1].length; i++) {
      var z = entry[1][i];
      for (var j = 0; j < z.length; j++) {
        this.setU8(entry[0] + 2 + len, z[j]);
        len++;
      }
    }
    this.setU16(entry[0], len);
    //console.log("stream3",this.unicodeFromZSCII(this.data.slice(entry[0]+2, entry[0]+2+len)));
  } else {
    console.log("output_stream", number, table);
  }
};
// Saving and undo
ZMachine.prototype.save_undo = function () {
  throw new PauseException("save_undo", [], null);
};
ZMachine.prototype.restore_undo = function () {
  throw new PauseException("restore_undo", [], null);
};
// Miscellaneous
ZMachine.prototype.random = function (range) {
  range = range << 16 >> 16;
  function random32() {
    var top = (Math.random()*(1<<16))|0;
    var bot = (Math.random()*(1<<16))|0;
    return ((top<<16)|bot)>>>0;
  }
  function reseed() {
    return {
      x:random32(),
      y:random32(),
      z:random32(),
      w:random32(),
      v:random32()
    };
  }
  if (range === 0) {
    this._random_state = reseed();
    return 0;
  }
  var st = this._random_state;
  if (!st) {
    st = this._random_state = reseed();
  }
  if (range < 0) {
    st.x = st.y = st.z = st.w = st.v = (range>>>0);
    return 0;
  }

  function xorshift() {
    // https://groups.google.com/forum/#!msg/comp.lang.c/qZFQgKRCQGg/rmPkaRHqxOMJ
    var t=(st.x^(st.x>>>7)); st.x=st.y; st.y=st.z; st.z=st.w; st.w=st.v;
    st.v=((st.v^(st.v<<6))^(t^(t<<13)))>>>0;
    return Math.imul(st.y+st.y+1,st.v)>>>0;
  }
  return 1 + xorshift() % range;
};

// Constants
ZMachine.FLAGS1_COLORS = 1;
ZMachine.FLAGS1_BOLDFACE = 4;
ZMachine.FLAGS1_ITALIC = 8;
ZMachine.FLAGS1_FIXEDSPACE = 16;
ZMachine.FLAGS1_TIMEDINPUT = 128;
ZMachine.FLAGS2_TRANSCRIPTING = 1;
ZMachine.FLAGS2_FIXEDPITCH = 2;
ZMachine.FLAGS2_PICTURES = 8;
ZMachine.FLAGS2_UNDO = 16;
ZMachine.FLAGS2_MOUSE = 32;
ZMachine.FLAGS2_COLORS = 128;
ZMachine.FLAGS2_SOUND = 256;
ZMachine.Z_NULL = 0;
ZMachine.Z_DELETE = 8;
ZMachine.Z_TAB = 9;
ZMachine.Z_SENTENCE_SPACE = 11;
ZMachine.Z_NEWLINE = 13;
ZMachine.Z_ESCAPE = 27;
// 32 through 126 are standard ASCII
ZMachine.Z_CURSOR_UP = 129;
ZMachine.Z_CURSOR_DOWN = 130;
ZMachine.Z_CURSOR_LEFT = 131;
ZMachine.Z_CURSOR_RIGHT = 132;
ZMachine.Z_F1 = 133;
ZMachine.Z_F2 = 134;
ZMachine.Z_F3 = 135;
ZMachine.Z_F4 = 136;
ZMachine.Z_F5 = 137;
ZMachine.Z_F6 = 138;
ZMachine.Z_F7 = 139;
ZMachine.Z_F8 = 140;
ZMachine.Z_F9 = 141;
ZMachine.Z_F10 = 142;
ZMachine.Z_F11 = 143;
ZMachine.Z_F12 = 144;
ZMachine.Z_KEYPAD_0 = 145;
ZMachine.Z_KEYPAD_1 = 146;
ZMachine.Z_KEYPAD_2 = 147;
ZMachine.Z_KEYPAD_3 = 148;
ZMachine.Z_KEYPAD_4 = 149;
ZMachine.Z_KEYPAD_5 = 150;
ZMachine.Z_KEYPAD_6 = 151;
ZMachine.Z_KEYPAD_7 = 152;
ZMachine.Z_KEYPAD_8 = 153;
ZMachine.Z_KEYPAD_9 = 154;
// 155 through 251 are "extra characters"
//ZMachine.Z_MENU_CLICK = 252; // V6
//ZMachine.Z_DOUBLE_CLICK = 253; // V6
ZMachine.Z_SINGLE_CLICK = 254;

function PauseException(action, args, frame) {
  this.action = action;
  this.args = args;
  this.frame = frame;
}
PauseException.prototype.toString = function () { return "PauseException"; };

function CallFrame(numargs, locals, stack, cont, child) {
  this.numargs = numargs;
  this.locals = locals;
  this.stack = stack;
  this.cont = cont;
  this.child = child;
}
CallFrame.prototype.nextPC = function () {
  return (this.cont >> 9)|0;
};
CallFrame.prototype.shouldPush = function () {
  return (this.cont & (1<<8))?true:false;
};
CallFrame.prototype.storeVar = function () {
  return (this.cont & 0xFF);
};
CallFrame.prototype.describe = function () {
  console.log("* Frame *");
  console.log("  numargs " + this.numargs);
  console.log("  locals " + this.locals.join(', '));
  console.log("  stack " + this.stack.join(', '));
  console.log("  nextPC " + hexWord(this.nextPC()));
  if (this.shouldPush()) {
    console.log("  should push result");
  } else if (this.storeVar() === 0) {
    console.log("  should ignore result");
  } else if (this.storeVar() < 16) {
    console.log("  should store to arg_" + (this.storeVar()-1));
  } else {
    console.log("  should store to global " + (this.storeVar()-16));
  }
  if (this.child) {
    this.child.describe();
  }
};

function ZScreen($dest, lines, cols) {
  this.$el = $('<div class="zscreen">').appendTo($dest);
  this.lines = lines; // not used
  this.cols = cols;
  this.curWindow = 0; // 0 is lower, 1 is upper
  this.curForeground = null;
  this.curBackground = null;

  this.$upper = $('<div class="upperWindow">').appendTo(this.$el);
  this.$lower = $('<div class="lowerWindow">').appendTo(this.$el),

  this.upperLines = 0; // for split
  this.upperChars = [];

  this.cursor = {
    line: 1,
    col: 1
  };
  this.readCallback = null;
  this.input_history = [];
  this.$input = $('<input type="text" class="userinput">').appendTo(this.$el);
  this.$input.hide();

  var self = this;
  this.$el.attr("tabindex", "1");
  this.read_char_callback = null;
  this.$el.on("keydown.read_char", function (e) {
    if (self.read_char_callback) {
      e.preventDefault();
      e.stopPropagation();
      var rcc = self.read_char_callback;
      self.read_char_callback = null;
      // TODO translate properly
      if (e.key) {
        rcc(e.key.charCodeAt(0));
      } else {
        rcc(e.keyCode);
      }
    }
  });
  
  this.init();
}
ZScreen.prototype.init = function () {
  this.upperLines = 0;
  this.cursor.line = 1;
  this.cursor.col = 1;
  this.curWindow = 0;
  this.$upper.empty();
  this.$lower.empty();

  this.is_line_start = true;
  this.$curLine = $('<div class="line">').appendTo(this.$lower);

  this.clearStyle();
};
ZScreen.prototype.save_state = function () {
  return {
    input_history: this.input_history.slice()
  };
};
ZScreen.prototype.new_lower_line = function () {
  this.is_line_start = true;
  this.$curLine = $('<div class="line">').appendTo(this.$lower);
};
ZScreen.prototype.eraseAll = function () {
  this.erase(1);
  this.erase(0);
};
ZScreen.prototype.erase = function (num) {
  if (num === 1) {
    this.split_window(this.upperLines);
  } else if (num === 0) {
    this.$lower.empty();
  }
};
ZScreen.prototype.split_window = function (lines) {
  this.upperLines = lines;
  this.$upper.empty();
  for (var i = 0; i < lines * this.cols; i += this.cols) {
    var line = document.createElement("div");
    line.className = "upperLine";
    this.$upper[0].appendChild(line);
    for (var j = 0; j < this.cols; j++) {
      var char = this.upperChars[i+j];
      if (!char) {
        char = document.createElement("div");
        char.className = "upperChar";
        char.appendChild(document.createTextNode('\u00a0')); // nbsp
        this.upperChars[i+j] = char;
      } else {
        char.firstChild.nodeValue = '\u00a0'; // nbsp
        char.className = "upperChar";
        char.style.backgroundColor = this.curBackground;
      }
      line.appendChild(char);
    }
  }
  var upperHeight = this.$upper.innerHeight();
  this.$lower.css("padding-top", upperHeight + 10);
  if (char) {
    this.$lower.width(this.$upper.innerWidth());
  }

};
ZScreen.prototype.set_window = function (num) {
  this.curWindow = num;
  if (this.curWindow === 1) {
    this.cursor.line = 1;
    this.cursor.col = 1;
  }
};
ZScreen.prototype.error = function (str) {
  this.$el.append($('<div class=error>').text(str));
};
ZScreen.prototype.print = function (str) {
  if (this.curWindow === 1) {
    for (var i = 0; i < str.length; i++) {
      var c = str[i];
      if (c === '\n') {
        this.cursor.line++;
        this.cursor.col = 1;
        continue;
      }
      var pos = (this.cursor.line - 1)*this.cols + this.cursor.col - 1;
      var char = this.upperChars[pos];
      if (char) {
        char.firstChild.nodeValue = str[i];

        var cls = "upperChar";
        var fg = this.curForeground;
        var bg = this.curBackground;
        if (this.textReverse) {
          fg = this.curBackground;
          bg = this.curForeground;
        }
        if (this.textItalic) {
          cls += " textItalic";
        }
        if (this.textBold) {
          cls += " textBold";
        }
        char.className = cls;
        char.style.color = fg;
        char.style.backgroundColor = bg;
      }
      this.cursor.col++;
      if (this.cursor.col > this.cols) {
        this.cursor.line++;
        this.cursor.col = 1;
      }
      if (this.cursor.line > this.upperLines) {
        this.cursor.line = this.upperLines;
        this.cursor.col = this.cols;
      }
    }
  } else {
    var lines = str.split("\n");
    for (var i = 0; i < lines.length; i++) {
      var $span = $('<span>');
      var text = [];
      for (var j = 0; j < lines[i].length; j++) {
        if (this.is_line_start && lines[i][j] === ' ') {
          text.push('\u2002'); // en space
        } else {
          this.is_line_start = false;
          text.push(lines[i].slice(j));
          break;
        }
      }
      $span.text(text.join(''));

      var cls = "";
      var fg = this.curForeground;
      var bg = this.curBackground;
      if (this.textReverse) {
        fg = this.curBackground;
        bg = this.curForeground;
      }
      if (this.textFixed) {
        cls += " textFixed";
      }
      if (this.textItalic) {
        cls += " textItalic";
      }
      if (this.textBold) {
        cls += " textBold";
      }
      $span[0].className = cls;
      $span[0].style.color = fg;
      if (bg === '#ffffff') {
        bg = "transparent";
      }
      $span[0].style.backgroundColor = bg;
      
      this.$curLine.append($span);
      if (i + 1 < lines.length) {
        this.new_lower_line();
      }
    }
  }
};
ZScreen.prototype.clearStyle = function () {
  this.textReverse = false;
  this.textBold = false;
  this.textItalic = false;
  this.textFixed = false;
};
ZScreen.prototype.setReverseVideo = function () {
  this.textReverse = true;
};
ZScreen.prototype.setBold = function () {
  this.textBold = true;
};
ZScreen.prototype.setItalic = function () {
  this.textItalic = true;
};
ZScreen.prototype.setFixed = function () {
  this.textFixed = true;
};
ZScreen.prototype.setCursor = function (line, column) {
  this.cursor.line = line;
  this.cursor.col = column;
};
ZScreen.prototype.setForeground = function (rgb15) {
  this.curForeground = rgb15to32(rgb15);
};
ZScreen.prototype.setBackground = function (rgb15) {
  this.curBackground = rgb15to32(rgb15);
};
ZScreen.prototype.read = function (init, callback) {
  this.readCallback = callback;
  this.$curLine.append(this.$input);
  var self = this;
  this.$input.off("keydown.read");
  var index = -1; // -1 means current input (not history)
  var saved = null;
  this.$input.on("keydown.read", function (e) {
    if (e.which === 38) { // up arrow
      e.preventDefault();
      e.stopPropagation();
      if (index === -1) {
        saved = self.$input.val();
        index = self.input_history.length - 1;
      } else if (index > 0) {
        index--;
      }
      self.$input.val(self.input_history[index]);
    } else if (e.which === 40) { // down arrow
      e.preventDefault();
      e.stopPropagation();
      if (index + 1 === self.input_history.length) {
        self.$input.val(saved);
        index = -1;
      } else if (index !== -1) {
        self.$input.val(self.input_history[++index]);
      }
    } else if (e.which === 13) { // enter
      e.preventDefault();
      e.stopPropagation();
      self.input_history.push(self.$input.val());
      self.inputEntered();
    }
  });
  this.$input.val(init);
  this.$input.show();
  var inpWidth = this.$lower.innerWidth() - this.$input.position().left;
  this.$input.width(inpWidth-4);
  this.$input.focus();
};
ZScreen.prototype.read_char = function (callback) {
  this.read_char_callback = callback;
  this.$el.focus();
};
ZScreen.prototype.cancel_read_char = function () {
  this.read_char_callback = null;
};
ZScreen.prototype.inputEntered = function () {
  var text = this.$input.val();
  this.$input.val('').hide();
  this.$curLine.append($('<span>').text(text));
  this.new_lower_line();
  var cb = this.readCallback;
  this.readCallback = null;
  if (cb !== null) {
    cb(text);
  }
};

function rgb15to32(rgb15) {
  var r = (rgb15 >> 10) & 0x1F;
  var g = (rgb15 >> 5) & 0x1F;
  var b = rgb15 & 0x1F;
  var r8 = r * 255 / 0x1F;
  var g8 = g * 255 / 0x1F;
  var b8 = b * 255 / 0x1F;
  return "#"+hexByte(r8)+hexByte(g8)+hexByte(b8);
}

$(function () {

  $('#dump_routines').on("click", function (e) {
    var raddrs = Array.from(zmach.routines.keys());
    raddrs.sort(function (a, b) { return a - b; });
    var out = [];
    raddrs.forEach(function (raddr) {
      out.push(''+zmach.routines.get(raddr).compiled);
    });
    var strings = ["var game_strings = new Map;"];
    var saddrs = Array.from(zmach.dis.string_addrs);
    saddrs.sort(function (a, b) { return a - b; });
    saddrs.forEach(function (saddr) {
      var s = zmach.unicodeFromZSCII(zmach.getZSCII(saddr));
      strings.push("game_strings.set(" + saddr + ", "
                   + JSON.stringify(s)+");");
    });
    out.push(strings.join('\n'));
    var text = out.join('\n\n');
    var blob = new Blob([text], {type:"text/plain;charset=utf-8"});
    var $link = $('<a target="_blank">');
    $link
      .attr("href", URL.createObjectURL(blob))
      .attr("download", "zmach_gen_routines.js");
    $link.appendTo(document.body);
    $link[0].click();
    $link.remove();
  });

  var zmach = new ZMachine(coreData);
  window.zmach = zmach;

  var zscr = new ZScreen($("#mainscreen"), 40, 80);

  zmach.set_screen(zscr);

  zmach.run();

/*  zmach.get_routine(zmach.entry-1);
  var rout_addrs = [];
  zmach.routines.forEach(function (rout) {
    rout_addrs.push(rout.addr);
  });
  rout_addrs.sort(function (x, y) { return x - y; });
  var text = "";
  rout_addrs.forEach(function (addr) {
    var routine = zmach.get_routine(addr);
    text += "*** Routine $" + hexWord(addr) + " (" + routine.locals + " locals) ***\n";
    //text += pp(routine.code);
    text += ''+routine.compiled;
    text += "\n\n";
  });
  $("#output").text(text);*/

});
