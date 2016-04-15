
function remove_breaks(code) {

  return blockify(_remove_breaks(code, [], []));

  function seq(codes, labelstack, ends) {
    var newcode = [];
    for (var i = codes.length-1; i >= 0; i--) {
      newcode = _remove_breaks(codes[i], labelstack, ends).concat(newcode);
      ends = [];
    }
    return newcode;
  }
  function labelget(labelstack, name) {
    for (var i = labelstack.length-1; i >= 0; i--) {
      if (name === null || labelstack[i][0] === name) {
        return i;
      }
    }
    throw new Error;
  }

  function _remove_breaks(code, labelstack, ends) {
    var state, ends2, lab, idx, depth, endidx;
    switch (code[0]) {
    case "block": // blocks must _always_ have a label if there is a break
      labelstack.push([code[1], 0, "block"]);
      var blockcode = seq(code[2], labelstack, ends.concat(["block"]));
      state = labelstack.pop();
      if (state[1]) {
        return [["block", code[1], blockcode]];
      } else {
        return seq(blockcode, labelstack, ends);
      }
    case "switch": // switches may optionally have a label if there is a break
      labelstack.push([code[1], 0, "switch"]);
      ends2 = ends.concat(["switch"]);
      var switchcode = code[3].map(function (entry) {
        return [entry[0], seq(entry[1], labelstack, ends2)];
      });
      state = labelstack.pop();
      return [["switch", state[1] > 1 ? code[1] : null, code[2], switchcode]];
    case "if":
      var ifcode = code.slice(2).map(function (cons) {
        return seq(cons, labelstack, ends);
      });
      return [["if", code[1]].concat(ifcode)];
    case "loop":
      labelstack.push([code[1], 0, "loop"]);
      var loopcode = seq(code[2], labelstack, ends.concat(["loop"]));
      state = labelstack.pop();
      return [["loop", state[1] > 1 ? code[1] : null, loopcode]];
    case "break":
      lab = code[1];
      idx = labelget(labelstack, lab);
      depth = labelstack.length-idx;
      endidx = ends.length-depth;
      if (depth === 1 && endidx >= 0 && (ends[endidx] === "block" || ends[endidx] === "switch")) {
        return [];
      }
      state = labelstack[idx];
      state[1] = Math.max(state[1], depth);
      return [["break", idx + 1 === labelstack.length && state[2] !== "block" ? null : lab]];
    case "continue":
      lab = code[1];
      idx = labelget(labelstack, lab);
      depth = labelstack.length-idx;
      endidx = ends.length-depth;
      if (depth === 1 && endidx >= 0 && ends[endidx] === "loop") {
        return [];
      }
      state = labelstack[idx];
      state[1] = Math.max(state[1], depth);
      return [["continue", idx + 1 === labelstack.length ? null : lab]];
    case "comment":
    case "ignore":
    case "set":
    case "push":
    case "pop":
    case "quit":
    case "restart":
    case "return":
    case "cont":
    case "contstack":
    case "get_var":
      return [code];
    default:
      throw new Error(code[0]);
    }
  }
}

function remove_labelsets(code) {
  // Assumption: code does not use __label__ variable in any other way
  // than with (set (var __label__) ...) or (switch ... (var
  // __label__) ...), and the control flow graph only switches on a
  // label in a single location, as constructed by the relooper.
  
  function child_point(pt, i) {
    return pt + "_" + i;
  }
  var changed;
  function update_labels(pt, res) {
    var vals = point_label_vals(pt);
    res.forEach(function (addr) {
      if (!vals.has(addr)) {
        changed = true;
        vals.add(addr);
      }
    });
    return vals;
  }
  function join(ress) {
    var vals = new Set;
    ress.forEach(function (res) {
      res.forEach(function (addr) { vals.add(addr); });
    });
    return vals;
  }

  var _point_label_vals = new Map; // :: Map(point, vals)
  function point_label_vals(pt) {
    if (!_point_label_vals.has(pt)) {
      _point_label_vals.set(pt, new Set());
    }
    return _point_label_vals.get(pt);
  }

  function compute_seq(point, codes, res) {
    for (var i = codes.length-1; i >= 0; i--) {
      res = compute_points(codes[i], child_point(point, i), res);
    }
    return res;
  }

  function is_var_label(c) {
    return c[0] === "var" && c[1] === "__label__";
  }

  var labelstack = [];
  function labelget(lab) {
    for (var i = labelstack.length-1; i >= 0; i--) {
      if (lab === null || lab === labelstack[i][0]) {
        return labelstack[i][1];
      }
    }
    console.log(lab);
    console.log(labelstack);
    throw new Error;
  }

  function compute_points(code, point, lat) {
    var res;
//    console.log(sexp(code));
    switch(code[0]) {
    case "block":
      labelstack.push([code[1], point]);
      update_labels(point + "_break", lat);
      res = update_labels(point, compute_seq(point, code[2], lat));
      labelstack.pop();
      return res;
    case "switch":
      if (is_var_label(code[2])) {
        labelstack.push([code[1], point]);
        update_labels(point + "_break", lat);
        update_labels(point, lat);
        code[3].forEach(function (entry, j) {
          compute_seq(child_point(point, j), entry[1], lat);
          update_labels(point, entry[0]);
        });
        labelstack.pop();
        return point_label_vals(point);
      } else {
        throw new Error;
      }
    case "if":
      code.slice(2).forEach(function (cons, j) {
        compute_seq(child_point(point, j), cons, lat);
      });
      return new Set;
    case "loop":
      labelstack.push([code[1], point]);
      update_labels(point + "_break", lat);
      update_labels(point + "_continue", point_label_vals(point));
      res = compute_seq(point, code[2], point_label_vals(point));
      labelstack.pop();
      return update_labels(point, res);
    case "set":
      if (is_var_label(code[1])) {
        update_labels(point, lat);
        return new Set;
      } else {
        return lat;
      }
    case "break":
      return point_label_vals(labelget(code[1]) + "_break");
    case "continue":
      return point_label_vals(labelget(code[1]) + "_continue");
    case "comment":
    case "ignore":
    case "push":
    case "pop":
    case "cont":
    case "contstack":
    case "get_var":
      return lat;
    case "quit":
    case "restart":
    case "return":
      return new Set;
    default:
      throw new Error(code[0]);
    }
  }

  function remove_children(codes, point) {
    var c = [];
    for (var i = codes.length-1; i >= 0; i--) {
      c = remove(codes[i], child_point(point, i)).concat(c);
    }
    return c;
  }

  function remove(code, point) {
    switch(code[0]) {
    case "block":
      return [["block", code[1], remove_children(code[2], point)]];
    case "switch":
      if (is_var_label(code[2])) {
        return [["switch", code[1], code[2],
                 code[3].map(function (entry, j) {
                   return [entry[0], remove_children(entry[1], child_point(point, j))];
                 })]];
      } else {
        throw new Error;
      }
    case "if":
      var test = code[1];
      var cons = remove_children(code[2], child_point(point, 0));
      var alt = remove_children(code[3], child_point(point, 1));
      return [["if", test, cons, alt]];
    case "loop":
      return [["loop", code[1], remove_children(code[2], point)]];
    case "set":
      if (is_var_label(code[1])) {
        var vals = point_label_vals(point);
        if (vals.size === 0) { //  !vals.has(code[2][1])) {
          return [];
        } else {
          return [code];
        }
      } else {
        return [code];
      }
    case "break":
    case "continue":
    case "comment":
    case "ignore":
    case "push":
    case "pop":
    case "cont":
    case "contstack":
    case "get_var":
    case "quit":
    case "restart":
    case "return":
      return [code];
    default:
      throw new Error(code[0]);
    }
  }

  do {
    changed = false;
    compute_points(code, "0", new Set);
  } while (changed);

  if (0) {
    var s = "";
    _point_label_vals.forEach((m, k) => {
      s += k + "\n";
      m.forEach(a => { s += "  :" + hexWord(a) + "\n"; });
    });
    console.log(s);
  }
  return blockify(remove(code, "0"));

  //return blockify(_remove_labelsets(code).code);
}

function simplify_ifs(code) {
  function simplify_seq(codes) {
    return codes.map(simplify_ifs);
  }
  switch (code[0]) {
  case "block":
    return ["block", code[1], simplify_seq(code[2])];
  case "switch":
    return ["switch", code[1], code[2],
            code[3].map(function (entry) {
              return [entry[0], simplify_seq(entry[1])];
            })];
  case "if":
    var test = code[1];
    var cons = simplify_seq(code[2]);
    var alt = simplify_seq(code[3]);
    function empty(cons) {
      return cons.length === 0 || cons.length === 1 && cons[0][0] === "comment";
    }
    if (empty(cons) && empty(alt)) {
      return ["ignore", test];
    }
    if (empty(cons)) {
      test = ["not", test];
      cons = alt; alt = [];
    }
    function check_only_if(cons) {
      if (cons.length === 1 && cons[0][0] === "if") return cons[0];
      else if (cons.length === 2 && cons[0][0] === "comment" && cons[1][0] === "if") return cons[1];
      else return null;
    }
    if (empty(alt)) {
      alt = [];
      var subif = check_only_if(cons);
      if (subif !== null && empty(subif[3])) {
        test = ["and", test, subif[1]];
        cons = subif[2];
        // no need to loop since already simplified by recursion
      }
    }
    return ["if", test, cons, alt];
  case "loop":
    return ["loop", code[1], simplify_seq(code[2])];
  case "set":
  case "break":
  case "continue":
  case "comment":
  case "ignore":
  case "push":
  case "pop":
  case "cont":
  case "contstack":
  case "get_var":
  case "quit":
  case "restart":
  case "return":
    return code;
  default:
    throw new Error(code[0]);
  }
}

function eliminate_stack(code) {
  
  // depth is 0,1,..., and -1 for bottom, -2 for unknown

  var changed;

  function child_point(pt, i) {
    return pt + "_" + i;
  }
  var _point_stackdepth = new Map; // :: Map(point, depth)
  function point_stackdepth(pt) {
    if (!_point_stackdepth.has(pt)) {
      return -2;
    }
    return _point_stackdepth.get(pt);
  }
  function update(pt, depth) {
    var odepth = point_stackdepth(pt);
    var jdepth = join([depth, odepth]);
    if (odepth !== jdepth) {
      changed = true;
      _point_stackdepth.set(pt, jdepth);
    }
    return jdepth;
  }
  function join(depths) {
    var jdepth = -2;
    depths.forEach(function (depth) {
      if (jdepth === -2) {
        jdepth = depth;
      } else if (jdepth === -1 || depth === -2) {
        // remains same
      } else if (depth === -1 || jdepth !== depth) {
        jdepth = -1;
      } else {
        // they are equal
      }
    });
    return jdepth;
  }

  var labelstack = [];
  function labelget(lab) {
    for (var i = labelstack.length-1; i >= 0; i--) {
      if (lab === null || lab === labelstack[i][0]) {
        return labelstack[i][1];
      }
    }
    throw new Error;
  }

  function compute_seq(codes, point, depth) {
    for (var i = 0; i < codes.length; i++) {
      depth = compute(codes[i], child_point(point, i), depth);
    }
    return depth;
  }
  function compute(code, point, depth) {
    var depth2;
    switch (code[0]) {
    case "block":
      labelstack.push([code[1], point]);
      depth2 = compute_seq(code[2], point, depth);
      labelstack.pop();
      return update(point + "_break", depth2);
    case "switch":
      depth = update(point + "_break", depth);
      labelstack.push([code[1], point]);
      depth2 = join(code[3].map(function (entry, j) {
        return compute_seq(entry[1], child_point(point, j), depth);
      }));
      labelstack.pop();
      return update(point + "_break", depth2);
    case "if":
      return join(code.slice(2).map(function (cons, j) {
        return compute_seq(cons, child_point(point, j), depth);
      }));
    case "loop":
      depth = update(point + "_continue", depth);
      labelstack.push([code[1], point]);
      depth2 = compute_seq(code[2], point, depth);
      labelstack.pop();
      update(point + "_continue", depth2);
      return update(point + "_break", depth2);
    case "push":
      depth = update(point, depth);
      if (depth === -2 || depth === -1) {
        return depth;
      } else {
        return depth + 1;
      }
    case "pop":
      depth = update(point, depth);
      if (depth === -2 || depth === -1) {
        return depth;
      } else {
        if (depth === 0) throw new Error;
        return depth - 1; // 0 becomes bottom
      }
    case "break":
      update(labelget(code[1]) + "_break", depth);
      return -2;
    case "continue":
      update(labelget(code[1]) + "_continue", depth);
      return -2;
    case "quit":
    case "return":
      return -2;
    case "set":
    case "comment":
    case "ignore":
      return depth;
    default:
      throw new Error(code[0]);
    }
  }

  function replace_seq(codes, point) {
    return codes.map(function (code, i) {
      return replace_push(code, child_point(point, i));
    });
  }

  function replace_push(code, point) {
    var depth;
    switch (code[0]) {
    case "block":
      return ["block", code[1], replace_seq(code[2], point)];
    case "switch":
      return ["switch", code[1], code[2],
              code[3].map(function (entry, j) {
                return [entry[0], replace_seq(entry[1], child_point(point, j))];
              })];
    case "if":
      return ["if", code[1],
              replace_seq(code[2], child_point(point, 0)),
              replace_seq(code[3], child_point(point, 1))];
    case "loop":
      return ["loop", code[1],
              replace_seq(code[2], point)];
    case "push":
      depth = point_stackdepth(point);
      if (depth >= 0) {
        return ["set", ["var", "s_" + depth], code[1]];
      } else {
        return code;
      }
    case "pop":
      depth = point_stackdepth(point);
      if (depth >= 0) {
        return ["set", code[1], ["var", "s_" + (depth-1)]];
      } else {
        return code;
      }
    case "break":
    case "continue":
    case "quit":
    case "return":
    case "set":
    case "comment":
    case "ignore":
      return code;
    default:
      throw new Error(code[0]);
    }
  }

  do {
    changed = false;
    compute(code, "0", 0);
  } while (changed);

  // can't really do anything if bottom appears
  var quit = false;
  _point_stackdepth.forEach((m, k) => {
    if (m === -1) quit = true;
  });
  if (quit) return code;

  return replace_push(code, "0", 0);
}
