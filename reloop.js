
function Simple(label, block, next) {
  this.label = label;
  this.block = block;
  this.next = next;
}
Simple.prototype.entries = function () {
  return [this.label];
};
function Loop(name, inner, next) {
  this.name = name; // for continue/break
  this.inner = inner;
  this.next = next;
}
Loop.prototype.entries = function () {
  return this.inner.entries();
};
function Multiple(name, handled, next) {
  this.name = name; // for break
  this.handled = handled;
  this.next = next;
}
Multiple.prototype.entries = function () {
  var entries = [];
  this.handled.forEach(function (h) {
    h.entries().forEach(function (e) { entries.push(e); });
  });
  if (this.next) {
    this.next.entries().forEach(function (e) { entries.push(e); });
  }
  return entries;
};

function correct_block(block, exitlabel, entries, inner) {
  var last = block[block.length-1];
  var newlast = last;
  if (last[0] === "branch") {
    newlast = last.slice(0, 2).concat(last.slice(2).map(function (br) {
      if (!(br instanceof Array)) {
        if (!inner.has(br)) {
          return ["break", exitlabel, br];
        } else if (-1 !== entries.indexOf(br)) {
          return ["continue", exitlabel, br];
        }
      }
      return br;
    }));
  }
  return block.slice(0,-1).concat([newlast]);
}

function reloop(blocks, entries) {
  if (entries.length === 0) {
    return null;
  }
  for (var i = 0; i < entries.length; i++) {
    var idx = entries.lastIndexOf(entries[i]);
    if (idx > i) {
      entries.splice(idx, 1);
    }
  }
  var to_visit = entries.map(function (ent) { return [ent, ent];});
  var enteredby = new Map();
  while (to_visit.length > 0) {
    var label_by = to_visit.pop();
    block_branches(blocks.get(label_by[0])).forEach(function (br) {
      if (!enteredby.has(br)) {
        enteredby.set(br, new Set());
      }
      if (!enteredby.get(br).has(label_by[1])) {
        enteredby.get(br).add(label_by[1]);
        to_visit.push([br, label_by[1]]);
      }
    });
  }
  if (entries.length === 1 && !enteredby.has(entries[0])) {
    var block = blocks.get(entries[0]);
    return new Simple(entries[0], block,
                      reloop(blocks, block_branches(block)));
  }

  // check if can create Multiple

  var multentries = [];
  var multiple = [];
  var selfloops = 0;
  var multlabels = new Set();
  var notmultentries = [];
  entries.forEach(function (entry) {
    var selfloop;
    if (!enteredby.has(entry) || (selfloop = (enteredby.get(entry).size === 1
                                              && enteredby.get(entry).has(entry)))) {
      if (selfloop) selfloops++;
      multentries.push(entry);
    } else {
      notmultentries.push(entry);
    }
  });
  multentries.forEach(function (entry) {
    var mlabels = new Set([entry]);
    multlabels.add(entry);
    enteredby.forEach(function (by, label) {
      if (-1 === entries.indexOf(label) && by.size === 1 && by.has(entry)) {
        mlabels.add(label);
        multlabels.add(label);
      }
    });
    multiple.push([entry, mlabels]);
  });
  if (multiple.length > 0 && (multiple.length !== selfloops || selfloops > 1)) {
    // allow multiple.length === selfloops so that we get
    // multiple(loop) rather than loop(multiple).
    var multname = gensym();
    var nextlabels = new Set(notmultentries);
    var multblocks = multiple.map(function (entry_mlabels) {
      var entry = entry_mlabels[0],
          mlabels = entry_mlabels[1];
      var mblocks = new Map();
      mlabels.forEach(function (multlab) {
        var block = blocks.get(multlab);
        block_branches(block).forEach(function (br) {
          if (!mlabels.has(br)) {
            nextlabels.add(br);
          }
        });
        mblocks.set(multlab, correct_block(block, multname, [], mlabels));
      });
      return reloop(mblocks, [entry]);
    });
    return new Multiple(multname, multblocks,
                        reloop(blocks, Array.from(nextlabels)));
  }

  // It must be a loop

  var looplabel = gensym();
  var pre = new Set(entries); // labels which can reach entries ('pre'-entries)

  var numnodes = enteredby.size;
  var changed;
  do {
    changed = false;
    enteredby.forEach(function (_, label) {
      if (pre.has(label))
        return;
      block_branches(blocks.get(label)).forEach(function (br) {
        if (pre.has(br) && !pre.has(label)) {
          changed = true;
          pre.add(label);
        }
      });
    });
  } while (changed);

  var nextlabels = new Set();
  var innerblocks = new Map();
  pre.forEach(function (innerlab) {
    var block = blocks.get(innerlab);
    block_branches(block).forEach(function (br) {
      if (!pre.has(br)) {
        nextlabels.add(br);
      }
    });
    innerblocks.set(innerlab, correct_block(block, looplabel, entries, pre));
  });
  return new Loop(looplabel,
                  reloop(innerblocks, entries),
                  reloop(blocks, Array.from(nextlabels)));
}


Simple.prototype.show = function (builder) {
  builder.indent("block $" + hexWord(this.label) + " {");
  this.block.forEach(function (entry) {
    if (entry[0] === "branch") {
      if (entry[1] === null) {
        builder.add("__label__ = " + sexp(entry[2]));
      } else {
        builder.indent("if (" + sexp(entry[1]) + ") {");
        builder.add("__label__ = " + sexp(entry[2]));
        builder.dedent("} else {"); builder.indent();
        builder.add("__label__ = " + sexp(entry[3]));
        builder.dedent("}");
      }
    } else {
      builder.add(sexp(entry));
    }
  });
  builder.dedent("}");
  if (this.next) {
    this.next.show(builder);
  }
};
Loop.prototype.show = function (builder) {
  builder.indent("loop " + this.name + " {");
  builder.add("entries " + this.entries().map(hexWord));
  this.inner.show(builder);
  builder.dedent("}");
  if (this.next) {
    this.next.show(builder);
  }
};
Multiple.prototype.show = function (builder) {
  builder.indent("multiple " + this.name + " {");
  builder.add("entries " + this.entries().map(hexWord));
  this.handled.forEach(function (h) {
    builder.indent("case {");
    h.show(builder);
    builder.dedent("}");
  });
  builder.dedent("}");
  if (this.next) {
    this.next.show(builder);
  }
};
