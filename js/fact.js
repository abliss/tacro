(function(module) {
    // A Fact is an "interlingua" object representing a stmt, thm, or
    // defthm. This is designed for easy conversion to/from JSON.  For
    // consistency, you must almways name things in the same order.  Once the
    // hyps and stmt have been set, further calls to nameKind and nameTerm will
    // not affect the result of getKey().
    function Fact(obj) {

        // This is the Fact schema. Only these fields are allowed. Anything
        // undefined may only be set to a string or, in the case of
        // Tree.Definiendum, an int.
        var schema = {
            Core: [
                [], // Hyps
                [], // Stmt
                [], // Free
            ],
            Skin: {
                Name: undefined,
                License: undefined,
                HypNames:[],
                DepNames: [],
                VarNames: [],
                TermNames: [],
                Delimiters: [],
            },
            Tree: {
                Cmd: undefined,
                Definiendum: undefined,  // Defthms: which term is defined?
                Deps: [],
                Proof: [],
            },
        };
        function copyFromSchema(schemaObj, inputObj, outputObj) {
            for (var k in schemaObj) {
                if (inputObj && inputObj.hasOwnProperty(k)) {
                    var s = schemaObj[k];
                    if ((Array.isArray(s) && (s.length > 0)) ||
                        (!Array.isArray(s) && s)) {
                        outputObj[k] = schemaObj[k];
                        copyFromSchema(schemaObj[k], inputObj[k], outputObj[k]);
                    } else {
                        outputObj[k] = inputObj[k];
                    }
                } else {
                    outputObj[k] = schemaObj[k]
                }
            }
        }
        copyFromSchema(schema, obj, this);
    }

    Fact.CORE_HYPS = 0;
    Fact.CORE_STMT = 1;
    Fact.CORE_FREE = 2;

    // returns the index of s in the array. If necessary, pushes it on the end
    // and calls onAdd(n).
    function indexOf(arr, s, onAdd) {
        for (var i = 0; i < arr.length; i++) {
            if (arr[i] == s) return i;
        }
        var n = arr.push(s) - 1;
        if (onAdd) {
            onAdd(n);
        }
        return n;
    }

    // set up methods on the obj
    Fact.prototype.nameTerm = function(s) {
        return indexOf(this.Skin.TermNames, s);
    };
    Fact.prototype.nameHyp = function(s) {
        return 'Hyps.' + indexOf(this.Skin.HypNames, s);
    };
    Fact.prototype.nameDep = function(s, fact) {
        var that = this;
        return 'Deps.' + indexOf(this.Skin.DepNames, s, function(n) {
            var termMap = fact.getCoreTermNames().map(function(term) {
                return that.nameTerm(term);
            });
            that.Tree.Deps[n] = [fact.Core, termMap]; //TODO: should copy Core
        });
    };
    Fact.prototype.nameVar = function(s) {
        return indexOf(this.Skin.VarNames, s);
    };
    Fact.prototype.setName = function(s) {
        this.Skin.Name = s;
        return this;
    };
    Fact.prototype.setCmd = function(s) {
        this.Tree.Cmd = s;
        return this;
    };
    Fact.prototype.setHyps = function(arr) {
        this.Core[Fact.CORE_HYPS] = arr;
        return this;
    };
    Fact.prototype.setFree = function(arr) {
        this.Core[Fact.CORE_FREE] = arr;
        return this;
    };
    Fact.prototype.setDefiniendum = function(term) {
        this.Tree.Definiendum = this.nameTerm(term);
        return this;
    };
    Fact.prototype.setProof = function(arr) {
        this.Tree.Proof = arr;
    };
    Fact.prototype.setStmt = function(sexp) {
        this.Core[Fact.CORE_STMT] = sexp;
    };
    // Returns a subexpression whose first element is the given term.
    function findSubExpWithTerm(sexp, term) {
        // TODO: unexceptional exception
        function recurse(subexp) {
            if (Array.isArray(subexp)) {
                if (subexp[0] == term) throw(subexp);
                subexp.slice(1).map(recurse);
            }
        }
        try { recurse(sexp); }
        catch (e) { return e; }
        throw new Error("Term not found! " + term + " in " +
                        JSON.stringify(sexp));
    };
    Fact.prototype.toGhilbert = function(context, toGhilbertCb) {
        //console.log("# XXXX toGhilbert: " + this.Skin.Name);
        var that = this;
        var out = "";
        function getVar(s) {
            // TODO: insert var/tvar cmds
            return that.Skin.VarNames[s];
        }
        function stringify(sexp) {
            if (sexp.slice) {
                var args = sexp.slice(1).map(stringify);
                args.unshift(that.Skin.TermNames[sexp[0]]);
                return "(" + args.join(" ") + ")";
            } else {
                return getVar(sexp);
            }
        }

        out += this.Tree.Cmd
        out += " ";
        out += "(" + this.Skin.Name;
        out += "\n  ";

        if (this.Tree.Cmd == 'defthm') {
            out += " k " + "\n"; // TODO: kinds
            // infer the dsig by grabbing a subexp with the required term
            var dsig = findSubExpWithTerm(this.Core[Fact.CORE_STMT],
                                          this.Tree.Definiendum);
            out += stringify(dsig) + "\n  ";
        }

        out += '(' + this.Core[Fact.CORE_FREE].map(function(fv) {
            return '(' + fv.map(getVar).join(' ') + ')';
        }).join(' ') + ')';
        out += "\n  ";
        out += "(";

        for (var i = 0; i < this.Core[Fact.CORE_HYPS].length; i++) {
            if (this.Tree.Cmd != 'stmt') {
                out += this.Skin.HypNames[i];
                out += " ";
            }
            out += stringify(this.Core[Fact.CORE_HYPS][i]);
            if (i + 1 < this.Core[Fact.CORE_HYPS].length) {
                out += "\n   ";
            }
        }
        out += ")";
        out += "\n  ";

        out += stringify(this.Core[Fact.CORE_STMT]);
        out += "\n  ";

        if (this.Tree.Proof) {
            var outstandingQueries = 0;
            var finishedQuerying = false;
            var depNames = [];
            var mapped = [];
            function finish() {
                out += mapped.join(' ') + "\n)\n";
                toGhilbertCb(null, out);
            }
            function step(s) {
                if (!s.match) {
                    return stringify(s);
                } else if (s.match(/^Hyps/)) {
                    return that.Skin.HypNames[s.substring(5)];
                } else if (s.match(/^Deps/)) {
                    var depNum = s.substring(5);
                    var depCore = that.Tree.Deps[depNum][0];
                    var depMap = that.Tree.Deps[depNum][1]; //XXX
                    var origDep = that.Skin.DepNames[depNum];
                    if (!depNames[depNum]) {
                        depNames[depNum] = {toString: function() {
                            return this.name || "WTF";
                        }}
                        outstandingQueries++;
                        var hint = {name:origDep};
                        hint.terms = depMap.map(function(n) {
                            return that.Skin.TermNames[n];});
                        /*
                        console.log("# XXXX Gh " +
                                    that.Skin.Name + " wants " +
                                    hint.name);
*/
                        context.requestFact(
                            depCore, hint,
                            function(err, fact) {
                                if (err) {
                                    toGhilbertCb(err, null);
                                } else {
                                    depNames[depNum].name = fact.Skin.Name;
                                    outstandingQueries--;
/*
                                    console.log("# XXXX Gh " +
                                                that.Skin.Name +
                                                " got " + fact.Skin.Name +
                                                " wants " + outstandingQueries);
*/
                                    if (finishedQuerying &&
                                        (outstandingQueries == 0)) {
                                        finish();
                                    }
                                }
                            });
                    }
                    return depNames[depNum];
                }
            }
            mapped = that.Tree.Proof.map(step);
            finishedQuerying = true;
            if (outstandingQueries == 0) {
                finish();
            }
        }
    };
    Fact.prototype.getNewTerm = function() {
        if (this.Tree.Cmd != 'defthm') {
            return null;
        }
        return this.Skin.TermNames[this.Tree.Definiendum];
    };
    // Returns an appropriate database key, specific to the core
    Fact.prototype.getKey = function() {
        var key = this.getMark();
        if (Math.random() < 0.01) {
            console.log("XXXX Key: " + key)
        }
        return key;
    };
    // Returns the prefix of this.Skin.TermNames which is used in the Core.
    Fact.prototype.getCoreTermNames = function() {
        // TODO: this is a little hacky...
        var maxOp = -1;
        function scan(exp) {
            if (exp.slice) {
                if (exp[0] > maxOp) {
                    maxOp = exp[0];
                }
                exp.slice(1).map(scan);
            }
        }
        this.Core[Fact.CORE_HYPS].forEach(scan);
        scan(this.Core[Fact.CORE_STMT]);
        return this.Skin.TermNames.slice(0, maxOp + 1);
    };
    Fact.prototype.getMark = function() {
        return JSON.stringify(this.Core) + ";" +
            JSON.stringify(this.getCoreTermNames());
    };
    Fact.prototype.ensureFree = function(termVar, bindingVar) {
        if (Array.isArray(termVar) || Array.isArray(bindingVar)) {
            throw new Error("Expected vars: " + JSON.stringify(termVar) +
                            " " + JSON.stringify(bindingVar));
        }
        var myFree = this.Core[Fact.CORE_FREE];
        var freeList;
        var firstIndexBigger = myFree.length;
        // Keeps the list sorted if it already was.
        for (var i = 0; i < myFree.length; i++) {
            if (myFree[i][0] == termVar) {
                freeList = myFree[i];
                break;
            } else if (myFree[i][0] > termVar) {
                firstIndexBigger = i;
            }
        }
        if (!freeList) {
            freeList = [termVar];
            myFree.splice(firstIndexBigger, 0, freeList);
        }
        firstIndexBigger = freeList.length;
        for (var i = 1; i < freeList.length; i++) {
            if (freeList[i] == bindingVar) {
                // Already there. Nothing to do.
                return;
            } else if (freeList[i] > bindingVar) {
                firstIndexBigger = i;
            }
        }
        freeList.splice(firstIndexBigger, 0, bindingVar);
    };
    module.exports = Fact;
})(module);