// This is designed to test a log of facts from a playthrough of the game, as
// generated from stairs.js:exportFacts

var Fs = require('fs');
var Fact = require('../../caghni/js/fact.js'); //XXX
var Async = require('async');
var Engine = require('./engine.js');

var lands = [];
var state = {};

var DEBUG = false;

state.factsByMark = {};
state.requestFact = function(core, hint, cb) {
    var mark = JSON.stringify(core) + ";" + JSON.stringify(hint.terms);
    var fact = state.factsByMark[mark];
    if (!fact) {
        cb(new Error("No fact for mark " + JSON.stringify(mark)) +
           "\n facts: " + JSON.stringify(state.factsByMark));
    } else {
        cb(null, fact);
    }
}

// A container to queue and collect async serializations
function Context() {
    var facts = [];
    var txt = "";
    var that = this;
    var isIface = null;
    // 0 .. highest var number seen
    var maxVar = [];
    // terms seen in this context
    var myTerms = {};

    var queue = Async.queue(function(task, cb) {
        task.toGhilbert(state, function(err, ghTxt) {
            if (err) {
                console.log(err);
                cb(err);
            } else if (ghTxt == null) {
                cb("Null ghtext!");
            } else {
                txt += ghTxt;
                cb(null);
            }
        });
    },1);
    this.length = function() {
        return facts.length;
    }
    this.append = function(x) {
        if (!x || !x.Core) {
            throw new Error("Bad fact: " + JSON.stringify(x));
        }
        facts.push(x);
        return this;
    }


    function checkFact(fact, ignored, ignored, termsAreDone) {
        var factVarIsBinding = [];
        factVarIsBinding.sourceFact = fact;

        // A context must have only stmts or only thms/defthms. This sets
        // isIface to true or false (assuming facts is nonempty), and throws
        // up if they are mixed.
        if (fact.Tree.Cmd == 'stmt') {
            if (isIface == null) {
                isIface = true;
            } else if (!isIface) {
                throw new Error("Stmt encountered:" + JSON.stringify(fact));
            }
        } else {
            if (isIface == null) {
                isIface = false;
            } else if (isIface) {
                throw new Error("Thm encountered:" + JSON.stringify(fact));
            }
        }
        // Check the terms and vars of this fact, populating terms/ maxVar.
        // Returns true if exp was an binding var, false if array or Tvar,
        // otherwise null.
        function checkExp(exp) {
            if (Array.isArray(exp) && (exp.length > 0)) {
                var tn = fact.Skin.TermNames[exp[0]];
                if (!that.terms.hasOwnProperty(tn)) that.terms[tn] = [];
                myTerms[tn] = true;
                var termArgIsTerm = that.terms[tn];
                for (var i = 0; i < exp.length - 1; i++) {
                    var arg = exp[i+1];
                    if (termArgIsTerm.length <= i) {
                        termArgIsTerm[i] = null;
                    }
                    // Positive termness in an arg constrains the term.
                    if (checkExp(arg) == false) {
                        if (termArgIsTerm[i] == false) {
                            throw new Error("term arg mismatch");
                        } else {
                            if (((tn == "&forall;") || (tn == "&exist;")) &&
                                (i == 0)) {
                                // TODO: XXX HACK
                                throw new Error("WRONG!\n" +
                                                JSON.stringify(fact) + "\nin:"+
                                                JSON.stringify(exp) + "\nfvib"+
                                                JSON.stringify(factVarIsBinding));
                            }
                            termArgIsTerm[i] = true;
                        }
                    }
                    // Positive (or presumptive) bindingness from the term
                    // constrains var arg. TODO:??
                    if ((termArgIsTerm[i] == false)
                       || (termsAreDone && (termArgIsTerm[i] == null))
                       ) {
                        if (typeof arg == 'number') {
                            if (factVarIsBinding[arg] == false) {
                                throw new Error("Var bind mismatch");
                            } else {
                                factVarIsBinding[arg] = true;
                            }
                        } else {
                            throw new Error("Term found, mismatch");
                        }
                    }
                }
                return false;
            } else if (typeof exp == 'number') {
                if (exp >= maxVar.length) {
                    maxVar[exp] = exp;
                }
                if (exp >= factVarIsBinding.length) {
                    factVarIsBinding[exp] = null;
                }
                return factVarIsBinding[exp];
            } else {
                // Strings of proof handled below
                return null;
            }
        }
        function checkFreemap(fm) {
            // We allow term vars at the front of freelists, even though
            // ghilbert doesn't.
            //factVarIsBinding[fm[0]] = false;
            fm.slice(1).forEach(function(v) {
                factVarIsBinding[v] = true;
            });
        }
        fact.Core[Fact.CORE_FREE].forEach(checkFreemap);
        fact.Core[Fact.CORE_HYPS].forEach(checkExp);
        checkExp(fact.Core[Fact.CORE_STMT]);
        if (fact.Tree.Proof) {
            var mandHyps = [];
            fact.Tree.Proof.forEach(function(step) {
                checkExp(step);
                // Now we need to propagate binding results through mandhyps,
                // for the 'eqid' case.
                if (!termsAreDone) {
                    return;
                }
                if (!step.substr) {
                    mandHyps.push(step);
                } else if (step.substr(0,5) == 'Deps.') {
                    var dep = fact.Tree.Deps[step.substr(5)];
                    // TODO: this is sloppy
                    var depMark = JSON.stringify(dep[0]) + ";" + JSON.stringify(
                        dep[1].map(function(n){return fact.Skin.TermNames[n]}));
                    var depFvib = that.markToFvib[depMark];
                    if (depFvib == undefined) {
                        throw new Error("no fvib for " + depMark);
                    }
                    mandHyps.forEach(function(mandHyp, j) {
                        if (depFvib[j]) {
                            if (typeof mandHyp != 'number') {
                                // TODO:  should actually backpropagate this!
                                throw new Error(
                                    "Bad mandHyp " + mandHyp + " at " +
                                        j + " in " +
                                        JSON.stringify(fact) + " to " +
                                        depMark + " of " +
                                        JSON.stringify(depFvib) + " dep " +
                                        JSON.stringify(depFvib.sourceFact)
                                );
                            }
                            factVarIsBinding[mandHyp] = true;
                        }
                    });
                    mandHyps = [];
                    }
            });
        }
        // TODO: we might need to propagate these changes by running through
        // again. E.g. suppose var 0 is only passed to a new term in the
        // stmt; but in the proof it is passed to a term known to be binding
        // on that arg. Then the var doesn't get marked binding until the
        // proof check, but this should be propagated up to the new term.
        // This might cascade...
        that.markToFvib[fact.getMark()] = factVarIsBinding;

        return factVarIsBinding;
    }
    this.inferTerms = function() {
        facts.forEach(checkFact);
    }
    this.toString = function(cb) {
        txt += isIface ? "kind (k)\n" : 'import (TMP tmp2.ghi () "")\n';

        txt += "tvar (k " + maxVar.map(function(v) { return "V"+v;}).join(" ");
        txt += ")\n";
        txt += " var (k " + maxVar.map(function(v) { return "v"+v;}).join(" ");
        txt += ")\n";

        if (isIface) {
            for (var t in myTerms) if (myTerms.hasOwnProperty(t)) {
                var termArgIsTerm = that.terms[t];
                txt += "term (k (" + t;
                for (var i = 0; i < termArgIsTerm.length; i++) {
                    // TODO: presumptive binding...???
                    txt += " " + ((termArgIsTerm[i] == true)? "V" : "v") + i;
                }
                txt += "))\n";
            }
        }

        txt += "\n";

        facts.forEach(function(fact) {
            var factVarIsBinding = checkFact(fact, null, null, true);
            for (var i = 0; i < fact.Skin.VarNames.length; i++) {
                fact.Skin.VarNames[i] = (factVarIsBinding[i] ? "v" : "V") + i;
            }
            // We allow binding vars to have free lists, but ghilbert doesn't.
            fact.Core[Fact.CORE_FREE] = fact.Core[Fact.CORE_FREE].filter(
                function(freeList) { return !factVarIsBinding[freeList[0]]; });
        });

        queue.drain = function() {
            cb(null, txt);
        }
        queue.push(facts);
    }
}

Context.prototype = new Context();
// terms seen in any context: map from array of Booleans for isTermVar
// (null, true, false)
Context.prototype.terms = {};
// map from mark to factVarIsBinding array
// This is needed for proofs like 'eqid' where binding vars disappear. Oof.
Context.prototype.markToFvib = {};



var proofCtx = new Context();
var ifaceCtx = new Context();


var log = require('./factlog.js');
log.facts.forEach(function(factObj) {
    var fact = new Fact(factObj);

    state.factsByMark[fact.getMark()] = fact;
    if (factObj && factObj.Tree && factObj.Tree.Proof && factObj.Tree.Proof.length > 0) {
        if (!factObj.Tree.Cmd) {
            factObj.Tree.Cmd = 'thm';
        }
        proofCtx.append(new Fact(factObj));
    } else {
        if (!factObj.Tree) factObj.Tree = {};
        factObj.Tree.Cmd = 'stmt';
        ifaceCtx.append(new Fact(factObj));
    }
});

DEBUG=true

// ==== Verify ====
GH = global.GH = {};
global.log = console.log;
require('../../caghni/js/verify.js')
require('../../caghni/js/proofstep.js')

var UrlCtx = {
    files: {},
    resolve: function(url) {
        return this.files[url];
    }
}


function run(url_context, url, context) {
    var scanner = new GH.Scanner(url_context.resolve(url).split(/\r?\n/));
    while (true) {
        var command = GH.read_sexp(scanner);
        if (command === null || command === undefined) {
            return true;
        }
        if (GH.typeOf(command) != 'string') {
            throw 'Command must be atom';
        }
        // We don't care about styling, but apparently we need to participate in passing
        // it around.
        var styling = scanner.styleScanner.get_styling('');
        var arg = GH.read_sexp(scanner);
        context.do_cmd(command, arg, styling);
        scanner.styleScanner.clear();
    }
    return false;
}

var verifyCtx = new GH.VerifyCtx(UrlCtx, run);

ifaceCtx.inferTerms();
proofCtx.inferTerms();
Async.parallel(
    {iface:ifaceCtx.toString, proof:proofCtx.toString},
    function(err, results) {
        UrlCtx.files["tmp2.ghi"] = results.iface;
        UrlCtx.files["tmp2.gh"] = results.proof;
        if (DEBUG) {
            console.log("==== IFACE ====\n" + results.iface);
            console.log("==== PROOF ====\n" + results.proof.substr(00000));
        }
        try {
            run(UrlCtx, "tmp2.gh", verifyCtx);
        } catch (e) {
            console.log(e.toString());
            throw(new Error(e));
        }
    });
/**/
