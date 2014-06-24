var Fs = require('fs');
var Bencode = require('bencode');
var Crypto = require('crypto');
var Fact = require('../../caghni/js/fact.js'); //XXX
var Async = require('async');

var lands = [];
var state = {};

var TODO_DETACHMAP = {};

var DEBUG = false;

state.factsByMark = {};
function sfbm(mark) {
    var fact = state.factsByMark[mark];
    if (!fact) throw new Error("mark not found: " + mark);
    return fact;
}

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

function getLand(filename) {
    // Uses eval instead of json to allow comments and naked keys.
    // This is almost certainly a terrible idea.
    var land = eval("("+Fs.readFileSync(filename,'utf8')+")");
    land.facts = [];
    land.addFact = function(f){
        var fact = new Fact(f);
        if (DEBUG) {
            console.log("# Adding fact: " + JSON.stringify(fact));
        }
        fact = canonicalize(fact);
        if (DEBUG) {
            console.log("# Canonically: " + JSON.stringify(fact));
        }
        state.factsByMark[fact.getMark()] = fact;
        return fact;
    }
    function addAxiom(fact) {
        if (!fact.Tree) {
            fact.Tree = {};
        }
        fact.Tree.Cmd = "stmt";

        fact = land.addFact(fact);
        ifaceCtx.append(fact);
    }

    if (land.axioms) land.axioms.forEach(addAxiom);
    if (land.inferences) land.inferences.forEach(addAxiom);
    lands.push(land);
    state.land = land;
    state.goal = 0;

    return land;
}

function fingerprint(obj) {
    var hash = Crypto.createHash('sha1');
    hash.update(Bencode.encode(obj));
    return "bencode-sha1-" + hash.digest('hex');
}

function clone(obj) {
    return JSON.parse(JSON.stringify(obj));
}

function makeMark(fact) {
    return new Fact(fact).getMark();
}

function nameDep(workFact, depFact) {
    var n = workFact.nameDep(fingerprint(depFact.getMark()), depFact);
    return n;
}

function startWork(fact) {
    var work = new Fact(clone(fact));
    work.setHyps([clone(work.Core[Fact.CORE_STMT])]);
    work.Skin.HypNames = ["Hyps.0"];
    function nameVar(varNum) {
        work.Skin.VarNames[varNum] = "V" + varNum;
    }
    eachVarOnce(work.Core[Fact.CORE_STMT], nameVar);
    if (!work.Tree.Cmd) {
        work.setCmd("thm");
    }
    work.setProof(["Hyps.0"]);
    return new Fact(work);
}


// NB: not the same as orcat's xpath definition. Pass 0 to get the term.
function zpath(exp, path) {
    var a = exp, l = path.length, i = 0;
    for (i = 0; i < l; i++) {
        a=a[path[i]];
    }
    return a;
}

// Visits each var exactly once, in left-to-right depth-first order
function eachVarOnce(exp, cb, seen) {
    seen = seen || {};
    if (!Array.isArray(exp)) {
        if (!seen[exp]) {
            seen[exp] = 1;
            cb(exp);
        }
    } else {
        for (var i = 1; i < exp.length; i++) {
            eachVarOnce(exp[i], cb, seen);
        }
    }
}

function newDummy() {
    return "DUMMY_" + Math.random(); //XXX
}

function undummy(workOrExp, dummyMap) {
    function replaceDummies(x) {
        // TODO: handle freemap dummies correctly!
        if (Array.isArray(x)) {
            for (var i = 1; i < x.length; i++) {
                x[i] = replaceDummies(x[i]);
            }
            return x;
        } else if ((typeof x == 'number') || (typeof x == 'string')) {
            while (dummyMap[x] != undefined) {
                x = dummyMap[x];
            }
            return Array.isArray(x) ? replaceDummies(x) : x;
        } else {
            throw new Error("hmm")
        }
    }
    if (DEBUG) {
        for (var v in dummyMap) if (dummyMap.hasOwnProperty(v)) {
            console.log("#XXXX Dummy:" + v + "=> " + JSON.stringify(dummyMap[v]));
        }
    }
    if ((typeof workOrExp == 'number') || Array.isArray(workOrExp)) {
        return replaceDummies(workOrExp);
    } else {
        workOrExp.Core[Fact.CORE_STMT] = replaceDummies(
            workOrExp.Core[Fact.CORE_STMT])
        workOrExp.Core[Fact.CORE_HYPS] =
            workOrExp.Core[Fact.CORE_HYPS].map(replaceDummies);
        workOrExp.Tree.Proof =
            workOrExp.Tree.Proof.map(replaceDummies);
        // TODO: undummy freemap
        if (DEBUG) {
            console.log("#XXXX Work undummied: " + JSON.stringify(workOrExp));
        }
        return workOrExp;
    }
}

// Returns a list of mandatory hypotheses (i.e., values for each var) of the
// fact, such that the named subexpression of the fact's stmt matches the named
// subexpression of the work's first hyp.
// @param TODO
// @return a list of terms (in the work's variables). dummy variables will get
//     no assignment.
// @throws an error if the unification is impossible or would violate a Free
//     constraint.
// TODO: HACK: or you can give a factHypPath instead.
function getMandHyps(work, hypPath, fact, stmtPath, factHypPath) {
    var debugPath = [];
    var nonDummy = {};
    var dummyMap = {};
    eachVarOnce(work.Core[Fact.CORE_STMT], function(v) {
        nonDummy[v] = v;
    });
    // from fact vars to work exps
    var varMap = {};
    var workExp = zpath(work.Core[Fact.CORE_HYPS][0], hypPath);
    var factExp;
    if (stmtPath !== null) {
        factExp = zpath(fact.Core[Fact.CORE_STMT], stmtPath);
    } else {
        factExp = zpath(fact.Core[Fact.CORE_STMT], factHypPath);
    }
    if (workExp == undefined) {
        throw new Error("Bad work path:\n" + hypPath + "\n" +
                        JSON.stringify(work));
    }
    if (factExp == undefined) {
        throw new Error("Bad fact path:\n" + stmtPath + "\n" +
                        JSON.stringify(fact));
    }
    function assertEqual(msgTag, thing1, thing2) {
        if (thing1 !== thing2) {
            throw new Error("Unification error: " + msgTag + " @ " +
                            JSON.stringify(debugPath) +
                            "\nWork:  " + JSON.stringify(workExp) +
                            "\nFact:  " + JSON.stringify(factExp) +
                            "\nWant:  " + thing1 + " === " + thing2);
        }
    }
    function assertNotFree(exp, freeMap) {
        if (!Array.isArray(exp)) {
            assertEqual("free", freeMap[exp], undefined);
        } else {
            for (var i = 1; i < exp.length; i++) {
                debugPath.push(i);
                assertNotFree(exp[i], freeMap);
                debugPath.pop();
            }
        }
    }
    function getFreeList(factVarName) {
        var freeMap = fact.Core[Fact.CORE_FREE];
        if (!freeMap) {
            return undefined;
        }
        // TODO: could be faster.
        for (var i = 0; i < freeMap.length; i++) {
            if (freeMap[i][0] === factVarName) {
                var free = {};
                freeMap[i].slice(1).forEach(function(v) {
                    free[v] = 1;
                });
                return free;
            }
        }
        return undefined;
    }
    function mapVarTo(factVarName, workExp) {
        // Check freemap. TODO: untested
        var free = getFreeList(factVarName);
        if (free) {
            assertNotFree(workExp, free);
        }
        if (factVarName == undefined) {
            throw new Error("undefined varMap to " + JSON.stringify(workExp));
        }
        varMap[factVarName] = workExp;
    }
    function recurse(workSubExp, factSubExp, alreadyMapped) {
        if (!alreadyMapped && !Array.isArray(factSubExp) &&
            (varMap[factSubExp] != undefined)) {
            factSubExp = varMap[factSubExp];
            alreadyMapped = true;
        }
        if (alreadyMapped) {
            while (dummyMap[factSubExp]) {
                factSubExp = dummyMap[factSubExp];
            }
        }
        while (dummyMap[workSubExp]) {
            workSubExp = dummyMap[workSubExp];
        }


        if ((hypPath.length == 0) &&
            (stmtPath.length == 0) &&
            Array.isArray(workSubExp) &&
            (workSubExp[0] == work.Tree.Definiendum)) {
            // When grounding a defthm, the statement left on the stack
            // doesn't match the Core's STMT until the substitution is
            // applied.
            // TODO: but we *should* be checking the consistency of the
            // substitution....
            return;
        }

        if (!Array.isArray(factSubExp)) {
            if (alreadyMapped) {
                if (Array.isArray(workSubExp)) {
                    assertEqual("mappedA", factSubExp, workSubExp)
                }
                if (!nonDummy[workSubExp]) {
                    if (factSubExp != workSubExp) {
                        dummyMap[workSubExp] = factSubExp;
                    }
                } else if (!nonDummy[factSubExp]) {
                    if (factSubExp != workSubExp) {
                        dummyMap[factSubExp] = workSubExp;
                    }
                } else {
                    assertEqual("mapped", factSubExp, workSubExp);
                }
            } else {
                mapVarTo(factSubExp, workSubExp);
            }
        } else {
            var factTerm = (alreadyMapped ? work : fact).Skin.TermNames[
                factSubExp[0]];
            if (factTerm == undefined) {
                throw new Error("No factTerm\n" +
                                JSON.stringify(fact) + "\n" +
                                JSON.stringify(factSubExp));
            }
            if (!Array.isArray(workSubExp)) {
                // Work is var, Fact is exp.
                if (nonDummy[workSubExp]) {
                    assertEqual("shrug", workSubExp, factSubExp); //XXX
                } else {
                    var newExp = [];
                    newExp.push(work.nameTerm(factTerm));
                    for (var i = 1; i < factSubExp.length; i++) {
                        newExp.push(work.nameVar(newDummy()));
                    }
                    dummyMap[workSubExp] = newExp;
                    workSubExp = newExp;
                }
            }
            if (Array.isArray(workSubExp)) {
                // exp - exp
                var workTerm = work.Skin.TermNames[workSubExp[0]];
                assertEqual("term", workTerm, factTerm);
                assertEqual("arity", workSubExp.length, factSubExp.length);
                for (var i = 1; i < workSubExp.length; i++) {
                    debugPath.push(i);
                    // TODO: possible infinite loop here on bad unification
                    recurse(workSubExp[i], factSubExp[i], alreadyMapped);
                    debugPath.pop();
                }
            }
        }
    }
    recurse(workExp, factExp, false);
    undummy(work, dummyMap);
    //console.log("Unified: " + JSON.stringify(varMap));
    for (x in varMap) if (varMap.hasOwnProperty(x)) {
        varMap[x] = undummy(varMap[x], dummyMap);
    }
    return varMap;
}


function queryPushUp(goalOp, goalArgNum, goalOpArity, toolOp, toolArgNum) {
    // Try covariant first, then contravariant if not found.
    var p = new PushUp(goalOp, goalArgNum, goalOpArity, toolOp, toolArgNum, true);
    if (!state.factsByMark[p.mark]) {
        p = new PushUp(goalOp, goalArgNum, goalOpArity, toolOp, toolArgNum, false);
        if (!state.factsByMark[p.mark]) {
            throw new Error("No pushUp found for " + JSON.stringify(arguments));
        }
    }
    return p;
}

function queryDetach(params) {
    // TODO
    var detach = TODO_DETACHMAP[params];
    if (!detach) {
        throw new Error("No detach found for " + JSON.stringify(params));
    }
    return detach;
}

function globalSub(fact, varMap, work) {
    function mapper(x) {
        if (Array.isArray(x) && (x.length > 0)) {
            var out = x.slice(1).map(mapper);
            out.unshift(work.nameTerm(fact.Skin.TermNames[x[0]]));
            return out;
        } else {
            if (varMap[x] == undefined) {
                throw new Error("Unmapped var " + x);
            }
            return varMap[x];
        }
    }
    return mapper(fact.Core[Fact.CORE_STMT]);
}
function applyFact(work, workPath, fact, factPath) {
    var varMap = getMandHyps(work, workPath, fact, factPath);
    if (DEBUG) {console.log("# MandHyps: " + JSON.stringify(varMap));}
    // If that didn't throw, we can start mutating
    // PushUpScratchPad
    var pusp = {};

    pusp.newSteps = [];
    if (DEBUG) console.log("Vars from " + JSON.stringify(fact));
    eachVarOnce(fact.Core[Fact.CORE_STMT], function(v) {
        var newV = varMap[v];
        if (DEBUG) {console.log("v=" + v + ", newV=" + varMap[v]);}
        if (newV == undefined) {
            newV = work.nameVar(newDummy()); // XXX HACK
            varMap[v] = newV;
        }
        if (DEBUG) {console.log("v=" + v + ", newV=" + varMap[v]);}
        pusp.newSteps.push(newV);
    });
    pusp.newSteps.push(nameDep(work, fact));
    // Now on the stack: an instance of fact, with factPath equalling a subexp
    // of work.

    // #. add appropriate grease for generification and equivalences
    // --> TODO: change caghni to list kinds before terms for easy grease lookup
    // #. invoke sequence of pushup theorems, ensuring presence in Deps
    pusp.tool = globalSub(fact, varMap, work); // what's on the stack
    pusp.toolPath = clone(factPath);           // path to subexp A
    pusp.goal = clone(work.Core[Fact.CORE_HYPS][0]);      // what we want to prove
    pusp.goalPath = clone(workPath);           // path to subexp B
    // invariant: subexp A == subexp B
    function checkInvariant() {
        if (DEBUG) {
            console.log("Check invariant: \n" +
                        JSON.stringify(zpath(pusp.tool, pusp.toolPath)) +
                        "\n" +
                        JSON.stringify(zpath(pusp.goal, pusp.goalPath)));
            console.log("XXXX pusp: ", JSON.stringify(pusp));
        }
        if (JSON.stringify(zpath(pusp.tool, pusp.toolPath)) !=
            JSON.stringify(zpath(pusp.goal, pusp.goalPath))) {
            throw new Error("Invariant broken!");
        }
    }

    while (pusp.goalPath.length > 0) {
        checkInvariant();
        var goalArgNum = pusp.goalPath.pop();
        var goalParent = zpath(pusp.goal, pusp.goalPath);
        var goalTerm = work.Skin.TermNames[goalParent[0]];
        var goalTermArity = goalParent.length;
        pusp.goalPath.push(goalArgNum);
        var toolArgNum = pusp.toolPath.pop();
        var toolTerm = work.Skin.TermNames[zpath(pusp.tool, pusp.toolPath)[0]];
        pusp.toolPath.push(toolArgNum);

        queryPushUp(goalTerm, goalArgNum, goalTermArity, toolTerm,
                     pusp.toolPath[pusp.toolPath.length - 1]).
            pushUp(pusp, work);

    }
    checkInvariant();

    // Now, since the invariant holds and goalPath = [], and
    // tool[toolPath[0]] == goal, so just detach.
    var query = [work.Skin.TermNames[pusp.tool[0]], pusp.toolPath];
    queryDetach(query).detach(pusp, work);

    // #. compute new preimage and update Hyps.0
    // TODO: hardcoded for now

    // don't delete any steps
    pusp.newSteps.unshift(0);
    // keep the "hyps.0".
    pusp.newSteps.unshift(1);
    work.Tree.Proof.splice.apply(work.Tree.Proof, pusp.newSteps);


    // TODO:
    // #. update DV list
    // #. renumber all the vars
    // #. Add explanatory comments to Skin.Delimiters
    return work;
}

function applyInference(work, infFact) {
    PICKUP()

    var varMap = getMandHyps(work, [], infFact, );
    if (DEBUG) {console.log("# MandHyps: " + JSON.stringify(varMap));}

    var newSteps = [work.Tree.Proof[0]];
    newSteps.push(nameDep(work, infFact));
    newSteps.push.apply(work.Tree.Proof.slice(1));
    
}
// Replace a dummy variable with a new exp containing the given term and some
// new dummy variables.
function specifyDummy(work, dummyPath, newTerm, newTermArity) {
    // TODO: duplicated code
    var nonDummy = {};
    var dummyMap = {};
    eachVarOnce(work.Core[Fact.CORE_STMT], function(v) {
        nonDummy[v] = v;
    });
    var workExp = zpath(work.Core[Fact.CORE_HYPS][0], dummyPath);
    if (workExp == undefined) {
        throw new Error("Bad work path:\n" + dummyPath + "\n" +
                        JSON.stringify(work));
    }
    if (nonDummy[workExp]) {
        throw new Error("Var " + workExp + " is no dummy!");
    }
    var newExp = [work.nameTerm(newTerm)];
    for (var i = 0; i < newTermArity; i++) {
        newExp.push(work.nameVar(newDummy()));
    }
    dummyMap[workExp] = newExp;
    return undummy(work, dummyMap);
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
            txt += ghTxt;
            cb(err);
        });
    },1);
    this.append = function(x) {
        if (!x || !x.Core) {
            throw new Error("Bad fact: " + JSON.stringify(x));
        }
        facts.push(x);
        return this;
    }


    function checkFact(fact, termsAreDone) {
        var factVarIsBinding = [];
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
                    if (termArgIsTerm.length < i) {
                        termArgIsTerm[i] = null;
                    }
                    // Positive termness in an arg constrains the term.
                    if (checkExp(arg) == false) {
                        if (termArgIsTerm[i] == false) {
                            throw new Error("term arg mismatch");
                        } else {
                            termArgIsTerm[i] = true;
                        }
                    }
                    // Positive (or presumptive) bindingness from the term
                    // constrains var arg
                    if ((termArgIsTerm[i] == false) ||
                        (termsAreDone && (termArgIsTerm[i] == null))) {
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
                if (exp >= maxVar.length) maxVar[exp] = exp;
                return factVarIsBinding[exp];
            } else {
                // Strings in proof require no checking
                return null;
            }
        }
        function checkFreemap(fm) {
            factVarIsBinding[fm[0]] = false;
            fm.slice(1).forEach(function(v) {
                factVarIsBinding[v] = true;
            });
        }
        fact.Core[Fact.CORE_FREE].forEach(checkFreemap);
        fact.Core[Fact.CORE_HYPS].forEach(checkExp);
        checkExp(fact.Core[Fact.CORE_STMT]);
        if (fact.Tree.Proof) {
            fact.Tree.Proof.forEach(checkExp);
        }
        // TODO: we might need to propagate these changes by running through
        // again. E.g. suppose var 0 is only passed to a new term in the
        // stmt; but in the proof it is passed to a term known to be binding
        // on that arg. Then the var doesn't get marked binding until the
        // proof check, but this should be propagated up to the new term.
        // This might cascade...
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
                    txt += " " + (termArgIsTerm[i] ? "V" : "v") + i;
                }
                txt += "))\n";
            }
        }
        
        txt += "\n";

        facts.forEach(function(fact) {
            var factVarIsBinding = checkFact(fact, true);
            for (var i = 0; i < fact.Skin.VarNames.length; i++) {
                fact.Skin.VarNames[i] = (factVarIsBinding[i] ? "v" : "V") + i;
            }
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

var proofCtx = new Context();
var ifaceCtx = new Context();


var landRarr = getLand("land_rarr.js");
var ax1 =   sfbm('[[],[0,0,[0,1,0]],[]];["&rarr;"]');
var imim1 = sfbm('[[],[0,[0,0,1],[0,[0,1,2],[0,0,2]]],[]];["&rarr;"]');
var imim2 = sfbm('[[],[0,[0,0,1],[0,[0,2,0],[0,2,1]]],[]];["&rarr;"]');
var pm243 = sfbm('[[],[0,[0,0,[0,0,1]],[0,0,1]],[]];["&rarr;"]');
var axmp =  sfbm('[[0,[0,0,1]],1,[]];["&rarr;"]');

TODO_DETACHMAP[["&rarr;",[2]]] = {
    mark:'[[0,[0,0,1]],1,[]];["&rarr;"]',
    detach: function(pusp, work) {
        var detachFact = sfbm(this.mark);
        pusp.newSteps.push(nameDep(work, detachFact));
        work.Core[Fact.CORE_HYPS][0] = pusp.tool[1];
    }
};
TODO_DETACHMAP[["&harr;",[2]]] = {
    mark:'[[],[0,[1,0,1],[0,0,1]],[]];["&rarr;","&harr;"]',
    detach: function(pusp, work) {
        var detachFact = sfbm(this.mark);
        pusp.newSteps.push(pusp.tool[1]);
        pusp.newSteps.push(pusp.tool[2]);
        pusp.newSteps.push(nameDep(work, detachFact));
        pusp.newSteps.push(nameDep(work, axmp)); // XXX
        pusp.newSteps.push(nameDep(work, axmp)); // XXX
        work.Core[Fact.CORE_HYPS][0] = pusp.tool[1];
    }
};
TODO_DETACHMAP[["&harr;",[1]]] = {
    mark:'[[],[0,[1,0,1],[0,1,0]],[]];["&rarr;","&harr;"]',
    detach: function(pusp, work) {
        var detachFact = sfbm(this.mark);
        pusp.newSteps.push(pusp.tool[1]);
        pusp.newSteps.push(pusp.tool[2]);
        pusp.newSteps.push(nameDep(work, detachFact));
        pusp.newSteps.push(nameDep(work, axmp)); // XXX
        pusp.newSteps.push(nameDep(work, axmp)); // XXX
        work.Core[Fact.CORE_HYPS][0] = pusp.tool[2];
    }
};


// goalOp is an goalOpArity-arg term.
// goalArg is in 1...goalOpArity, specifying which argchild the goal is
// toolOp is the name of a 2-arg binary term
// toolArg is 1 or 2, specifying one of the args of the tool on the stack.
// the current goal's paren'ts [goalArg] equals the current tool's [toolArg]
// we want to replace it with the tool's other arg.
// isContra tells whether the tool args will be reversed in order.
function PushUp(goalOp, goalArg, goalOpArity, toolOp, toolArg, isContra) {
    this.goalOp = goalOp;
    this.goalArg = goalArg;
    this.goalOpArity = goalOpArity;
    this.toolOp = toolOp;
    this.toolArg = toolArg;
    this.isContra = isContra;
    // Goal's parent: [goalOp, g0, g1, ..., gGoalArg=Goal, ...]
    // Tool: [toolOp, otherToolArg, tToolArg=Goal]
    // new goal: [goalOp, g0, g1, ..., otherToolArg, ...]
    // pushup: [rarr, [toolOp, otherToolArg, Goal],
    //                [toolOp, [goalOp, ...Goal...],          // isContra swaps
    //                         [goalOp, ...otherToolArg...]]] // these two
    var tmpFact = new Fact;
    var termNames = [];
    var rarrN = tmpFact.nameTerm("&rarr;");
    var toolN = tmpFact.nameTerm(toolOp);
    var goalN = tmpFact.nameTerm(goalOp);
    //var stmt = [rarrN, [toolN, 0, 1], [toolN, [goalN, ...], [goalN, ...]]]
    var arr1 =                                  [goalN];
    var arr2 =                                                [goalN];
    var nextVar = 2;
    for (var i = 1; i < goalOpArity; i++) {
        if (i != goalArg) {
            arr1[i] = arr2[i] = nextVar++;
        }
    }
    arr1[goalArg] = toolArg - 1;
    arr2[goalArg] = 2 - toolArg;
    var stmt =  [rarrN, [toolN, 0, 1], [toolN,
                                        isContra ? arr2 : arr1,
                                        isContra ? arr1 : arr2]];
    tmpFact.setStmt(stmt);
    this.mark = tmpFact.getMark();
}
PushUp.prototype = new PushUp();
PushUp.prototype.pushUp = function(pusp, work) {
    pusp.newSteps.push(pusp.tool[1]);
    pusp.newSteps.push(pusp.tool[2]);
    pusp.goalPath.pop();
    var goalParent = zpath(pusp.goal, pusp.goalPath);
    var goalN = work.nameTerm(this.goalOp);
    var arr1 = [goalN];
    var arr2 = [goalN];
    for (var i = 1; i < this.goalOpArity; i++) {
        if (i == this.goalArg) {
            arr1.push(pusp.tool[this.toolArg]);
            arr2.push(pusp.tool[3 - this.toolArg]);
        } else {
            var arg = goalParent[i];
            pusp.newSteps.push(arg);
            arr1.push(arg);
            arr2.push(arg);
        }
    }
    var pushupFact = sfbm(this.mark);
    pusp.newSteps.push(nameDep(work, pushupFact));
    pusp.newSteps.push(nameDep(work, axmp));
    var toolN = work.nameTerm(this.toolOp);
    pusp.tool = [toolN,
                 this.isContra ? arr2 : arr1,
                 this.isContra ? arr1 : arr2];
    pusp.toolPath = [this.isContra ? 2 : 1];
}

function ground(work, dirtFact) {
    // verify that the hyp is an instance of the dirt
    var varMap = getMandHyps(work, [], dirtFact, []);
    if (DEBUG) {console.log("# ground MandHyps: " + JSON.stringify(varMap));}
    work.Core[Fact.CORE_HYPS].shift();
    var newSteps = [];
    eachVarOnce(dirtFact.Core[Fact.CORE_STMT], function(v) {
        var newV = varMap[v];
        if (newV == undefined) {
            newV = work.nameVar(newDummy()); // XXX HACK
            varMap[v] = newV;
        }
        newSteps.push(newV);
    });
    newSteps.push(nameDep(work, dirtFact));

    // remove hyp step
    work.Tree.Proof.shift();
    // Replace with proof of hyp instance
    work.Tree.Proof.unshift.apply(work.Tree.Proof, newSteps);
    if (DEBUG) {console.log("#XXXX Work before canon:" + JSON.stringify(work));}

    work = canonicalize(work);
    return work;
}

// Reorders terms/variables so that they appear in first-used order.
// Removes no-longer-used dummies.
// Renames remaining variable Skins to Vn
// TODO: sort deps alphabetically?
function canonicalize(work) {
    var out = new Fact();
    function mapTerm(t) {
        return out.nameTerm(work.Skin.TermNames[t]);
    }
    function mapExp(exp) {
        if (Array.isArray(exp) && (exp.length > 0)) {
            var t = mapTerm(exp[0]);
            var mapped = exp.slice(1).map(mapExp);
            mapped.unshift(t);
            return mapped;
        } else if (typeof exp == 'number') {
            return out.nameVar("V" + exp);
        } else {
            return exp;
        }
    }
    for (var i = 0; i < work.Core[Fact.CORE_HYPS].length; i++) {
        out.Core[Fact.CORE_HYPS][i] = mapExp(work.Core[Fact.CORE_HYPS][i]);
        out.Skin.HypNames[i] = "Hyps." + i;
    }
    out.setStmt(mapExp(work.Core[Fact.CORE_STMT]));
    if (DEBUG) {
        console.log("\nwork=" + JSON.stringify(work) +
                    "\nfact=" +JSON.stringify(out));
    }
    out.setFree(work.Core[Fact.CORE_FREE].map(function(f) {
        return f.map(mapExp);}));

    out.setProof(work.Tree.Proof.map(mapExp));
    out.setCmd(work.Tree.Cmd);
    out.setName(fingerprint(out.getMark()));
    out.Tree.Deps = work.Tree.Deps.map(function(d) {
        return [clone(d[0]), d[1].map(mapTerm)];
    });
    if (work.Tree.Definiendum != undefined) {
        out.Tree.Definiendum = mapTerm(work.Tree.Definiendum);
    }

    for (var n = 0; n < out.Skin.VarNames.length; n++) {
        out.Skin.VarNames[n] = "V" + n;
    }
    return out;
}



startNextGoal();
// |- (PQR)(PQ)PR => |- (PQR)(PQ)PR
state.work = applyFact(state.work, [2,2], pm243, [2]);
// |- (PQR)(PQ)PPR => |- (PQR)(PQ)PR
state.work = applyFact(state.work, [2,1], imim1, [1]);
// |- (P(QR))((Qr)(Pr))(P(PR)) => |- (PQR)(PQ)PR
state.work = ground(state.work, imim1);
// |- (PQR)(PQ)PR
var ax2 = saveGoal();

// Apparatus for importing proofs from orcat_test.js
var thms = {};
thms.imim1 = imim1;
thms.imim2 = imim2;
thms.Distribute = ax2;
thms.Simplify = ax1;

var stack = []; // goalPath, fact, factPath
function startNextGoal() {
    var goal = state.land.goals[state.goal];
    if (!goal) throw new Error("no more goals!");
    state.work = startWork(goal);
}
function saveGoal() {
    state.land.addFact(state.work);
    proofCtx.append(state.work);
    state.goal++;
    return state.work;
}
function startWith(fact) {
    stack = [[fact]];
}
function getArity(tok) {
    switch(tok) {
    case 'Oslash':
        return 0;
    case 'not':
        return 1;
    case 'rarr':
    case 'harr':
    case 'and':
    case 'or':
    case 'forall':
        return 2;
    default:
        return -1;
    }
}

function parseMark(str) { // parse orcat's thm names
    var out = new Fact();
    if (str[0] == '_') throw new Error("todo");
    var toks = str.split("_");
    function recurse() {
        var tok = toks.shift();
        var arity = getArity(tok);
        console.log("tok " + tok  +" arity " + arity);
        if (arity == -1) {
            return out.nameVar(tok);
        } else {
            var exp = [out.nameTerm('&' + tok + ';')];
            for (var i = 0; i < arity; i++) {
                exp.push(recurse());
            }
            return exp;
        }
    }
    out.setStmt(recurse());
    return out.getMark();
}
function applyArrow(path, fact, side) {
    if (typeof fact == 'string') {
        fact = sfbm(parseMark(fact));
    }
    stack.unshift([path.map(function(x){return x+1;}), fact, [2 - side]]);
}
function generify() {
    stack.unshift(generify);
}

function save() {
    startNextGoal();
    stack.forEach(function(step) {
        if (DEBUG) {console.log("# XXXX Work now: " + JSON.stringify(state.work));}
        try {
            if (step == generify) {
                // ??? PICKUP
            } else if (step.length > 1) {
                state.work = applyFact(state.work, step[0], step[1], step[2]);
            } else {
                state.work = ground(state.work, step[0]);
            }
        } catch (e) {
            console.log("Error in step " + JSON.stringify(step) +
                        "\nwork=" + JSON.stringify(state.work));
            throw(e);
        }

    });
    if (DEBUG) {console.log("# XXXX Work now: " + JSON.stringify(state.work));}
    saveGoal();
    startWith(state.work);
    return state.work;
}

// ==== BEGIN import from orcat_test.js ====
startWith(thms.Simplify);
applyArrow([], thms.imim1, 0);
thms.himp1 = save();

startWith(thms.Distribute);
applyArrow([1,0],thms.Simplify, 1);
thms.con12 = save();


startWith(thms.Simplify);
applyArrow([], thms.Distribute, 0);
thms.iddlem1 = save();

startWith(thms.iddlem1)
applyArrow([0], thms.Simplify, 1);
thms.idd = save();

applyArrow([], thms.idd, 0);
thms.id = save();

startWith(thms.Distribute);
applyArrow([0], thms.idd, 1);
applyArrow([1,0], thms.Simplify, 1);
thms.mpd = save();

applyArrow([], thms.mpd, 0);
thms.mp = save();
startWith(thms.id);
applyArrow([], thms.mp, 0);
thms.idie = save();

// XXX already defined
//startWith(thms.mp);
//applyArrow([], thms.Distribute, 0);
//thms.contract = save();
thms.contract = pm243;

// Level 2

var landNot = getLand("land_not.js");

thms.Transpose = sfbm('[[],[0,[0,[1,0],[1,1]],[0,1,0]],[]];["&rarr;","&not;"]');

startWith(thms.Simplify);
applyArrow([1], thms.Transpose, 0);
thms.fie = save();
startWith(thms.fie);
applyArrow([1], thms.Transpose, 0);
applyArrow([1], thms.idie, 0);
thms.nn1 = save();
startWith(thms.fie);
applyArrow([1], thms.Transpose, 0);
applyArrow([1], thms.idie, 0);
applyArrow([], thms.Transpose, 0);
thms.nn2 = save();
startWith(thms.Transpose);
applyArrow([0,1], thms.nn2, 1);
applyArrow([0,0], thms.nn1, 0);
thms.con3 = save();

//XXX TODO PICKUP scheme.setBinding(not, 0, scheme.RIGHT(), thms.con3);

startWith(thms.Simplify);
applyArrow([], thms.con3, 0);
thms.nimp2 = save();
startWith(thms.fie);
applyArrow([], thms.con3, 0);
applyArrow([1], thms.nn1, 0);
thms.nimp1 = save();
startWith(thms.mp);
applyArrow([1], thms.con3, 0);
thms.conjnimp = save();
startWith(thms.fie);
applyArrow([], thms.Distribute, 0);
applyArrow([1], thms.Transpose, 0);
applyArrow([1], thms.idie, 0);
thms.contradict = save();


startWith(thms.id);
applyArrow([], thms.conjnimp, 0);
applyArrow([0], thms.nn2, 1);
applyArrow([], thms.idie, 0);
thms.dfand = save();

var landHarr = getLand("land_and.js");
startNextGoal();
state.work = ground(state.work, thms.dfand);
thms.Conjoin = saveGoal();

//scheme.setBinding(not, 0, scheme.RIGHT(), thms.con3); // TODO

startWith(thms.Conjoin);
applyArrow([], thms.nimp1, 0);
thms.and1 = save();

startWith(thms.Conjoin);
applyArrow([], thms.nimp2, 0);
applyArrow([], thms.nn1, 0);
thms.and2 = save();

startWith(thms.imim1);
applyArrow([1], thms.con3, 0);
applyArrow([1,0], thms.and1, 1);
applyArrow([1,1], thms.and2, 0);
thms.anim1 = save();

// scheme.setBinding(and, 0, scheme.LEFT(), thms.anim1); // TODO

startWith(thms.imim2);
applyArrow([1], thms.con3, 0);
applyArrow([1,1], thms.and2, 0);
applyArrow([1,0], thms.and1, 1);
applyArrow([0], thms.con3, 1);
thms.anim2 = save();

// scheme.setBinding(and, 1, scheme.LEFT(), thms.anim2); // TODO


startWith(thms.and1);
applyArrow([1], thms.nimp1, 0);
thms.andl = save();

startWith(thms.and1);
applyArrow([1], thms.nimp2, 0);
applyArrow([1], thms.nn1, 0);
thms.andr = save();

startWith(thms.conjnimp);
applyArrow([1,1], thms.and2, 0);
applyArrow([1,0], thms.nn2, 1);
thms.conj = save();

startWith(thms.conj);
applyArrow([], thms.contract, 0);
thms.anid = save();


startWith(thms.and1);
applyArrow([1,0], thms.Transpose, 1);
applyArrow([1,0,0], thms.nn1, 0);
applyArrow([1], thms.and2, 0);
thms.ancom = save();

startWith(thms.anim2);
applyArrow([1,0], thms.anid, 1);
thms.ancr = save();

startWith(thms.andr);
applyArrow([], thms.imim1, 0);
applyArrow([], thms.imim2, 0);
applyArrow([1], thms.contract, 0);
applyArrow([0,0], thms.andl, 0);
thms.imprt = save();

startWith(thms.mp);
applyArrow([], thms.imprt, 0);
thms.anmp = save();

startWith(thms.andl);
applyArrow([1], thms.conj, 0);
applyArrow([1], thms.imim2, 0);
applyArrow([], thms.ancr, 0);
applyArrow([1,0], thms.andr, 0);
applyArrow([1], thms.anmp, 0);
thms.anim3 = save();

startWith(thms.anim3);
applyArrow([1,1], thms.ancom, 0);
applyArrow([1,1], thms.anim3, 0);
applyArrow([1], thms.imprt, 0);
applyArrow([1,0], thms.ancom, 1);
applyArrow([1,1], thms.ancom, 0);
thms.prth = save();

var landHarr = getLand("land_harr.js");


startWith(thms.id);
applyArrow([], thms.conj, 0);
applyArrow([], thms.idie, 0);
thms.dfbi = save();

startNextGoal();
state.work = ground(state.work, thms.dfbi);
thms.Equivalate = saveGoal();

//  scheme.setEquivalence(exports.wff, harr); // TODO
  startWith(thms.Equivalate);
  applyArrow([], thms.andl, 0);
  thms.defbi1 = save();

  startWith(thms.Equivalate);
  applyArrow([], thms.andr, 0);
  thms.defbi2 = save();

  startWith(thms.defbi1);
  applyArrow([1], thms.andl, 0);
  thms.bi1 = save();

//  scheme.setEquivalenceImplication(exports.wff, 0, thms.bi1); //TODO

  startWith(thms.defbi1);
  applyArrow([1], thms.andr, 0);
  thms.bi2 = save();

//  scheme.setEquivalenceImplication(exports.wff, 1, thms.bi2);


  startWith(thms.defbi1);
  applyArrow([1,1], thms.imim1, 0);
  applyArrow([1,0], thms.imim1, 0);
  applyArrow([1], thms.defbi2, 0);
  thms.imbi1 = save();

//  scheme.setEquivalenceThm(exports.rarr, 0, thms.imbi1);

  startWith(thms.defbi1);
  applyArrow([1,0], thms.imim2, 0);
  applyArrow([1,1], thms.imim2, 0);
  applyArrow([1], thms.defbi2, 0);
  thms.imbi2 = save();
//  scheme.setEquivalenceThm(exports.rarr, 1, thms.imbi2);

//  scheme.setBinding(harr, 0, scheme.EXACT());
//  scheme.setBinding(harr, 1, scheme.EXACT());

  startWith(thms.defbi1);
  applyArrow([1,0], thms.imim1, 0);
  applyArrow([1,1], thms.imim2, 0);
  applyArrow([1], thms.prth, 0);
  applyArrow([1,0], thms.defbi1, 1);
  applyArrow([1,1], thms.defbi2, 0);
  applyArrow([], thms.ancr, 0);
  applyArrow([1,0], thms.defbi1, 0);
  applyArrow([1,0,0], thms.imim2, 0);
  applyArrow([1,0,1], thms.imim1, 0);
  applyArrow([1,0], thms.prth, 0);
  applyArrow([1,0,0], thms.ancom, 1);
  applyArrow([1,0,1], thms.ancom, 0);
  applyArrow([1,0,0], thms.defbi1, 1);
  applyArrow([1,0,1], thms.defbi2, 0);
  applyArrow([1], thms.defbi2, 0);
  thms.bibi1 = save();
//  scheme.setEquivalenceThm(exports.harr, 0, thms.bibi1);

  startWith(thms.defbi1);
  applyArrow([1,0], thms.imim2, 0);
  applyArrow([1,1], thms.imim1, 0);
  applyArrow([1], thms.prth, 0);
  applyArrow([1,0], thms.defbi1, 1);
  applyArrow([1,1], thms.defbi2, 0);
  applyArrow([], thms.ancr, 0);
  applyArrow([1,0], thms.defbi1, 0);
  applyArrow([1,0,0], thms.imim1, 0);
  applyArrow([1,0,1], thms.imim2, 0);
  applyArrow([1,0], thms.prth, 0);
  applyArrow([1,0,0], thms.ancom, 1);
  applyArrow([1,0,1], thms.ancom, 0);
  applyArrow([1,0,0], thms.defbi1, 1);
  applyArrow([1,0,1], thms.defbi2, 0);
  applyArrow([1], thms.ancom, 0);
  applyArrow([1], thms.defbi2, 0);
  thms.bibi2 = save();
//  scheme.setEquivalenceThm(exports.harr, 1, thms.bibi2);

  startWith(thms.mp);
  applyArrow([1,0], thms.bi1, 1);
  thms.mpbi = save();

  startWith(thms.mp);
  applyArrow([1,0], thms.bi2, 1);
  thms.mpbir = save();
  startWith(thms.defbi1);


  applyArrow([1,0], thms.anim1, 0);
  applyArrow([1,1], thms.anim1, 0);
  applyArrow([1], thms.defbi2, 0);
  thms.anbi1 = save();
//  scheme.setEquivalenceThm(exports.and, 0, thms.anbi1);

  startWith(thms.defbi1);
  applyArrow([1,0], thms.anim2, 0);
  applyArrow([1,1], thms.anim2, 0);
  applyArrow([1], thms.defbi2, 0);
  thms.anbi2 = save();
//  scheme.setEquivalenceThm(exports.and, 1, thms.anbi2);

  startWith(thms.defbi1);
  applyArrow([1,0], thms.con3, 0);
  applyArrow([1,1], thms.con3, 0);
  applyArrow([1], thms.defbi2, 0);
  thms.notbi = save();
//  scheme.setEquivalenceThm(exports.not, 0, thms.notbi);

  // Level 5

  startWith(thms.bi1);
  applyArrow([], thms.ancr, 0);
  applyArrow([1,0], thms.bi2, 0);
  applyArrow([1], thms.defbi2, 0);
  applyArrow([], thms.conj, 0);
  applyArrow([1], thms.defbi2, 0);
  applyArrow([0,1], thms.defbi2, 1);
  applyArrow([0,1,1], thms.bi1, 1);
  applyArrow([0,1], thms.ancom, 1);
  applyArrow([0], thms.ancr, 1);
  applyArrow([0,1], thms.bi2, 1);
  applyArrow([], thms.idie, 0);
  thms.bicom = save();

  startWith(thms.dfbi);
  applyArrow([], thms.defbi2, 0);
  thms.biid = save();

  startWith(thms.nn1);
  applyArrow([], thms.conj, 0);
  applyArrow([1], thms.defbi2, 0);
  applyArrow([0,1], thms.nn2, 1);
  applyArrow([], thms.idie, 0);
  applyArrow([], thms.bicom, 1);
  thms.nnbi = save();

  startWith(thms.Transpose);
  applyArrow([], thms.conj, 0);
  applyArrow([1], thms.ancom, 0);
  applyArrow([1], thms.defbi2, 0);
  applyArrow([0,1], thms.con3, 1);
  applyArrow([], thms.idie, 0);
  thms.con3bi = save();

  startWith(thms.and1);
  applyArrow([], thms.conj, 0);
  applyArrow([1], thms.defbi2, 0);
  applyArrow([0,1], thms.and2, 1);
  applyArrow([], thms.idie, 0);
  thms.dfanbi = save();

  startWith(thms.ancom);
  applyArrow([], thms.conj, 0);
  applyArrow([1], thms.defbi2, 0);
  applyArrow([0,0], thms.ancom, 0);
  applyArrow([], thms.idie, 0);
  thms.ancombi = save();

  startWith(thms.anid);
  applyArrow([], thms.conj, 0);
  applyArrow([1], thms.defbi2, 0);
  applyArrow([0,0], thms.andr, 0);
  applyArrow([], thms.idie, 0);
  thms.anidbi = save();

  startWith(thms.con12);
  applyArrow([], thms.conj, 0);
  applyArrow([1], thms.defbi2, 0);
  applyArrow([0,1], thms.con12, 1);
  applyArrow([], thms.idie, 0);
  thms.con12bi = save();


  startWith(thms.dfanbi);
  applyArrow([1,0,1,0], thms.dfanbi, 0);
  applyArrow([1,0,1], thms.nnbi, 1);
  applyArrow([1,0], thms.con12bi, 0);
  applyArrow([1,0,1], thms.nnbi, 0);
  applyArrow([1], thms.dfanbi, 1);
  applyArrow([1,1], thms.dfanbi, 1);
  applyArrow([0], thms.ancombi, 0);
  applyArrow([1,1], thms.ancombi, 0);
  thms.anass = save();

startNextGoal();
state.work = applyFact(state.work, [], thms.idie, [2]);
state.work = specifyDummy(state.work, [1,1], "&rarr;", 2);
state.work = applyFact(state.work, [1,1,1], thms.conj, [1]);
state.work = applyFact(state.work, [1,1], thms.imim2, [2]);
state.work = applyFact(state.work, [2], thms.defbi2, [2]);
state.work = applyFact(state.work, [], thms.conj, [2]);
state.work = ground(state.work, thms.imprt);
thms.impexp = saveGoal();


  // startWith(thms.imprt);
  // applyArrow([], thms.conj, 0);
  // applyArrow([1], thms.defbi2, 0);
  // applyArrow([0,0], thms.imim2, 0);
  // applyArrow([0,0,0], thms.conj, 1);
  // applyArrow([], thms.idie, 0);
  // thms.impexp = save();

  startWith(thms.defbi1);
  applyArrow([], thms.conj, 0);
  applyArrow([1], thms.defbi2, 0);
  applyArrow([0,1], thms.defbi2, 1);
  applyArrow([], thms.idie, 0);
  thms.dfbi3 = save();

startWith(thms.bibi1)
applyArrow([1,0], thms.bicom, 0);
save();


var landOr = getLand("land_or.js");

  // Level 6

startNextGoal();
state.work = ground(state.work, thms.biid);
thms.df_or = saveGoal();

  // startWith(thms.biid);
  // proofState = proofState.specify([1], exports.rarr);
  // proofState = proofState.specify([1,0], exports.not);
  // thms.df_or = defthm('&or;');


startWith(thms.df_or);  applyArrow([],thms.bicom,0);
  applyArrow([], thms.bi2, 0);
  applyArrow([0], thms.Simplify, 1);
  thms.or2 = save();
  // GHT.Thms['or2'] = T(O("->"),TV("wff -53792),T(O("or"),TV("wff -53793),TV("wff -53792)));

  startWith(thms.df_or);  applyArrow([],thms.bicom,0);
  applyArrow([], thms.bi2, 0);
  applyArrow([0], thms.con3bi, 0);
  applyArrow([0], thms.Simplify, 1);
  applyArrow([0], thms.nnbi, 1);
  thms.or1 = save();

  startWith(thms.imim2);
  applyArrow([1,0], thms.con3bi, 1);
applyArrow([1,0], thms.df_or, 0);
  applyArrow([1,1], thms.con3bi, 0);
  applyArrow([1,1,1], thms.nnbi, 1);
applyArrow([1,1], thms.df_or, 0);
  applyArrow([0,0], thms.nnbi, 1);
  thms.orim1 = save();

  startWith(thms.imbi1);
  applyArrow([1,0], thms.df_or, 0);
  applyArrow([1,1], thms.df_or, 0);
  applyArrow([0], thms.notbi, 1);
  thms.orbi1 = save();
//  scheme.setEquivalenceThm(theory.operator("or"), 0, thms.orbi1);
//  scheme.setBinding(theory.operator("or"), 0, scheme.LEFT(), thms.orim1);

  startWith(thms.imim2);
  applyArrow([1,0], thms.df_or, 0);
  applyArrow([1,1], thms.df_or, 0);
  thms.orim2 = save();

  startWith(thms.imbi1);
  applyArrow([1,0], thms.con3bi, 1);
  applyArrow([1,1], thms.con3bi, 1);
  applyArrow([1,0], thms.df_or, 0);
  applyArrow([1,1], thms.df_or, 0);
  applyArrow([0], thms.notbi, 1);
  thms.orbi2 = save();
//  scheme.setEquivalenceThm(theory.operator("or"), 1, thms.orbi2);
//  scheme.setBinding(theory.operator("or"), 1, scheme.LEFT(), thms.orim2);


  startWith(thms.con3bi);
  applyArrow([1], thms.df_or, 0);
  applyArrow([0], thms.df_or, 0);
  applyArrow([1,1], thms.nnbi, 1);
  thms.orcom = save();


var landForall = getLand("land_forall.js");

thms.axalim='rarr_forall_z_rarr_A_B_rarr_forall_z_A_forall_z_B';
startWith(thms.bi1);
generify();
applyArrow([], thms.axalim, 0);
applyArrow([1], thms.axalim, 0);
var tmp = save();
startWith(thms.bi2);
generify();
applyArrow([], thms.axalim, 0);
applyArrow([1], thms.axalim, 0);
applyArrow([1], 'rarr_A_rarr_B_and_A_B', 0);
applyArrow([1,1], 'rarr_and_rarr_A_B_rarr_B_A_harr_A_B', 0);
applyArrow([1,0], tmp, 1);
applyArrow([], 'rarr_rarr_A_rarr_A_B_rarr_A_B', 0);
applyArrow([1], 'harr_harr_A_B_harr_B_A', 0);
thms["19.15"] = save();  // (-> (A. x (<-> ph ps)) (<-> (A. x ph) (A. x ps)))

  /*
  // ==== END import from orcat_test.js ====
  */


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
DEBUG=true
ifaceCtx.inferTerms();
proofCtx.inferTerms();
Async.parallel(
    {iface:ifaceCtx.toString, proof:proofCtx.toString},
    function(err, results) {
        UrlCtx.files["tmp2.ghi"] = results.iface;
        UrlCtx.files["tmp2.gh"] = results.proof;
        if (DEBUG) {
            console.log("==== IFACE ====\n" + results.iface);
            console.log("==== PROOF ====\n" + results.proof);
        }
        try {
            run(UrlCtx, "tmp2.gh", verifyCtx);
        } catch (e) {
            console.log(e.toString());
            throw(new Error(e));
        }
    });

/*
  ==== Things to be proved ====

[],[rarr,[forall,z,[harr,A,B]],[rarr,[forall,z,A],[forall,z,B]]],[]
[],[rarr,[forall,z,[harr,A,B]],[harr,[forall,z,A],[forall,z,B]]],[]
[],[rarr,[forall,z,[harr,A,B]],[harr,[forall,z,B],[forall,z,A]]],[]
[],[rarr,[not,[forall,z,[not,[equals,a,b]]]],[not,[forall,z,[not,[equals,b,b]]]]],[]
[],[equals,a,a],[]
[],[exist,z,[equals,z,a]],[[a,z]]
[],[rarr,[equals,a,b],[rarr,[equals,a,c],[equals,c,b]]],[]
[],[rarr,[equals,a,b],[equals,b,a]],[]
[],[harr,[equals,a,b],[equals,b,a]],[]
[],[rarr,[and,[forall,z,A],[exist,z,B]],[exist,z,[and,A,B]]],[]
[],[rarr,[forall,z,[and,A,B]],[forall,z,A]],[]
[],[rarr,[forall,z,[and,A,B]],[and,[forall,z,A],[forall,z,B]]],[]
[],[harr,[forall,z,[and,A,B]],[and,[forall,z,A],[forall,z,B]]],[]
[],[rarr,[and,[forall,z,[forall,y,[rarr,[equals,z,y],[rarr,A,B]]]],[forall,z,A]],[forall,z,[forall,y,[rarr,[equals,z,y],B]]]],[[A,y]]
[],[rarr,[exist,z,A],A],[[A,z]]
[],[rarr,[exist,z,A],A],[[A,z]]
[],[rarr,A,[exist,z,A]],[]
[],[harr,[harr,A,B],[harr,[not,B],[not,A]]],[]
[],[harr,[forall,z,[not,A]],[not,[exist,z,A]]],[]
[],[rarr,[forall,z,A],[exist,z,A]],[]
[],[harr,[forall,z,[forall,y,A]],[forall,y,[forall,z,A]]],[]
[],[rarr,[forall,z,[rarr,A,B]],[rarr,[exist,z,A],[exist,z,B]]],[]
[],[rarr,[forall,z,[harr,A,B]],[harr,[forall,z,[not,B]],[forall,z,[not,A]]]],[]
[],[rarr,[forall,z,[harr,A,B]],[harr,[exist,z,A],[exist,z,B]]],[]
[],[rarr,[forall,z,[forall,y,[rarr,[equals,z,y],[rarr,A,B]]]],[rarr,[forall,z,A],[forall,z,B]]],[[A,y],[B,y]]
[],[rarr,[exist,z,A],A],[[A,z]]
[],[rarr,[forall,z,[forall,y,[rarr,[equals,z,y],[rarr,A,B]]]],[rarr,[forall,z,A],[forall,y,B]]],[[A,y],[B,z]]

[],[rarr,[rarr,A,B],[rarr,[rarr,B,A],[harr,A,B]]],[]
[],[harr,[and,[rarr,A,B],[rarr,A,C]],[rarr,A,[and,B,C]]],[]

[],[rarr,[forall,z,[forall,y,[rarr,[equals,z,y],[harr,A,B]]]],[harr,[forall,z,A],[forall,y,B]]],[[A,y],[B,z]]
[],[rarr,[equals,a,b],[equals,[plus,c,a],[plus,c,b]]],[]
[],[forall,z,[rarr,[equals,z,a],[equals,[plus,[Oslash],z],[plus,[Oslash],a]]]],[]
[],[rarr,[forall,z,[forall,y,[rarr,[equals,z,y],[harr,A,B]]]],[harr,[exist,y,A],[exist,z,B]]],[[A,z],[B,y]]
[],[rarr,[equals,a,b],[harr,[equals,a,c],[equals,b,c]]],[]
[],[rarr,[forall,z,[forall,y,[rarr,[equals,z,y],[harr,A,B]]]],[harr,[exist,z,A],[exist,y,B]]],[[A,y],[B,z]]
[],[rarr,[equals,a,b],[harr,[equals,a,c],[equals,b,c]]],[]
[],[rarr,[equals,a,b],[harr,[equals,c,a],[equals,c,b]]],[]
[],[harr,[exist,z,[equals,[plus,a,z],b]],[exist,y,[equals,[plus,a,y],b]]],[[a,y],[a,z],[b,y],[b,z]]
[],[harr,[exist,z,[equals,[plus,a,z],b]],[exist,y,[equals,[plus,a,y],b]]],[[a,y],[a,z],[b,y],[b,z]]
[],[rarr,[rarr,[equals,a,[Oslash]],[equals,[plus,[Oslash],[Oslash]],a]],[rarr,[equals,a,[Oslash]],[equals,[plus,[Oslash],a],a]]],[]
[],[rarr,[equals,[plus,[Oslash],[Oslash]],[Oslash]],[rarr,[equals,a,[Oslash]],[equals,[plus,[Oslash],a],a]]],[]
[],[rarr,[forall,z,[rarr,[forall,y,[rarr,[equals,y,z],[equals,[plus,[Oslash],y],y]]],[forall,y,[rarr,[equals,y,[sect,z]],[equals,[plus,[Oslash],y],y]]]]],[forall,y,[equals,[plus,[Oslash],y],y]]],[]
[],[rarr,[equals,[plus,[Oslash],[sect,a]],b],[rarr,[equals,c,[sect,a]],[equals,[plus,[Oslash],c],b]]],[]
[rarr,[equals,a,b],[harr,[equals,[plus,[Oslash],a],a],[equals,[plus,[Oslash],b],b]]],[],[]
[rarr,[equals,a,[sect,[plus,[Oslash],b]]],[rarr,[equals,[plus,[Oslash],b],b],[equals,a,[sect,b]]]],[],[]
[rarr,[equals,[plus,[Oslash],a],a],[equals,[plus,[Oslash],[sect,a]],[sect,a]]],[],[]
[rarr,[equals,[plus,[Oslash],a],a],[rarr,[equals,a,b],[equals,[plus,[Oslash],b],b]]],[],[]
[rarr,[equals,[plus,[Oslash],a],a],[forall,z,[rarr,[equals,z,[sect,a]],[equals,[plus,[Oslash],z],z]]]],[[a,z]],[]
[rarr,[rarr,[equals,a,a],A],A],[],[]
[rarr,[exist,z,A],[rarr,[forall,z,[rarr,A,B]],[exist,z,B]]],[],[]
[harr,[exist,z,[equals,[plus,[Oslash],z],z]],[exist,y,[equals,[plus,[Oslash],y],y]]],[],[]
[equals,[plus,[Oslash],z],z],[],[]
[le,a,a],[],[]
[equals,a,a],[],[]
[rarr,[rarr,[exist,z,[equals,z,a]],A],A],[[a,z]],[]
[rarr,[forall,z,[rarr,[equals,z,a],A]],[exist,z,[and,[equals,z,a],A]]],[[a,z]],[]
[rarr,[forall,z,[forall,y,[rarr,[equals,y,[Oslash]],[harr,A,B]]]],[rarr,[forall,z,[forall,y,[rarr,[equals,y,z],[harr,A,C]]]],[rarr,[forall,z,[forall,y,[rarr,[equals,y,[sect,z]],[harr,A,D]]]],[rarr,[forall,z,[forall,y,[rarr,[equals,y,a],[harr,A,E]]]],[rarr,B,[rarr,[forall,z,[rarr,C,D]],E]]]]]],[[A,z],[B,y],[C,y],[D,y],[E,y],[a,y]],[]
[rarr,[and,[harr,A,B],[harr,A,C]],[harr,B,C]],[],[]
[rarr,[and,[equals,a,b],[equals,c,d]],[harr,[equals,a,c],[equals,b,d]]],[],[]
[rarr,[rarr,[forall,z,[forall,y,[rarr,[equals,a,b],[harr,[equals,[plus,[plus,c,d],a],[plus,c,[plus,d,a]]],[equals,[plus,[plus,c,d],b],[plus,c,[plus,d,b]]]]]]],A],A],[],[]
[],[rarr,[rarr,[forall,z,[rarr,A,A]],B],B],[]
[],[equals,[plus,[plus,a,b],c],[plus,a,[plus,b,c]]],[]

*/
