var Fs = require('fs');
var Bencode = require('bencode');
var Crypto = require('crypto');
var Fact = require('../../caghni/js/fact.js'); //XXX

var lands = [];
var state = {};

var TODO_PUSHUPMAP = {};

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
        fact.toGhilbert(state, appendTo(interfaceText));
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
    work.setCmd("thm");
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

// Returns a list of mandatory hypotheses (i.e., values for each var) of the
// fact, such that the named subexpression of the fact's stmt matches the named
// subexpression of the work's first hyp.
// @param TODO
// @return a list of terms (in the work's variables). dummy variables will get
//     no assignment.
// @throws an error if the unification is impossible or would violate a Free
//     constraint.
function getMandHyps(work, hypPath, fact, stmtPath) {
    var debugPath = [];
    // from fact vars to work exps
    var varMap = {};
    var workExp = zpath(work.Core[Fact.CORE_HYPS][0], hypPath);
    var factExp = zpath(fact.Core[Fact.CORE_STMT], stmtPath);
    if ((workExp == undefined) || (factExp == undefined)) {
        throw new Error("Undefined!\n" + JSON.stringify(work) + "\n" +
                        JSON.stringify(hypPath) + "\n" +
                        JSON.stringify(fact) + 
                        JSON.stringify(stmtPath));
    }
    var nonDummy = {};
    var dummyMap = {};
    eachVarOnce(work.Core[Fact.CORE_STMT], function(v) {
        nonDummy[v] = v;
    });
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

        if (!Array.isArray(factSubExp)) {
            if (alreadyMapped) {
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
        console.log("#XXXX Work now: " + JSON.stringify(work));
        
        for (var v in dummyMap) if (dummyMap.hasOwnProperty(v)) {
            console.log("#XXXX Dummy:" + v + "=> " + JSON.stringify(dummyMap[v]));
            
        }
    }
    work.Core[Fact.CORE_STMT] = replaceDummies(work.Core[Fact.CORE_STMT])
    work.Core[Fact.CORE_HYPS] = work.Core[Fact.CORE_HYPS].map(replaceDummies);
    work.Tree.Proof = work.Tree.Proof.map(replaceDummies);
     // TODO: undummy freemap
    if (DEBUG) {
        console.log("#XXXX Work undummied: " + JSON.stringify(work));
    }

    //console.log("Unified: " + JSON.stringify(varMap));
    for (x in varMap) if (varMap.hasOwnProperty(x)) {
        varMap[x] = replaceDummies(varMap[x]);
    }
    return varMap;
}


function queryPushUp(params) {
    // TODO
    var pushup = TODO_PUSHUPMAP[params];
    if (!pushup) {
        throw new Error("No pushup found for " + JSON.stringify(params));
    }
    return pushup
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
function apply(work, workPath, fact, factPath) {
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
        var goalTerm = work.Skin.TermNames[zpath(pusp.goal, pusp.goalPath)[0]];
        pusp.goalPath.push(goalArgNum);
        var toolArgNum = pusp.toolPath.pop();
        var toolTerm = work.Skin.TermNames[zpath(pusp.tool, pusp.toolPath)[0]];
        pusp.toolPath.push(toolArgNum);

        var query = [goalTerm, goalArgNum, toolTerm,
                     pusp.toolPath[pusp.toolPath.length - 1]];
        var pushUp = queryPushUp(query);
        pushUp.pushUp(pusp, work);

    }
    checkInvariant();

    // Now, since the invariant holds and goalPath = [], tool[2] == goal, so 
    // just detach.
    pusp.newSteps.push(nameDep(work, axmp)); // TODO: XXX ???

    // #. compute new preimage and update Hyps.0
    // TODO: hardcoded for now
    work.Core[Fact.CORE_HYPS][0] = pusp.tool[1];
    
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

// TODO: should be generated
var interfaceText = {txt:'kind (kind0)\n' +
    'tvar (kind0 V0 V1 V2 V3 V4)\n' +
                     'term (kind0 (&rarr; V0 V1))\n\n'};

var outstanding = 0;
function appendTo(strptr) {
    outstanding++;
    return function(err, txt) {
        if (err) throw new Error(err);
        strptr.txt += txt;
        outstanding--;
    }
}

var landRarr = getLand("land_rarr.js");
var ax1 = state.factsByMark[
    "[[],[0,0,[0,1,0]],[]];[\"&rarr;\"]"];
var imim1 = state.factsByMark[
    "[[],[0,[0,0,1],[0,[0,1,2],[0,0,2]]],[]];[\"&rarr;\"]"];
var imim2 = state.factsByMark[
    "[[],[0,[0,0,1],[0,[0,2,0],[0,2,1]]],[]];[\"&rarr;\"]"];
var pm243 = state.factsByMark[
    "[[],[0,[0,0,[0,0,1]],[0,0,1]],[]];[\"&rarr;\"]"];
var axmp = state.factsByMark[
    "[[1,[0,1,0]],0,[]];[\"&rarr;\"]"];

TODO_PUSHUPMAP[[["&rarr;",2],["&rarr;",2]]] = {
    fact:imim2,
    pushUp: function(pusp, work) {
        pusp.newSteps.push(pusp.tool[1]);
        pusp.newSteps.push(pusp.tool[2]);
        pusp.goalPath.pop();
        var thirdArg = zpath(pusp.goal, pusp.goalPath)[1];
        pusp.newSteps.push(thirdArg);
        pusp.newSteps.push(nameDep(work, this.fact));
        pusp.newSteps.push(nameDep(work, axmp));
        var rarr = work.nameTerm("&rarr;");
        pusp.tool = [rarr,
                     [rarr, thirdArg, pusp.tool[1]],
                     [rarr, thirdArg, pusp.tool[2]]];
        pusp.toolPath = [2];
    }
};
TODO_PUSHUPMAP[[["&rarr;",1],["&rarr;",1]]] = {
    fact:imim1,
    pushUp: function(pusp, work) {
        // Goal: -> A B
        // Tool: -> A C
        // new goal: -> C B 
        // imim1: (-> (-> A C) (-> (-> C B) (-> A B))
        pusp.newSteps.push(pusp.tool[1]);
        pusp.newSteps.push(pusp.tool[2]);
        pusp.goalPath.pop();
        var thirdArg = zpath(pusp.goal, pusp.goalPath)[2];
        pusp.newSteps.push(thirdArg);
        pusp.newSteps.push(nameDep(work, this.fact));
        pusp.newSteps.push(nameDep(work, axmp));
        var rarr = work.nameTerm("&rarr;");
        pusp.tool = [rarr,
                     [rarr, pusp.tool[2], thirdArg],
                     [rarr, pusp.tool[1], thirdArg]];
        pusp.toolPath = [2];
    }
};
TODO_PUSHUPMAP[[["&rarr;",1],["&rarr;",2]]] = {
    fact:imim1,
    pushUp: function(pusp, work) {
        // Goal: -> A B
        // Tool: -> C A
        // new goal: -> C B 
        // imim1: (-> (-> C A) (-> (-> A B) (-> C B))
        pusp.newSteps.push(pusp.tool[1]);
        pusp.newSteps.push(pusp.tool[2]);
        pusp.goalPath.pop();
        var thirdArg = zpath(pusp.goal, pusp.goalPath)[2];
        pusp.newSteps.push(thirdArg);
        pusp.newSteps.push(nameDep(work, this.fact));
        pusp.newSteps.push(nameDep(work, axmp));
        var rarr = work.nameTerm("&rarr;");
        pusp.tool = [rarr,
                     [rarr, pusp.tool[2], thirdArg],
                     [rarr, pusp.tool[1], thirdArg]];
        pusp.toolPath = [1];
    }
};
TODO_PUSHUPMAP[[["&rarr;",2],["&rarr;",1]]] = {
    fact:imim2,
    pushUp: function(pusp, work) {
        // Goal: -> A B
        // Tool: -> B C
        // new goal: -> A C 
        // imim2: (-> (-> B C) (-> (-> A B) (-> A C))
        pusp.newSteps.push(pusp.tool[1]);
        pusp.newSteps.push(pusp.tool[2]);
        pusp.goalPath.pop();
        var thirdArg = zpath(pusp.goal, pusp.goalPath)[1];
        pusp.newSteps.push(thirdArg);
        pusp.newSteps.push(nameDep(work, this.fact));
        pusp.newSteps.push(nameDep(work, axmp));
        var rarr = work.nameTerm("&rarr;");
        pusp.tool = [rarr,
                     [rarr, thirdArg, pusp.tool[1]],
                     [rarr, thirdArg, pusp.tool[2]]];
        pusp.toolPath = [1];
    }
};

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

// Reorders variables so that they appear in first-used order.
// Removes no-longer-used dummies.
// Renames remaining variable Skins to Vn
// TODO: doesn't handle freemap, currently
// TODO: reorder termnames
// TODO: sort deps alphabetically?
function canonicalize(work) {
    var out = new Fact();
    var terms = work.Skin.TermNames;
    if (work.Core[Fact.CORE_FREE] && work.Core[Fact.CORE_FREE].length > 0) {
        throw new Error("TODO");
    }
    function mapExp(exp) {
        if (Array.isArray(exp) && (exp.length > 0)) {
            var mapped = exp.slice(1).map(mapExp);
            mapped.unshift(out.nameTerm(terms[exp[0]]));
            return mapped;
        } else if (typeof exp == 'number') {
            return out.nameVar("V" + exp);
        } else {
            return exp;
        }
    }
    out.setStmt(mapExp(work.Core[Fact.CORE_STMT]));
    out.setFree([]); // XXX
    for (var i = 0; i < work.Core[Fact.CORE_HYPS].length; i++) {
        out.Core[Fact.CORE_HYPS][i] = mapExp(work.Core[Fact.CORE_HYPS][i]);
        out.Skin.HypNames[i] = "Hyps." + i;
    }
    out.setProof(work.Tree.Proof.map(mapExp));
    out.setCmd(work.Tree.Cmd);
    out.setName(fingerprint(out.getMark()));
    out.Tree.Deps = work.Tree.Deps.map(function(d) {
        var e = d[1].map(function(t) {
            return out.nameTerm(work.Skin.TermNames[t]);
        });
        return [clone(d[0]), e];
    });

    
    for (var n = 0; n < out.Skin.VarNames.length; n++) {
        out.Skin.VarNames[n] = "V" + n;
    }
    if (DEBUG) {
        console.log("work=" + JSON.stringify(work) +
                    "\nfact=" +JSON.stringify(out));
    }
    return out;
}




var ghilbertText = {txt:'import (TMP tmp2.ghi () "")\n' +
    'tvar (kind0 V0 V1 V2 V3 V4 V5)\n\n'};
state.work = startWork(state.land.goals[state.goal]);
// |- (PQR)(PQ)PR => |- (PQR)(PQ)PR
state.work = apply(state.work, [2,2], pm243, [2]);
// |- (PQR)(PQ)PPR => |- (PQR)(PQ)PR
state.work = apply(state.work, [2,1], imim1, [1]);
// |- (P(QR))((Qr)(Pr))(P(PR)) => |- (PQR)(PQ)PR
state.work = ground(state.work, imim1);
// |- (PQR)(PQ)PR
state.land.addFact(state.work);
state.goal++;
var ax2 = state.work;
state.work.toGhilbert(state, appendTo(ghilbertText));

// Apparatus for importing proofs from orcat_test.js
var thms = {};
thms.imim1 = imim1;
thms.imim2 = imim2;
thms.Distribute = ax2;
thms.Simplify = ax1;

var stack = []; // goalPath, fact, factPath
function startWith(fact) {
    stack = [[fact]];
}
function applyArrow(path, fact, side) {
    stack.unshift([path.map(function(x){return x+1;}), fact, [2 - side]]);
}
function save() {
    state.work = startWork(state.land.goals[state.goal]);
    stack.forEach(function(step) {
        if (DEBUG) {console.log("# XXXX Work now: " + JSON.stringify(state.work));}
        try {
            if (step.length > 1) {
                state.work = apply(state.work, step[0], step[1], step[2]);
            } else {
                state.work = ground(state.work, step[0]);
            }
        } catch (e) {
            console.log("Error in step " + JSON.stringify(step));
            throw(e);
        }

    });
    if (DEBUG) {console.log("# XXXX Work now: " + JSON.stringify(state.work));}
    state.land.addFact(state.work);
    state.goal++;
    state.work.toGhilbert(state, appendTo(ghilbertText));
    startWith(state.work);
    return state.work;
}

// %%% BEGIN import from orcat_test.js
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

// Level 2

interfaceText.txt += '\nterm (kind0 (&not; V0))\n'; //TODO: should be auto
var landNot = getLand("land_not.js");

thms.Transpose = state.factsByMark[
    "[[],[1,[1,[0,0],[0,1]],[1,1,0]],[]];[\"&not;\",\"&rarr;\"]"];

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



/*
// %%% END import from orcat_test.js
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

while (outstanding > 0) {
    throw "yield";
}
UrlCtx.files["tmp2.ghi"] = interfaceText.txt;
UrlCtx.files["tmp2.gh"] = ghilbertText.txt;

if (DEBUG) {
    console.log("==== IFACE ====\n" + interfaceText.txt);
    console.log("==== PROOF ====\n" + ghilbertText.txt);
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
if (DEBUG) {
    console.log("#### AXIOMS");
    console.log(UrlCtx.files["tmp2.ghi"]);
    console.log("#### PROOFS");
    console.log(UrlCtx.files["tmp2.gh"]);
}

try {
    run(UrlCtx, "tmp2.gh", verifyCtx);
} catch (e) {
    console.log(e.toString());
    throw(new Error(e));
}

