var Fs = require('fs');
var Bencode = require('bencode');
var Crypto = require('crypto');
var Fact = require('../../caghni/js/fact.js'); //XXX

var lands = [];
var state = {};

var TODO_PUSHUPMAP = {};

var DEBUG = false;

function getLand(filename) {
    // Uses eval instead of json to allow comments and naked keys.
    // This is almost certainly a terrible idea.
    var land = eval("("+Fs.readFileSync(filename,'utf8')+")");
    land.facts = [];
    land.factsByMark = {};
    land.addFact = function(f){
        var fact = Fact(f);
        if (!fact.Skin) {
            fact.Skin = {};
        }
        if (!fact.Skin.Name) {
            fact.Skin.Name = fingerprint(fact.getMark());
        }
        land.factsByMark[fact.getMark()] = fact;
    }
    land.axioms.forEach(land.addFact);
    land.inferences.forEach(land.addFact);
    land.getFact = function(mark) {
        return land.factsByMark[mark];
    }

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
    return Fact(fact).getMark();
}

function nameDep(workFact, depFact) {
    return workFact.nameDep(fingerprint(depFact.getMark()), depFact);
}

function startWork(fact) {
    var work = clone(fact);
    work.Bone.Hyps = [clone(work.Bone.Stmt)];
    work.Bone.Free = [];
    work.Skin = {
        HypNames: ["Hyps.0"],
        DepNames: [],
        V: [],
        T: [],
    };
    function nameVar(varStr) {
        var p = parseVarString(varStr);
        if (p.cmd != 'T' && p.cmd != 'V') {
            throw new Error("Bad var cmd " + varStr);
        }
        if (!work.Skin[p.cmd][p.kind]) {
            work.Skin[p.cmd][p.kind] = [];
        }
        work.Skin[p.cmd][p.kind][p.num] = varStr;
    }
    eachVarOnce(work.Bone.Stmt,nameVar);
    work.Tree = {
        Cmd: "thm",
        Proof: ["Hyps.0"],
        Terms: work.Meat.Terms, //XXX: dangerous?
        Kinds: work.Meat.Kinds,
        Deps: [],
    };
    return Fact(work);
}

// returns {cmd:T or V, kind:kindIndex, num:varNum]
function parseVarString(s) {
    var arr = s.substring(1).split('.');
    arr[0] = Number(arr[0]);
    arr[1] = Number(arr[1]);
    if (((s[0] != 'T') && (s[0] != 'V')) ||
        isNaN(arr[0]) ||
        isNaN(arr[1])) {
        throw new Error("Bad var string " + s);
    }
    return {cmd:s[0], kind:arr[0], num:arr[1]};
}

// NB: not the same as orcat's xpath definition. Pass 0 to get the term.
function zpath(exp, path) {
    var a = exp, l = path.length, i = 0;
    for (i = 0; i < l; i++) {
        a=a[path[i]];
    }
    return a;
}

function isString(s) {
    return (typeof s === "string") || (s instanceof String);
}

// Visits each var exactly once, in left-to-right depth-first order
function eachVarOnce(exp, cb, seen) {
    seen = seen || {};
    if (isString(exp)) {
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
    var workExp = zpath(work.Bone.Hyps[0], hypPath);
    var factExp = zpath(fact.Bone.Stmt, stmtPath);
    var nonDummy = {};
    var dummyMap = {};
    eachVarOnce(work.Bone.Stmt, function(v) {
        nonDummy[v] = v;
    });
    function assertEqual(msgTag, thing1, thing2) {
        if (thing1 !== thing2) {
            throw new Error("Unification error: " + msgTag + " @ " + debugPath +
                            "\nWork:  " + JSON.stringify(workExp) +
                            "\nFact:  " + JSON.stringify(factExp) +
                            "\nWant:  " + thing1 + " === " + thing2);
        }
    }
    function assertNotFree(exp, freeMap) {
        if (isString(exp)) {
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
        if (!fact.Bone.Free) {
            return undefined;
        }
        // TODO: could be faster.
        for (var i = 0; i < fact.Bone.Free.length; i++) {
            if (fact.Bone.Free[i][0] === factVarName) {
                var free = {};
                fact.Bone.Free[i].slice(1).forEach(function(v) {
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
        // TODO: check kind match and tvarness match
        varMap[factVarName] = workExp;
    }
    function recurse(workSubExp, factSubExp, alreadyMapped) {
        if (!alreadyMapped && isString(factSubExp) && varMap[factSubExp]) {
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

        if (isString(factSubExp)) {
            if (alreadyMapped) {
                if (!nonDummy[workSubExp]) {
                    if (factSubExp != workSubExp) { 
                        dummyMap[workSubExp] = factSubExp;
                    }
                } else if (!nonDummy[factSubExp]) {
                    if (factSubExp != workSubExp) { 
                        dummyMap[factSubExp] = workSubExp;;
                    }                
                } else {
                    assertEqual("mapped", factSubExp, workSubExp);
                }
            } else {
                mapVarTo(factSubExp, workSubExp);
            }
        } else {
            var factTerm = fact.Meat.Terms[factSubExp[0]];
            if (isString(workSubExp)) {
                // Work is var, Fact is exp. 
                if (nonDummy[workSubExp]) {
                    assertEqual("shrug", workSubExp, factSubExp); //XXX
                } else {
                    var newExp = [];
                    newExp.push(work.nameTerm(factTerm));
                    for (var i = 1; i < factSubExp.length; i++) {
                        newExp.push(work.nameVar(
                            "T",
                            work.Meat.Kinds[0], //XXX: Need Meat.Signs!
                            newDummy()));
                    }
                    dummyMap[workSubExp] = newExp;
                    workSubExp = newExp;
                }
            } 
            if (!isString(workSubExp)) {
                // exp - exp
                var term1 = work.Meat.Terms[workSubExp[0]];
                assertEqual("term", term1, factTerm);
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
        if (isString(x)) {
            while (dummyMap[x]) {
                x = dummyMap[x];
            }
            return isString(x) ? x : replaceDummies(x);
        } else if (!isNaN(x)) {
            return x;
        } else {
            for (var k in x) if (x.hasOwnProperty(k)) {
                x[k] = replaceDummies(x[k]);
            }
            return x;
        }
    }
    if (DEBUG) {
        console.log("#XXXX Work now: " + JSON.stringify(work));
        
        for (var v in dummyMap) if (dummyMap.hasOwnProperty(v)) {
            console.log("#XXXX Dummy:" + v + "=> " + JSON.stringify(dummyMap[v]));
            
        }
    }
    replaceDummies(work.Bone.Stmt);
    replaceDummies(work.Bone.Hyps);
    replaceDummies(work.Tree.Proof);
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
        if (!isNaN(x)) {
            return work.nameTerm(fact.Meat.Terms[x]);
        } else if (isString(x)) {
            if (!varMap[x]) {
                throw new Error("Unmapped var " + x);
            }
            return varMap[x];
        } else {
            return x.map(mapper);
        }
    }
    return mapper(fact.Bone.Stmt);
}
function apply(work, workPath, fact, factPath) {
    var varMap = getMandHyps(work, workPath, fact, factPath);
    if (DEBUG) {console.log("# MandHyps: " + JSON.stringify(varMap));}
    // If that didn't throw, we can start mutating
    // PushUpScratchPad
    var pusp = {};

    pusp.newSteps = [];
    
    eachVarOnce(fact.Bone.Stmt, function(v) {
        var newV = varMap[v];
        if (!newV) {
            var p = parseVarString(v);
            newV = work.nameVar(p.cmd,
                                //TODO: nameKind goes in tree not meat!!
                                fact.Meat.Kinds[p.kind],
                                newDummy()); // XXX HACK
            varMap[v] = newV;
        }
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
    pusp.goal = clone(work.Bone.Hyps[0]);      // what we want to prove
    pusp.goalPath = clone(workPath);           // path to subexp B
    // invariant: subexp A == subexp B
    function checkInvariant() {
        if (JSON.stringify(zpath(pusp.tool, pusp.toolPath)) !=
            JSON.stringify(zpath(pusp.goal, pusp.goalPath))) {
            throw new Error("Invariant broken!");
        }
/*
        console.log("Check invariant: \n" +
                    zpath(pusp.tool, pusp.toolPath) + "\n" + 
                    zpath(pusp.goal, pusp.goalPath));
        console.log("XXXX pusp: ", JSON.stringify(pusp));
*/
    }

    while (pusp.goalPath.length > 0) {
        checkInvariant();
        var goalArgNum = pusp.goalPath.pop();
        var goalTerm = work.Meat.Terms[zpath(pusp.goal, pusp.goalPath)[0]];
        pusp.goalPath.push(goalArgNum);
        var toolArgNum = pusp.toolPath.pop();
        var toolTerm = work.Meat.Terms[zpath(pusp.tool, pusp.toolPath)[0]];
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
    work.Bone.Hyps[0] = pusp.tool[1];
    
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

var rarr = getLand("land_rarr.js");
lands.push(rarr);
state.land = rarr;
state.goal = 0;
var ax1 = Fact(state.land.axioms[0]);   // PQP
var imim1 = Fact(state.land.axioms[1]); // (PQ)(QR)PR
var imim2 = Fact(state.land.axioms[2]); // (PQ)(RP)RQ
var pm243 = Fact(state.land.axioms[3]); // (PPQ)PQ
var axmp = Fact(state.land.inferences[0]);

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

function ground(work, dirtFact) {
    // verify that the hyp is an instance of the dirt
    var varMap = getMandHyps(work, [], dirtFact, []);
    if (DEBUG) {console.log("# ground MandHyps: " + JSON.stringify(varMap));}
    work.Bone.Hyps.shift();
    var newSteps = [];
    eachVarOnce(dirtFact.Bone.Stmt, function(v) {
        var newV = varMap[v];
        if (!newV) {
            var p = parseVarString(v);
            newV = work.nameVar(p.cmd,
                                //TODO: nameKind goes in tree not meat!!
                                dirtFact.Meat.Kinds[p.kind],
                                newDummy()); // XXX HACK
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
// Renames remaining variable Skins to Tx.y
// Reorders Deps so they appear in first-used order
// Trims from Meat.Kinds and Meat.Terms that which is not in Bone
// TODO: doesn't handle hyps or free, currently
function canonicalize(work) {
    var out = new Fact();
    function mapList(exp) {
        if (isString(exp)) {
            var dots = exp.split(".");
            if (dots[0] == "Deps") {
                var depNum = dots[1];
                // TODO: HACK
                var depWrap = {getMark: function() {
                    return work.Tree.Deps[depNum];}};
                return out.nameDep(work.Skin.DepNames[depNum],
                                   depWrap);
            }
            var p = parseVarString(exp);
            return out.nameVar(p.cmd,
                               work.Tree.Kinds[p.kind],
                               exp);
        } else if (!isNaN(exp)) {
            return out.nameTerm(work.Tree.Terms[exp]);
        } else {
            return exp.map(mapList);
        }
    }
    out.setCmd("thm");
    out.setStmt(mapList(work.Bone.Stmt));
    out.setFree([]); // XXX
    out.setProof(mapList(work.Tree.Proof));
    out.setName(fingerprint(out.getMark()));
    return out;
}


// TODO: should be generated
var ghilbertText = 'import (TMP tmp2.ghi () "")\n' +
    'tvar (kind0 T0.0 T0.1 T0.2 T0.3 T0.4 T0.5)\n\n' ;

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
if (DEBUG) {console.log("# XXXX Work now: " + JSON.stringify(state.work));}
ghilbertText += state.work.toGhilbert(state.land.getFact);


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
        if (step.length > 1) {
            state.work = apply(state.work, step[0], step[1], step[2]);
        } else {
            state.work = ground(state.work, step[0]);
        }
    });
    if (DEBUG) {console.log("# XXXX Work now: " + JSON.stringify(state.work));}
    state.land.addFact(state.work);
    state.goal++;
    ghilbertText += state.work.toGhilbert(state.land.getFact);
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
DEBUG=true
thms.id = save();
/*
startWith(thms.Distribute);
applyArrow([0], thms.idd, 1);
applyArrow([1,0], thms.Simplify, 1);
thms.mpd = save();

applyArrow([], thms.mpd, 0);
thms.mp = save();
startWith(thms.id);
applyArrow([], thms.mp, 0);
thms.idie = save();

startWith(thms.mp);
applyArrow([], thms.Distribute, 0);
thms.contract = save();
/*
// %%% END import from orcat_test.js
*/
console.log(ghilbertText);