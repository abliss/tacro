var Fs = require('fs');
var Bencode = require('bencode');
var Crypto = require('crypto');
var Fact = require('../../caghni/js/fact.js'); //XXX

var lands = [];
var state = {};

var TODO_PUSHUPMAP = {};

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
        //console.log("XXXX Recurse:\n  " + JSON.stringify(workSubExp) + "\n  " +
        //            JSON.stringify(factSubExp));
        if (!alreadyMapped && isString(factSubExp) && varMap[factSubExp]) {
            factSubExp = varMap[factSubExp];
            alreadyMapped = true;
        }
        if (isString(factSubExp)) {
            if (alreadyMapped) {
                assertEqual("mapped", factSubExp, workSubExp);
            } else {
                mapVarTo(factSubExp, workSubExp);
            }
        } else {
            if (isString(workSubExp)) {
                // Work is var, Fact is exp. Don't support now.
                assertEqual("shrug", workSubExp, factSubExp); //XXX
            } else {
                // exp - exp
                var term1 = work.Meat.Terms[workSubExp[0]];
                var term2 = fact.Meat.Terms[factSubExp[0]];
                assertEqual("term", term1, term2);
                assertEqual("arity", workExp.length, factExp.length);
                for (var i = 1; i < workExp.length; i++) {
                    debugPath.push(i);
                    recurse(workSubExp[i], factSubExp[i], alreadyMapped);
                    debugPath.pop();
                }
            }
        }
    }
    recurse(workExp, factExp, false);
    
    //console.log("Unified: " + JSON.stringify(varMap));
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
                                v);
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
    work.Bone.Hyps.shift();
    var newSteps = [];
    eachVarOnce(dirtFact.Bone.Stmt, function(v) {
        var newV = varMap[v];
        if (!newV) {
            var p = parseVarString(v);
            newV = work.nameVar(p.cmd,
                                //TODO: nameKind goes in tree not meat!!
                                dirtFact.Meat.Kinds[p.kind],
                                v);
            varMap[v] = newV;
        }
        newSteps.push(newV);
    });
    newSteps.push(nameDep(work, dirtFact));

    // remove hyp step
    work.Tree.Proof.shift(); 
    // Replace with proof of hyp instance
    work.Tree.Proof.unshift.apply(work.Tree.Proof, newSteps);
    return work;
}
state.work = startWork(state.land.goals[state.goal]);
// |- (PQR)(PQ)PR => |- (PQR)(PQ)PR
state.work = apply(state.work, [2,2], pm243, [2]);
console.log("XXXX Work now: " + JSON.stringify(state.work));
console.log("XXXX Ghilbert:\n" + state.work.toGhilbert(state.land.getFact));
// |- (PQR)(PQ)PPR => |- (PQR)(PQ)PR
state.work = apply(state.work, [2,1], imim1, [1]);
// |- (P(QR))((QR)(PR))(P(PR)) => |- (PQR)(PQ)PR
console.log("XXXX Work now: " + JSON.stringify(state.work));
console.log("XXXX Ghilbert:\n" + state.work.toGhilbert(state.land.getFact));
state.work = ground(state.work, imim1);
// |- (PQR)(PQ)PR
state.land.addFact(state.work);
state.goal++;
console.log("XXXX Work now: " + JSON.stringify(state.work));
console.log("XXXX Ghilbert:\n" + state.work.toGhilbert(state.land.getFact));
var ax2 = state.work;
throw new Error("finis");
state.work = startWork(state.land.goals[state.goal]);
// |- ((PQ)R)QR => |- ((PQ)R)QR
state.work = apply(state.work, [], imim1, [1]);
// |- QPQ => |- ((PQ)R)QR
state.work = ground(state.work, ax1);
var himp1 = state.work;
