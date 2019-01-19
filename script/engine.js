var Fact = require('./fact.js'); //XXX
//var Crypto = require('crypto');
// This engine assists in authoring proofs by working backwards from a target
// goal. The exported methods operate on a "workspace", i.e. a Fact whose
// statement is the target, and whose only hypothesis represents "what we must
// prove". To start, the hypothesis is simply the conclusion, and the proof is
// trivial. At each step, we work backwards from the hypothesis, adding to the
// beginning of the proof, while the conclusion remains the same. Eventually we
// hope to "ground" the workspace in a known Fact, leaving us with a completed
// zero-hypothesis theorem.
(function(module) {
    // Enable for logs
    var DEBUG = false;

    // An incrementing number to disambiguate dummy vars
    var dummyNum = 0;

    // A list of all facts registered through onAddFact.
    // TODO: index this in a smart way.
    var allKnownFacts = [];

    var nextTick;
    if (typeof process !== 'undefined' && process.nextTick) {
        nextTick = process.nextTick;
    } else if (typeof window !== 'undefined' && window.setTimeout) {
        nextTick = function(cb) {window.setTimeout(cb, 0);}
    } else {
        throw new Error("No nextTick");
    }

    // The engine keeps this "scheme", a list of facts registered through
    // onAddFact which could be used for our automated-proving purposes (as a
    // detach or a pushUp).
    var scheme = {
        pushUpHalfMemo: {}, // An index of pushUpMemo by the first two params
        pushUpMemo : {},
        detachMemo : {},
        greaseMemo : {},
        toolsSeen: {},
        halfQueryPushUp: function(goalOp, goalArgNum) {
            var r = this.pushUpHalfMemo[[goalOp, goalArgNum]];
            return r || {};
        },
        queryPushUp:  function(query) { // [goalOp, goalArgNum, toolOp, toolArgNum]
            var pushUp = this.pushUpMemo[query];
            if (!pushUp) {
                throw new Error("pushUp not found! Check commit d2a748c " +
                                "for how this used to work.");
            }
            if (DEBUG) console.log("queryPushUp: " + JSON.stringify(query) + " => " +  pushUp);
            return pushUp;
        },
        queryDetach: function(params) {
            if (DEBUG) console.log("queryDetach: " + JSON.stringify(arguments));
            var detach = this.detachMemo[params];
            if (!detach) {
                throw new Error("No detach found for " +
                                JSON.stringify(params));
            }
            return detach;
        }
    };

    function Arrow(name, arity, freeMap) {
        this.name = name;
        this.arity = arity;
        this.freeMap = freeMap;
    }
    
    // A data structure for keeping in the scheme.
    // goalOp is an goalOpArity-arg term.
    // goalArg is in 1...goalOpArity, specifying which argchild the goal is
    // toolArg is 1 or 2, specifying one of the args of the tool on the stack.
    // the current goal's paren'ts [goalArg] equals the current tool's [toolArg]
    // we want to replace it with the tool's other arg.
    // isCovar tells whether the tool args will be reversed in order.
    function PushUp(axMp, goalArrow, goalArg, toolArg,
                    isCovar, parentArrow, grease, fact) {
        this.isCovar = isCovar;
        this.parentArrow = parentArrow;
        this.pushUp = function(pusp, work) {
            pusp.newSteps.push(pusp.tool[1]);
            pusp.newSteps.push(pusp.tool[2]);
            pusp.goalPath.pop();
            var goalParent = zpath(pusp.goal, pusp.goalPath);
            var goalN = work.nameTerm(goalArrow.name, goalArrow.freeMap);
            var arr1 = [goalN];
            var arr2 = [goalN];
            for (var i = 1; i < goalArrow.arity; i++) {
                if (i == goalArg) {
                    arr1.push(pusp.tool[toolArg]);
                    arr2.push(pusp.tool[3 - toolArg]);
                } else {
                    var arg = goalParent[i];
                    pusp.newSteps.push(arg);
                    arr1.push(arg);
                    arr2.push(arg);
                }
            }
            if (grease) grease(pusp, work);
            pusp.newSteps.push(nameDep(work, fact));
            pusp.newSteps.push(nameDep(work, axMp));
            var parentArrowN = work.nameTerm(parentArrow.name,
                                             parentArrow.freeMap);
            pusp.tool = [parentArrowN,
                         isCovar ? arr2 : arr1,
                         isCovar ? arr1 : arr2];
            pusp.toolPath = [isCovar ? 2 : 1];
        }
    }


    function globalSub(fact, varMap, work, exp) {
        function mapper(x) {
            if (Array.isArray(x) && (x.length > 0)) {
                var out = x.slice(1).map(mapper);
                var op = x[0];
                out.unshift(work.nameTerm(fact.Skin.TermNames[op],
                                          fact.FreeMaps[op]));
                return out;
            } else {
                if (varMap[x] == undefined) {
                    throw new Error("Unmapped var " + x);
                }
                return varMap[x];
            }
        }
        if (exp == undefined) exp = fact.Core[Fact.CORE_STMT];
        return mapper(exp);
    }

    function fingerprint(obj) {
        var B64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789._-";
        var str;
        if (typeof obj === 'string') {
            str = obj;
        } else {
            str = JSON.stringify(obj);
        }

        var hash = 0, i, chr, len;
        if (str.length == 0) return hash;
        for (i = 0, len = str.length; i < len; i++) {
            chr = str.charCodeAt(i);
            hash = ((hash << 5) - hash) + chr;
            //hash |= 0; // Convert to 32bit integer
        }
        var a = "";
        while (hash != 0 && hash != -1) {
            a += B64[hash & 63];
            hash = hash >> 6;
        }
        //console.log("str = " + str + "\nhash=" + hash + "\na  = " + a);
        return a;
    }

    function nameDep(workFact, depFact) {
        var n = workFact.nameDep(fingerprint(depFact.getMark()), depFact);
        return n;
    }

    function clone(obj) {
        return JSON.parse(JSON.stringify(obj)); // TODO:slow
    }

    // NB: not the same as orcat's xpath definition. Pass 0 to get the term.
    function zpath(exp, path) {
        var a = exp, l = path.length, i = 0;
        for (i = 0; i < l; i++) {
            a=a[path[i]];
        }
        return a;
    }

    // Visits each var in each exp exactly once, in left-to-right depth-first order
    // TODO: this is an error-prone api since exps will be confused for an exp
    function eachVarOnce(exps, cb, seen) {
        function visit(exp) {
            seen = seen || {};
            if (!Array.isArray(exp)) {
                if (!seen[exp]) {
                    seen[exp] = 1;
                    cb(exp);
                }
            } else {
                exp.slice(1).forEach(visit);
            }
        }
        exps.forEach(visit);
    }

    function newDummy() {
        dummyNum++;
        return "DUMMY_" + dummyNum;
    }

    // Given a fact or an expression, replace its variables with the
    // corresponding (transitively-closed) values from the map.
    function undummy(workOrExp, dummyMap) {
        function replaceDummies(x, alreadyReplaced) {
            // TODO: handle freemap dummies correctly!
            if (Array.isArray(x)) {
                for (var i = 1; i < x.length; i++) {
                    x[i] = replaceDummies(x[i], alreadyReplaced);
                }
                return x;
            } else if ((typeof x == 'number') || (typeof x == 'string')) {
                if (DEBUG) console.log("ar: " + JSON.stringify(alreadyReplaced));
                if (typeof alreadyReplaced != 'object') {
                    alreadyReplaced = {};
                }
                while (dummyMap[x] != undefined) {
                    if (alreadyReplaced[x]) {
                        throw new Error("DummyMap has cyle through " + x + ":" + JSON.stringify(dummyMap));
                    }
                    if (DEBUG) console.log("replacing: " + x + " with " + JSON.stringify(dummyMap[x]));
                    alreadyReplaced[x] = 1;
                    x = dummyMap[x];
                }
                return Array.isArray(x) ? replaceDummies(x, alreadyReplaced) : x;
            } else {
                throw new Error("hmm")
            }
        }

        if ((typeof workOrExp == 'number') || Array.isArray(workOrExp)) {
            return replaceDummies(workOrExp);
        } else if (workOrExp.ensureFree) {
            workOrExp.Core[Fact.CORE_STMT] = replaceDummies(
                workOrExp.Core[Fact.CORE_STMT])
            workOrExp.Core[Fact.CORE_HYPS] =
                workOrExp.Core[Fact.CORE_HYPS].map(replaceDummies);
            workOrExp.Tree.Proof =
                workOrExp.Tree.Proof.map(replaceDummies);
            var oldFreeLists = workOrExp.Core[Fact.CORE_FREE];
            workOrExp.setFree([]);
            oldFreeLists.forEach(function(freeList) {
                var oldTv = freeList.shift();
                eachVarOnce([replaceDummies(oldTv)], function(newV) {
                    freeList.forEach(function(v) {
                        workOrExp.ensureFree(newV, replaceDummies(v));
                    });
                });
            });
            return workOrExp;
        } else {
            throw new Error("Not work or exp: " + workOrExp);
        }
    }

    // Returns a list of mandatory hypotheses (i.e., values for each var) of the
    // fact, such that the named subexpression of the fact's stmt matches the
    // named subexpression of the work's first hyp.
    //
    // Assumes fact has no hypotheses.
    //
    // Modifies the work as necessary (but only once success is guaranteed) by
    // specifying dummy vars and adding Free constraints.
    //
    // @return a map from fact vars to terms in the work's variables. dummy
    //     variables will get new names for use in the work.
    //
    // @throws an error if the unification is impossible or would violate a Free
    //     constraint.
    function getMandHyps(work, hypPath, fact, stmtPath, optVarMap) {
        var debugPath = [];
        var nonDummy = {};
        var dummyMap = {};
        eachVarOnce([work.Core[Fact.CORE_STMT]], function(v) {
            nonDummy[v] = true;
        });
        // from fact vars to work exps
        var varMap = {};
        var workExp = zpath(work.Core[Fact.CORE_HYPS][0], hypPath);
        var factExp = zpath(fact.Core[Fact.CORE_STMT], stmtPath);
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

        function checkVarMapForFreeness(varMap) {
            fact.Core[Fact.CORE_FREE].forEach(function(freeList) {
                var newExp = varMap[freeList[0]];
                if (newExp == undefined) {
                    return;
                }
                var varsAppearing = {};
                eachVarOnce([newExp], function(v) {
                    varsAppearing[v] = true; // TODO: what if binding??
                });
                freeList.slice(1).forEach(function(freeVar) {
                    var newVar = varMap[freeVar];
                    if (Array.isArray(newVar)) {
                        // This should not be possible.
                        throw new Error("Substituting term for binding var?!");
                    }
                    if (varsAppearing[newVar]) {
                        throw new Error(
                            "Freeness Violation:\n  Found var " + newVar +
                                " (was " + freeVar +")\n  in exp " +
                                JSON.stringify(newExp) +
                                " (was " + freeList[0] +")");
                    }
                });
            });
        }
        function mapVarTo(factVarName, workExp) {
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
                (stmtPath != null) &&
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
                    if (!nonDummy[factSubExp]) {
                        if (factSubExp != workSubExp) {
                            dummyMap[factSubExp] = workSubExp;
                        }
                    } else if (Array.isArray(workSubExp)) {
                        // A mapped, nondummy, nonarray var should be an array exp.
                        // This isn't going to work.
                        assertEqual("mappedA", factSubExp, workSubExp)
                    } else if (!nonDummy[workSubExp]) {
                        if (factSubExp != workSubExp) {
                            dummyMap[workSubExp] = factSubExp;
                        }
                    } else {
                        // A mapped, nondummy, nonarray var should be a nondummy,
                        // nonarray var. They'd better be the same.
                        assertEqual("mapped", factSubExp, workSubExp);
                    }
                } else {
                    mapVarTo(factSubExp, workSubExp);
                }
            } else {
                var op = factSubExp[0];
                var factContext = alreadyMapped ? work : fact;
                var factTerm = factContext.Skin.TermNames[op];
                var factTermFreeMap = factContext.FreeMaps[op];
                if (factTerm == undefined) {
                    throw new Error("No factTerm\n" +
                                    JSON.stringify(fact) + "\n" +
                                    JSON.stringify(factSubExp));
                }
                if (!Array.isArray(workSubExp)) {
                    // Work is var, Fact is exp.
                    if (nonDummy[workSubExp]) {
                        assertEqual("shrug", workSubExp, factSubExp);
                    } else {
                        var newExp = [];
                        newExp.push(work.nameTerm(factTerm, factTermFreeMap));
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
        if (DEBUG) {console.log("# About to undummy : " + JSON.stringify(work));}
        if (DEBUG) {console.log("# Dummy map : " + JSON.stringify(dummyMap));}
        undummy(work, dummyMap);
        if (DEBUG) {console.log("# Undummied : " + JSON.stringify(workExp));}
        //console.log("Unified: " + JSON.stringify(varMap));
        for (x in varMap) if (varMap.hasOwnProperty(x)) {
            varMap[x] = undummy(varMap[x], dummyMap);
        }
        checkVarMapForFreeness(varMap);

        eachVarOnce([fact.Core[Fact.CORE_STMT]], function(v) {
            if (!varMap.hasOwnProperty(v)) {
                if (optVarMap && optVarMap.hasOwnProperty(v)) {
                    varMap[v] = optVarMap[v];
                } else {
                    varMap[v] = work.nameVar(newDummy());
                }
            }
        });
        return varMap;
    }

    // Returns an array of functions to push the given toolOp/toolArg up the
    // tree to the top and detach. Each one can be called on (pusp, work).
    function getPushUps(work, workPath, toolOp, toolArg) {
        // This looks a lot more complicated than it is.  Here's the concept: at
        // each level of the goal tree, we need to query for and apply a pushUp
        // theorem.  However, in order to know *which* pushUp theorem to apply,
        // we need both the goal's operator at the level above, and the result
        // of the pushUp query from the level below.
        // Each query is [goalOp, goalArgNum, toolOp, toolArgNum];
        var pushUps = []; // pushUp results, from the bottom up
        var queries = []; // goalOps and argNums from the top down
        var term = work.Core[Fact.CORE_HYPS][0];
        workPath.forEach(function(z) { // walk down, filling in the first half of the queries
            var op = work.Skin.TermNames[term[0]];
            queries.push([op, z]);
            term = term[z];
        });
        while (queries.length > 0) {        // walk back up, finishing and executing the queries
            var q = queries.pop();
            q.push(toolOp);
            q.push(toolArg);
            var pu = scheme.queryPushUp(q);
            pushUps.push(pu.pushUp.bind(pu));
            toolOp = pu.parentArrow.name;
            toolArg = (pu.isCovar ? 2 : 1);
        }
        // Now, since the invariant holds and goalPath = [], and
        // tool[toolPath[0]] == goal, so just detach.
        var detacher = scheme.queryDetach([toolOp, [toolArg]]);
        pushUps.push(detacher.detach.bind(detacher));
        return pushUps;
    }
    
    // Returns an map of {k: [operatator, argNum, opaque]} describing which theorems,
    // given the current set of known pushUps, could be applied to the given
    // work at the given path.  If you want, you can pass the opaque part back
    // to applyFact to maybe speed things up?
    function getUsableTools(work, workPath) {
        var actuals = {};
        var term = work.Core[Fact.CORE_HYPS][0];
        if (workPath.length > 0) {
            // Half-query for the final pushUp, then test the chain
            var parent;
            var argNum;
            workPath.forEach(function(z) {
                parent = term;
                term = term[z];
                argNum = z;
            });
            var goalOp = work.Skin.TermNames[parent[0]];
            var potentials = scheme.halfQueryPushUp(goalOp, argNum);
            for (var k in potentials) if (potentials.hasOwnProperty(k)) {
                var v = potentials[k];
                try {
                    var pus = getPushUps(work, workPath, v[0], v[1]);
                    var out = v.slice();
                    // TODO: supply opaque: out.push(pus);
                    actuals[v] = out;
                } catch(e) {
                    // TODO: should check which error
                }
            }
        } else {
            //Any detachable.
            for (var k in scheme.detachMemo) if (scheme.detachMemo.hasOwnProperty(k)) {
                var v = scheme.detachMemo[k];
                actuals[[v.op, v.argNum]] = [v.op, v.argNum];
            }
        }
        return actuals;
    }

    // Filters the known-theorem list for facts which could ground the given
    // work (i.e.e., a call to ground(work, fact) would succeed). For each fact,
    // callsback with the work and the grounding fact. Currently, this will be
    // slow if there are many known facts; in the future we hope to do some
    // fancy indexing.
    function forEachGroundableFact(work, cb) {
        allKnownFacts.forEach(function(f) {
            if (f.Core[Fact.CORE_HYPS].length == 0) {
                try {
                    if (work.Core[Fact.CORE_HYPS][0] !== 1) {
                        //XXX TODO: infinite recurse bug here, not trying.
                        getMandHyps(work, [], f, []);
                    }
                    nextTick(cb.bind(null,work,f));
                } catch(e) {
                    // TODO: should not be using exceptions for this
                }
            }
        });
    }
    
    // Applies the given fact (with zero hypotheses) to the workspace (a proved
    // theorem with one hypothesis, representing a work-in-progress). The
    // workpath points to a subexpression of the work's only hypothesis. The
    // factPath points to a subexpression of the fact's statement. These two
    // subexpressions will be unified; then the fact (and the required pushup
    // procedures) will be added to the beginning of the work's proof, and the
    // work's hypthesis will be updated.
    function applyFact(work, workPath, fact, factPath, optVarMap) {
        if (!Array.isArray(factPath) ||
            (factPath.length != 1) ||
            ((factPath[0] != 1) && (factPath[0] != 2))) {
            throw new Error("factPath must be [1] or [2] for now.");
        }
        if (!Array.isArray(workPath)) {
            throw new Error("Bad workPath " + workPath);
        }
        var varMap = getMandHyps(work, workPath, fact, factPath, optVarMap);
        if (DEBUG) {console.log("# MandHyps: " + JSON.stringify(varMap));}
        // If that didn't throw, we can start mutating
        // PushUpScratchPad
        var pusp = {};

        pusp.newSteps = [];
        if (DEBUG) console.log("Vars from " + JSON.stringify(fact));
        eachVarOnce([fact.Core[Fact.CORE_STMT]], function(v) {
            pusp.newSteps.push(varMap[v]);
        });
        pusp.newSteps.push(nameDep(work, fact));
        // Now on the stack: an instance of fact, with factPath equalling a
        // subexp of work.

        // #. invoke sequence of pushup theorems, ensuring presence in Deps
        pusp.tool = globalSub(fact, varMap, work);       // what's on the stack
        pusp.toolPath = clone(factPath);                 // path to subexp A
        pusp.goal = clone(work.Core[Fact.CORE_HYPS][0]); // what to prove
        pusp.goalPath = clone(workPath);                 // path to subexp B
        // invariant: subexp A == subexp B
        function checkInvariant() {
            if (DEBUG) {
                console.log("Check invariant: \n" +
                            JSON.stringify(zpath(pusp.tool, pusp.toolPath)) +
                            "\n" +
                            JSON.stringify(zpath(pusp.goal, pusp.goalPath)));
                console.log("  pusp: ", JSON.stringify(pusp));
            }
            if (JSON.stringify(zpath(pusp.tool, pusp.toolPath)) !=
                JSON.stringify(zpath(pusp.goal, pusp.goalPath))) {
                throw new Error("Invariant broken!");
            }
        }
        var pushUps = getPushUps(work, workPath,
                                 fact.Skin.TermNames[fact.Core[Fact.CORE_STMT][0]], factPath[0]);
        // Now apply the pushups from the bottom up, and finally detach.
        pushUps.forEach(function(pu) {
            if (DEBUG) checkInvariant();
            pu(pusp, work);
        })

        // Now we have a complete pusp, so apply it to the workspace.

        // don't delete any steps
        pusp.newSteps.unshift(0);
        // keep the "hyps.0".
        pusp.newSteps.unshift(1);
        work.Tree.Proof.splice.apply(work.Tree.Proof, pusp.newSteps);

        // #. update DV list
        fact.Core[Fact.CORE_FREE].forEach(function(freeList) {
            var origTermVar = freeList[0];
            var newExp = varMap[origTermVar];
            // NOTE: this creates freelists even for binding vars. They will be
            // omitted in the ghilbert serialization (Context.toString)
            eachVarOnce([newExp], function(newV) {
                freeList.slice(1).forEach(function(origBV) {
                    var bV = varMap[origBV];
                    if (newV == bV) {
                        // Shouldn't happen; this is checked for in mandHyps
                        throw new Error("Freeness violation!");
                    }
                    work.ensureFree(newV, bV);
                });
            });
        });
        // TODO:
        // #. Add explanatory comments to Skin.Delimiters
        return work;
    };

    // Applies the given inference fact, which must have exactly one
    // hypothesis. The conclusion of the inference must unify against the work's
    // only hypothesis. The work's new hypothesis will be the fact's hypothesis.
    function applyInference(work, infFact, optVarMap) {
        var varMap = getMandHyps(work, [], infFact, [], optVarMap);
        if (DEBUG) {console.log("# Inf MandHyps: " + JSON.stringify(varMap));}
        var newSteps = [];
        // Need a mandhyp step for each var appearing in the stmt which does NOT
        // appear in the hyps.
        var varToStepIndex = {};
        eachVarOnce([infFact.Core[Fact.CORE_STMT]], function(v) {
            varToStepIndex[v] = newSteps.length;
            newSteps.push(varMap[v]);
        });
        eachVarOnce(infFact.Core[Fact.CORE_HYPS], function(v) {
            if (varToStepIndex.hasOwnProperty(v)) {
                newSteps[varToStepIndex[v]] = "";
            }
        });
        newSteps = newSteps.filter(function(x) { return x !== "";});
        // preserve "hyps.0"
        newSteps.unshift(work.Tree.Proof.shift());
        newSteps.push(nameDep(work, infFact));
        newSteps.push.apply(newSteps, work.Tree.Proof);
        work.setProof(newSteps);
        var newHyp = globalSub(infFact, varMap, work,
                               infFact.Core[Fact.CORE_HYPS][0]);
        if (DEBUG) {console.log("# Inf newHyp: " + JSON.stringify(newHyp));}
        work.setHyps([newHyp]);
        return work;
    };

    // Replace a dummy variable with a new exp containing the given term and
    // some new dummy variables.  TODO: should not allow specifying binding var
    function specifyDummy(work, dummyPath, newTerm, arity, freeMap) {
        // TODO: duplicated code
        var nonDummy = {};
        eachVarOnce([work.Core[Fact.CORE_STMT]], function(v) {
            nonDummy[v] = true;
        });
        var workExp = zpath(work.Core[Fact.CORE_HYPS][0], dummyPath);
        if ((workExp == undefined) || Array.isArray(workExp)) {
            throw new Error("Bad work path:\n" + dummyPath + "\n" +
                            JSON.stringify(work));
        }
        if (nonDummy[workExp]) {
            throw new Error("Var " + workExp + " is no dummy!");
        }
        return specify(work, workExp, newTerm, arity, freeMap);
    }
    // Replace all instances of a variable in the given fact with a new exp.
    // newTermOrVarNum can be an existing variable number. Or it can be a term
    // name, in which case its arity and freeMap must be specified; it will get
    // all-new children.  (Note: using this on a Work with a non-dummy variable
    // is not sound! use specifyDummy instead to check for this.)  TODO: should
    // not allow specifying binding var
    function specify(fact, oldVarNum, newTermOrVarNum, arity, freeMap) {
        var newExp;
        if (arity === undefined) {
            if (typeof newTermOrVarNum !== 'number') {
                throw new Error("Expected var num or term with arity/freemap: "
                                + newTermOrVarNum);
                }
            newExp = newTermOrVarNum;
        } else {
            newExp = [fact.nameTerm(newTermOrVarNum, freeMap)];
            for (var i = 0; i < arity; i++) {
                newExp.push(fact.nameVar(newDummy()));
            }
        }
        var dummyMap = {};
        dummyMap[oldVarNum] = newExp;
        return undummy(fact, dummyMap);
    }

    // Asserts that the work's only hypothesis is an instance of the given
    // fact. Returns a "grounded" theorem, i.e. one with no hypothesis,
    // representing a completed proof.
    function ground(work, dirtFact) {
        // verify that the hyp is an instance of the dirt
        var varMap = getMandHyps(work, [], dirtFact, []);
        if (DEBUG) {console.log("# ground MandHyps: "+JSON.stringify(varMap));}
        work.Core[Fact.CORE_HYPS].shift();
        var newSteps = [];
        eachVarOnce([dirtFact.Core[Fact.CORE_STMT]], function(v) {
            newSteps.push(varMap[v]);
        });
        newSteps.push(nameDep(work, dirtFact));

        // remove hyp step
        work.Tree.Proof.shift();
        // Replace with proof of hyp instance
        work.Tree.Proof.unshift.apply(work.Tree.Proof, newSteps);
        if (DEBUG) {console.log("# Work before canon:" + JSON.stringify(work));}
        work = canonicalize(work);
        if (DEBUG) {console.log("# Work after canon:" + JSON.stringify(work));}
        return work;
    };

    // Reorders terms/variables so that they appear in first-used order.
    // Removes no-longer-used dummies. // TODO: remove from freemap
    // Renames remaining variable Skins to Vn
    // Consolidates and sort freelists
    // TODO: sort deps alphabetically
    function canonicalize(work) {
        var out = new Fact();
        function mapTerm(t) {
            if (!work.FreeMaps[t]) {
                throw new Error("canon " + JSON.stringify(work));
            }
            return out.nameTerm(work.Skin.TermNames[t], work.FreeMaps[t]);
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

        // Remove spurious free vars.
        var varsSeen = {};
        eachVarOnce(work.Core[Fact.CORE_HYPS],function(v) {
            varsSeen[v] = true;});
        eachVarOnce([work.Core[Fact.CORE_STMT]],function(v) {
            varsSeen[v] = true;});

        // Remove freelist entries where the first var is a binding var.
        var bindingVars = {};
        work.Core[Fact.CORE_FREE].forEach(function(freeList) {
            freeList.slice(1).forEach(function(v) {bindingVars[v] = 1;});
        });
        work.Core[Fact.CORE_FREE].forEach(function(freeList) {
            var termVar = mapExp(freeList[0]);
            if (varsSeen[termVar] && !bindingVars[termVar]) {
                freeList.slice(1).forEach(function(v) {
                    if (varsSeen[v]) {
                        out.ensureFree(termVar, mapExp(v));
                    }
                });
            }
        });

        out.setProof(work.Tree.Proof.map(mapExp));
        if (work.Tree.Proof.length == 0) {
            out.setCmd("stmt");
        } else if (typeof(work.Tree.Definiendum) == 'number') {
            out.setCmd("defthm");
        } else {
            out.setCmd("thm");
        }
        
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
    };

    // Register this fact as available to the prover for pushUp or detach.  If
    // this is the first time that the fact's root operator becomes usable for a
    // tool, we'll return that operator. Otherwise, nothing will be returned.
    function onAddFact(fact) {
        allKnownFacts.push(fact);
        var coreStr = JSON.stringify(fact.Core);
        var rarr, harr, rarr, rarrAxmp;
        // First, detect detachment theorems
        if (coreStr == "[[0,[0,0,1]],1,[]]") {
            // ax-mp
            rarr = fact.Skin.TermNames[0];
            //console.log("Discovered ax-mp: rarr=" + rarr);
            scheme.detachMemo[[rarr,[2]]] = {
                fact: fact,
                op: rarr,
                argNum: 2,
                detach: function(pusp, work) {
                    pusp.newSteps.push(nameDep(work, this.fact));
                    work.Core[Fact.CORE_HYPS][0] = pusp.tool[1];
                }
            };
            if (!scheme.toolsSeen[rarr]) {
                scheme.toolsSeen[rarr] = true;
                return rarr;
            }
        } else if (coreStr == "[[],[0,[1,0,1],[0,0,1]],[]]") {
            // bi1
            rarr = fact.Skin.TermNames[0];
            harr = fact.Skin.TermNames[1];
            rarrAxmp = scheme.detachMemo[[rarr, [2]]];
            if (rarrAxmp) {
                //console.log("Discovered bi1: harr=" + harr + " / rarr=" + rarr);
                scheme.detachMemo[[harr,[2]]] = {
                    fact: fact,
                    op: harr,
                    argNum: 2,
                    detach: function(pusp, work) {
                        pusp.newSteps.push(pusp.tool[1]);
                        pusp.newSteps.push(pusp.tool[2]);
                        pusp.newSteps.push(nameDep(work, this.fact));
                        pusp.newSteps.push(nameDep(work, rarrAxmp.fact));
                        pusp.newSteps.push(nameDep(work, rarrAxmp.fact));
                        work.Core[Fact.CORE_HYPS][0] = pusp.tool[1];
                    }
                }
                if (!scheme.toolsSeen[harr]) {
                    scheme.toolsSeen[harr] = true;
                    return harr;
                }
            }
        } else if (coreStr == "[[],[0,[1,0,1],[0,1,0]],[]]") {
            // bi2
            rarr = fact.Skin.TermNames[0];
            harr = fact.Skin.TermNames[1];
            rarrAxmp = scheme.detachMemo[[rarr, [2]]];
            if (rarrAxmp) {
                //console.log("Discovered bi2: harr=" + harr + " / rarr=" + rarr);
                scheme.detachMemo[[harr,[1]]] = {
                    fact: fact,
                    op: harr,
                    argNum: 1,
                    detach: function(pusp, work) {
                        pusp.newSteps.push(pusp.tool[1]);
                        pusp.newSteps.push(pusp.tool[2]);
                        pusp.newSteps.push(nameDep(work, this.fact));
                        pusp.newSteps.push(nameDep(work, rarrAxmp.fact));
                        pusp.newSteps.push(nameDep(work, rarrAxmp.fact));
                        work.Core[Fact.CORE_HYPS][0] = pusp.tool[2];
                    }
                }
                if (!scheme.toolsSeen[harr]) {
                    scheme.toolsSeen[harr] = true;
                    return harr;
                }
            }
        } else if (coreStr == "[[0],[0,1,0],[]]") {
            // ax-gen
            var forall = fact.Skin.TermNames[0];
            //console.log("Discovered ax-gen: forall=" + forall);
            scheme.greaseMemo[forall] = {fact:fact};
        }

        // Next, detect pushUp theorems.
        if (fact.Core[Fact.CORE_HYPS].length ||
            fact.Core[Fact.CORE_FREE].length) {
            // Can't use pushUp theorems with hyps or free constrains.
            return;
        }
        var stmt = fact.Core[Fact.CORE_STMT];
        var terms = fact.Skin.TermNames;
        var detacher = scheme.detachMemo[[terms[0], [2]]];
        var grease = null;

        if ((stmt.length != 3) || (stmt[0] != 0) || !detacher) {
            // Root operation must be some version of implication -- i.e.,
            // something we can detach.
            return;
        }
        if (detacher.fact.Core[Fact.CORE_HYPS].length == 0) {
            // TODO: right now this only works with ->/axmp, but it should work
            // with anything that can be detached. Detacher.detach() should
            // return pusp.tool[1] instead of putting it directly into the hyps.
            return;
        }

        if (!Array.isArray(stmt[1]) ||
            (stmt[1].length != 3) || (stmt[1][1] != 0)) {
            // Antecedent must be a binary operation on two args
            return;
        }
        var anteArrow;
        var anteArg1;
        var anteArg2;
        var greaser;
        if (stmt[1][2] == 1) {
            // This is a greaseless pushUp
            anteArrow = terms[stmt[1][0]];
            anteArg1 = 0;
            anteArg2 = 1;
        } else if (Array.isArray(stmt[1][2]) &&
                   (greaser = scheme.greaseMemo[terms[stmt[1][0]]]) &&
                   (stmt[1][2].length == 3) &&
                   (stmt[1][2][1] == 1) &&
                   (stmt[1][2][2] == 2)) {
            // Handle greasing forall
            anteArrow = terms[stmt[1][2][0]];
            anteArg1 = 1;
            anteArg2 = 2;
            grease = function(pusp, work) {
                var x = pusp.newSteps.pop();
                var b = pusp.newSteps.pop();
                var a = pusp.newSteps.pop();
                pusp.newSteps.push(x);
                pusp.newSteps.push(nameDep(work, greaser.fact));
                pusp.newSteps.push(x);
                pusp.newSteps.push(a);
                pusp.newSteps.push(b);
            };
        } else {
            // Not a valid pushUp
            return;
        }


        if (!Array.isArray(stmt[2]) || (stmt[2].length != 3) ||
            (!Array.isArray(stmt[2][1])) || (!Array.isArray(stmt[2][2])) ||
            (stmt[2][1].length != stmt[2][2].length) ||
            (stmt[2][1][0] != stmt[2][2][0])
           ) {
            // Consequent must be an binary operation on two terms identical
            // except for the replacement of the antecedent args
            return;
        }
        var parentTermNum = stmt[2][0];
        var parentArrow = new Arrow(terms[parentTermNum],
                                    stmt[2].length,
                                    fact.FreeMaps[parentTermNum]);
        var childTermNum = stmt[2][1][0];
        var childArrow = new Arrow(terms[childTermNum],
                                   stmt[2][1].length,
                                   fact.FreeMaps[childTermNum]);
        var whichArg = null;
        var isCov = true;
        for (var i = 1; i < childArrow.arity; i++) {
            var arg1 = stmt[2][1][i];
            var arg2 = stmt[2][2][i];
            switch (arg1) {
            case anteArg2:
                // Covariant facts have 0 in the first term and 1 in the second.
                // Contravariant facts have the reverse.
                isCov = false;
                // fall through
            case anteArg1:
                if (whichArg != null) {
                    // Antecedent args cannot appear more than once
                    return;
                }
                whichArg = i;
                if (arg1 + arg2 != anteArg1 + anteArg2) {
                    // Corresponding arg in other term must be the other of the
                    // two antecedent args
                    return;
                }
                break;
            default:
                if (arg2 != arg1) {
                    // all other args must be the same
                    return;
                }
            }
        }
        /*
        console.log("Discovered pushup: " +
                    " child=" + childArrow + "/" + whichArg + 
                    " ante=" + anteArrow + " isCov?" + isCov + " parent=" + parentArrow);
        */
        var halfMemo = scheme.pushUpHalfMemo[[childArrow.name, whichArg]];
        if (!halfMemo) {
            halfMemo = {};
            scheme.pushUpHalfMemo[[childArrow.name, whichArg]] = halfMemo;
        }
        for (var i = 1; i <= 2; i++) {
            halfMemo[[anteArrow, i]] = [anteArrow, i];
            scheme.pushUpMemo[[childArrow.name, whichArg, anteArrow, i]] =
                new PushUp(detacher.fact, childArrow, whichArg,
                           i, (i == 2 ? isCov : !isCov),
                           parentArrow, grease, fact);
        }
        if (!scheme.toolsSeen[anteArrow]) {
            scheme.toolsSeen[anteArrow] = true;
            return anteArrow;
        }
    };

    if (!module.exports) module.exports = {};
    module.exports.onAddFact = onAddFact;
    module.exports.canonicalize = canonicalize;
    module.exports.ground = ground;
    module.exports.specifyDummy = specifyDummy;
    module.exports.applyInference = applyInference;
    module.exports.applyFact = applyFact;
    module.exports.fingerprint = fingerprint;
    module.exports.forEachGroundableFact = forEachGroundableFact;
    module.exports.getUsableTools = getUsableTools;
    module.exports.getMandHyps = getMandHyps;
    module.exports.globalSub = globalSub;
    module.exports.specify = specify;
    module.exports.DEBUG = function() {DEBUG = true;};
})(module);
