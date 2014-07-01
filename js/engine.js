var Fact = require('../../caghni/js/fact.js'); //XXX
var Crypto = require('crypto');
var Bencode = require('bencode');

// This engine assists in authoring proofs by working backwards from a target
// goal. The exported methods operate on a "workspace", i.e. a Fact whose
// statement is the target, and whose only hypothesis represents "what we must
// prove". To start, the hypothesis is simply the conclusion, and the proof is
// trivial. At each step, we work backwards from the hypothesis, adding to the
// beginning of the proof, while the conclusion remains the same. Eventually we
// hope to "ground" the workspace in a known Fact, leaving us with a completed
// zero-hypothesis theorem.
(function(module) {
    var DEBUG = false;
    if (!module.exports) {
        module.exports = {};
    }


    function globalSub(fact, varMap, work, exp) {
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
        if (exp == undefined) exp = fact.Core[Fact.CORE_STMT];
        return mapper(exp);
    }

    function fingerprint(obj) {
        var hash = Crypto.createHash('sha1');
        hash.update(Bencode.encode(obj));
        return "bencode-sha1-" + hash.digest('hex');
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
        return "DUMMY_" + Math.random(); //XXX
    }

    // Given a fact or an expression, replace its variables with the
    // corresponding (transitively-closed) values from the map.
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
            if (DEBUG) {
                console.log("#XXXX Work undummied: " + JSON.stringify(workOrExp));
            }
            return workOrExp;
        }
    }

    // Returns a list of mandatory hypotheses (i.e., values for each var) of the
    // fact, such that the named subexpression of the fact's stmt matches the named
    // subexpression of the work's first hyp.
    //
    // Modifies the work as necessary (but only once success is guaranteed) by
    // specifying dummy vars and adding Free constraints.
    //
    // @return a map from fact vars to terms in the work's variables. dummy
    //     variables will get no assignment.
    //
    // @throws an error if the unification is impossible or would violate a Free
    //     constraint.
    function getMandHyps(work, hypPath, fact, stmtPath) {
        var debugPath = [];
        var nonDummy = {};
        var dummyMap = {};
        eachVarOnce([work.Core[Fact.CORE_STMT]], function(v) {
            nonDummy[v] = v;
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
        checkVarMapForFreeness(varMap);
        return varMap;
    }

    // Applies the given fact (with zero hypotheses) to the workspace (a proved
    // theorem with one hypothesis, representing a work-in-progress). The
    // workpath points to a subexpression of the work's only hypothesis. The
    // factPath points to a subexpression of the fact's statement. These two
    // subexpressions will be unified; then the fact (and the required pushup
    // procedures) will be added to the beginning of the work's proof, and the
    // work's hypthesis will be updated.
    // TODO: scheme = {queryPushup, queryDetach} needs some work.
    module.exports.applyFact = function(work, workPath, fact, factPath, scheme) {
        var varMap = getMandHyps(work, workPath, fact, factPath);
        if (DEBUG) {console.log("# MandHyps: " + JSON.stringify(varMap));}
        // If that didn't throw, we can start mutating
        // PushUpScratchPad
        var pusp = {};

        pusp.newSteps = [];
        if (DEBUG) console.log("Vars from " + JSON.stringify(fact));
        eachVarOnce([fact.Core[Fact.CORE_STMT]], function(v) {
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

            scheme.queryPushUp(goalTerm, goalArgNum, goalTermArity, toolTerm,
                        pusp.toolPath[pusp.toolPath.length - 1]).
                pushUp(pusp, work);

        }
        checkInvariant();

        // Now, since the invariant holds and goalPath = [], and
        // tool[toolPath[0]] == goal, so just detach.
        var query = [work.Skin.TermNames[pusp.tool[0]], pusp.toolPath];
        scheme.queryDetach(query).detach(pusp, work);

        // #. compute new preimage and update Hyps.0
        // TODO: hardcoded for now

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
    module.exports.applyInference = function(work, infFact) {
        var varMap = getMandHyps(work, [], infFact, []);
        if (DEBUG) {console.log("# Inf MandHyps: " + JSON.stringify(varMap));}
        var newSteps = [];
        // Need a mandhyp step for each var appearing in the stmt which does NOT
        // appear in the hyps.
        var varToStepIndex = {};
        eachVarOnce([infFact.Core[Fact.CORE_STMT]], function(v) {
            var newV = varMap[v];
            if (DEBUG) {console.log("v=" + v + ", newV=" + varMap[v]);}
            if (newV == undefined) {
                newV = work.nameVar(newDummy()); // XXX HACK
                varMap[v] = newV;
            }
            if (DEBUG) {console.log("v=" + v + ", newV=" + varMap[v]);}
            varToStepIndex[v] = newSteps.length;
            newSteps.push(newV);
        });
        eachVarOnce(infFact.Core[Fact.CORE_HYPS], function(v) {
            if (varToStepIndex.hasOwnProperty(v)) {
                newSteps[varToStepIndex[v]] = ""; // TODO: should clean these out.
            }
        });
        newSteps = newSteps.filter(function(x) { return x !== "";});
        // preserve "hyps.0"
        newSteps.unshift(work.Tree.Proof.shift());
        newSteps.push(nameDep(work, infFact));
        newSteps.push.apply(newSteps, work.Tree.Proof);
        work.setProof(newSteps);
        var newHyp = globalSub(infFact, varMap, work, infFact.Core[Fact.CORE_HYPS][0]);
        if (DEBUG) {console.log("# Inf newHyp: " + JSON.stringify(newHyp));}
        work.setHyps([newHyp]);
        return work;
    };

    // Replace a dummy variable with a new exp containing the given term and some
    // new dummy variables.
    // TODO: should not allow specifying binding var
    module.exports.specifyDummy = function(work, dummyPath, newTerm, newTermArity) {
        // TODO: duplicated code
        var nonDummy = {};
        var dummyMap = {};
        eachVarOnce([work.Core[Fact.CORE_STMT]], function(v) {
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

    // Asserts that the work's only hypothesis is an instance of the given
    // fact. Returns a "grounded" theorem, i.e. one with no hypothesis,
    // representing a completed proof.
    module.exports.ground = function(work, dirtFact) {
        // verify that the hyp is an instance of the dirt
        var varMap = getMandHyps(work, [], dirtFact, []);
        if (DEBUG) {console.log("# ground MandHyps: " + JSON.stringify(varMap));}
        work.Core[Fact.CORE_HYPS].shift();
        var newSteps = [];
        eachVarOnce([dirtFact.Core[Fact.CORE_STMT]], function(v) {
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
        work = module.exports.canonicalize(work);
        if (DEBUG) {console.log("#XXXX Work after canon:" + JSON.stringify(work));}
        return work;
    };

    // Reorders terms/variables so that they appear in first-used order.
    // Removes no-longer-used dummies. // TODO: remove from freemap
    // Renames remaining variable Skins to Vn
    // Consolidates and sort freelists
    // TODO: sort deps alphabetically
    module.exports.canonicalize = function(work) {
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
    };

})(module);
