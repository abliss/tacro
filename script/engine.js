'use strict';
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
Error.stackTraceLimit = Infinity;
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
        distributeMemo: {},
        toolsSeen: {},
        factsByMark:{},
        halfQueryPushUp: function(goalOp, goalArgNum) {
            var r = this.pushUpHalfMemo[[goalOp, goalArgNum]];
            return r || {};
        },
        /*
        query: [G, g, T, t] where G, T are ops, and g, t are arg nums
        Result: a PushUp wrapping a fact whose core stmt is of this form:
               [A,[T,a,b],
                  [P,[G, ..., a, ... ],
                     [G, ..., b, ... ]]]
        where A is a detachable arrow having an ax-mp equivalent (usually, -> or <->) exposed through the pushup
        and P is some "parent arrow", often the same as T (but not if crossing a kind boundary, e.g. T is = and G is < and P is <->)
        and g tells which arg of G changes.
        The above example is covariant; in a contravariant example, a and b would
        switch order in the consequent.
        It's also possible that [T,a,b] is actually [Forall,x, [T,a,b]] if there is a known ax-gen to "grease" the wheels.
        */
        queryPushUp:  function(query) { // [goalOp, goalArgNum, toolOp, toolArgNum]
            var pushUp = this.pushUpMemo[query];
            if (DEBUG) console.log("queryPushUp: " + JSON.stringify(query) + " => " +  JSON.stringify(pushUp ? pushUp.fact.Core[Fact.CORE_STMT] : null));
            if (!pushUp) {
                throw new Error("pushUp not found! Check commit d2a748c " +
                                "for how this used to work.");
            }
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
        },
        
        /*
         * Queries for a known distribution theorem of this form:
         * [A, [G,a,[U,b,c]],
         *     [U,[G,a,b],[G,a,c]]]
         * where A is a detachable arrow (typically, -> detached with axMp)
         *
         * @param gOp: which op maps to G
         * @param gArg: which arg of G varies in the consequent
         * @param uOp: which op maps to U
         * @param uArg: ignored???
         *
         *  TODO: support more than binary? Support mutated G in output?
         */
        queryDistribute: function(gOp, gArg, uOp, uArg) {
            var key = [gOp, gArg, uOp, uArg];
            var ret = this.distributeMemo[key];
            if (!ret) {
                throw new Error("No distribute for " + JSON.stringify(key));
            }
            return ret;
        }
    };

    function Arrow(name, arity, freeMap) {
        this.name = name;
        this.arity = arity;
        this.freeMap = freeMap;
    }

    function concatArr(arr1, arr2) {
        var out = (arr1 == undefined) ? [] : clone(arr1);
        out.push.apply(out, arr2);
        return out;
    }
    
   
    // A data structure for keeping in the scheme.
    // goalArrow wraps a goalOpArity-arg term.
    // goalArg is in 1...goalOpArity, specifying which argchild the goal is
    // toolArg is 1 or 2, specifying one of the args of the tool on the stack.
    // the current goal's parent's [goalArg] equals the current tool's [toolArg]
    // we want to replace it with the tool's other arg.
    // isCovar tells whether the tool args will be reversed in order.
    // An optional greasing function is allowed.
    // fact's root arg must be detachable by the provided axMp.
    function PushUp(detacher, goalArrow, goalArg, toolArg,
                    isCovar, parentArrow, grease, fact, isDistribute) {
        this.axMp = detacher.fact;
        this.goalArrow = goalArrow;
        this.goalArg = goalArg;
        this.toolArg = toolArg;
        this.isCovar = isCovar;
        this.parentArrow = parentArrow;
        this.grease = grease;
        this.fact = fact;
        this.isDistribute = isDistribute||false;

        if (isDistribute) {
            this.applyToPusp = applyDistributeToPusp;
        } else {
            this.applyToPusp = applyPushUpToPusp;
        }


        function assertEqual(msgTag, thing1, thing2) {
            if (JSON.stringify(thing1) !== JSON.stringify(thing2)) {
                throw new Error("Assertion error: " + msgTag +
                                "\nWant:  " + JSON.stringify(thing1) +
                                "\nHave:  " + JSON.stringify(thing2));
            }
        }

        function checkInvariant(pusp) {
            if (DEBUG) {
                console.log("Check invariant: " + JSON.stringify(zpath(pusp.goal, pusp.goalPath)));
                console.log("  pusp: ", JSON.stringify(pusp));
            }
            if (JSON.stringify(zpath(pusp.tool, pusp.toolPath)) !=
                JSON.stringify(zpath(pusp.goal, pusp.goalPath))) {
                throw new Error("Invariant broken!");
            }
        }

        /** 
         * Apply a distribute to the anchored tool, and detach the anchor from
         *  the work. Preconditions:
         *
         * 1. stack now has (a 1> (b 2> c))
         * 2. work subexp is the child of (a 1> c)
         * 3. my fact is ((a 1> (b 2> c)) 3> ((a 1> b) 4> (a 1> c)))
         * 4. my detacher detaches arrow 3>
         * 5. invariant holds
         *
         * Postconditions:
         * 1. work path is one shorter
         * 2. invariant holds.
         */
        function applyDistributeToPusp(pusp, work) {
            if (true || DEBUG) checkInvariant(pusp);
            var toolAnchor = zpath(pusp.tool, pusp.toolAnchorPath);
            var goalAnchor = zpath(pusp.goal, pusp.goalAnchorPath);

            var want = JSON.stringify(toolAnchor);
            var have = JSON.stringify(goalAnchor);
            if (want != have) {
                throw new Error("Anchor mismatch: want " + want + " = " + have);
            }
            if ((pusp.toolAnchorPath.length != 1) ||
                (pusp.toolAnchorPath[0] != 1)) {
                throw new Error("Fancy tool anchor not implemented");
            }

            var varMap = {0:zpath(pusp.tool, [1]),
                          1:zpath(pusp.tool, [2,1]),
                          2:zpath(pusp.tool, [2,2])};

            pusp.pushNewSteps("dist:", [
                varMap[0],
                varMap[1],
                varMap[2],
                nameDep(work, this.fact),
                nameDep(work, this.axMp)]);
            var subbed = globalSub(this.fact, varMap, work);
            var popped = pusp.stack.pop();
            assertEqual("stack dist", subbed[1], popped);
            pusp.stack.push(subbed[2]);

            pusp.goalPath.pop();
            var goalParent = zpath(pusp.goal, pusp.goalPath);
            var parentArrowN = work.nameTerm(this.parentArrow.name,
                                             this.parentArrow.freeMap);
            if (pusp.toolPath.length != 2 || pusp.toolPath[0] != 2) {
                throw new Error("TODO: Revisit assumption in next zpath");
            }
            var toolArg = pusp.toolPath[1];
            var goal = clone(zpath(pusp.goal, pusp.goalPath));
            var other = [goalParent[0],
                         toolAnchor,
                         zpath(pusp.tool, [2, 3-toolArg])];
            pusp.tool = [parentArrowN, null, null];
            pusp.tool[toolArg] = goal;
            pusp.tool[3-toolArg] = other;
            pusp.goalAnchorPath = undefined;
            pusp.toolAnchorPath = undefined;
            pusp.toolPath = [toolArg];
            if (true || DEBUG) checkInvariant(pusp);
        }

        // applies a single pushUp to a PushUpScratchPad and a
        // work-in-progress. This should perhaps move inside applyFact?  At the
        // beginning and at the end, our invariant holds: The tool's subexp at
        // toolPath (subexp A) must always equal the goal's subexp at goalPath
        // (subexp B). this remains true as we travel up the tree, popping off
        // the end of goalPath.
        function applyPushUpToPusp(pusp, work) {
            if (true || DEBUG) checkInvariant(pusp);
            // Prefix of toolPath the length of toolAnchorPath.  Points to the
            // "useful" part of the tool, i.e. the unanchored part.
            var toolPathPrefix = [];
            if (pusp.toolAnchorPath != undefined) {
                toolPathPrefix = pusp.toolPath.slice(
                    0, pusp.toolAnchorPath.length);
            }
            if (pusp.toolPath[pusp.toolPath.length - 1] != this.toolArg) {
                throw new Error("Unexpected toolArg: " + this.toolArg +
                                JSON.stringify(pusp));
            }
            var toolMandHyps = [
                zpath(pusp.tool, concatArr(toolPathPrefix,[1])),
                zpath(pusp.tool, concatArr(toolPathPrefix,[2]))];

            pusp.goalPath.pop();
            var goalParent = zpath(pusp.goal, pusp.goalPath);
            var goalN = work.nameTerm(this.goalArrow.name, 
                                      this.goalArrow.freeMap);
            var arr1 = [goalN]; // This one matches the goalExp
            var arr2 = [goalN]; // This one will replace the goalExp
            for (var i = 1; i < this.goalArrow.arity; i++) {
                if (i == this.goalArg) {
                    arr1.push(zpath(pusp.tool, pusp.toolPath));
                    arr2.push(zpath(pusp.tool, concatArr(toolPathPrefix, [3 - this.toolArg])));
                } else {
                    var arg = goalParent[i];
                    toolMandHyps.push(arg);
                    arr1.push(arg);
                    arr2.push(arg);
                }
            }
            pusp.pushNewSteps("tool mandhyps:", toolMandHyps);



            var greaseResult;
            if (this.grease) {
                greaseResult = this.grease(pusp, work);
            }
            pusp.pushNewSteps("pufact:", [nameDep(work, this.fact)]);
            if (true) {
                // TODO: should be more principled about this rather than
                // grovel about in newsteps for the mandhyps I just put
                // there. But it's tough to track them across a greasing,
                // so this will do for now.
                var numMandHyps = 0;
                var firstMandHyp = pusp.newSteps.length-1;
                var factStmt = this.fact.Core[Fact.CORE_STMT];
                eachVarOnce([factStmt], function() {numMandHyps++; firstMandHyp--});
                var varMap = {};
                for (var i = 0; i < numMandHyps; i++) {
                    varMap[i] = pusp.newSteps[firstMandHyp + i];
                }
                pusp.stack.push(globalSub(this.fact, varMap, work));
                if (DEBUG) console.log("  pusp: ", JSON.stringify(pusp));
            }
            var parentArrowN = work.nameTerm(this.parentArrow.name,
                                             this.parentArrow.freeMap);
            var nextTool = [parentArrowN,
                            this.isCovar ? arr2 : arr1,
                            this.isCovar ? arr1 : arr2];
            var nextToolArg = this.isCovar ? 2 : 1;
            var axMp = this.axMp;
            if (pusp.toolAnchorPath != undefined) {
                // If there's an anchor, we need to distribute it over the
                // parentArrow before we can axMp.
                if (pusp.toolAnchorPath.length != 1) {
                    throw new Error("Expected single depth anchor");
                }
                if (pusp.toolAnchorPath[0] != 1) {
                    console.warn("Non-1 anchorPath probably won't work.");
                }
                var toolAnchor = zpath(pusp.tool, pusp.toolAnchorPath);
                var dstGoalOp = work.Skin.TermNames[pusp.tool[0]];
                // If the anchor is the antecedent, then the thing that changes
                // in the goal is the consequent.
                var dstGoalArg = 3 - pusp.toolAnchorPath[0];
                var dstToolOp = this.axMp.Skin.TermNames[0]; // XXX should be?
                var dstToolArg = 2; // XXX Should be ?? 3-pusp.tap[0]
                var dstPU = scheme.queryPushUp([dstGoalOp, dstGoalArg, dstToolOp, dstToolArg]);
                if (dstGoalArg != 2) console.warn("pusp.tap[0] != 1");
                if (!dstPU.isCovar) console.warn("Non-covar dstPU");
                if (dstPU.grease) throw new Error("TODO handle");
                var step1 = zpath(pusp.tool, toolPathPrefix);
                if (greaseResult) {
                    step1 = [greaseResult.opNum, greaseResult.bindingVar, step1];
                }
                pusp.pushNewSteps("dstPU:", [
                    step1,
                    nextTool,
                    toolAnchor,
                    nameDep(work, dstPU.fact),
                    nameDep(work, dstPU.axMp)]);
                var subbed = globalSub(dstPU.fact, {0:step1, 1:nextTool ,2:toolAnchor}, work);
                var popped = pusp.stack.pop();
                assertEqual("stack dstPU", subbed[1], popped);
                pusp.stack.push(subbed[2]);
                if (DEBUG) console.log("  pusp: ", JSON.stringify(pusp));
                var dstParentArrowN = work.nameTerm(dstPU.parentArrow.name,
                                                    dstPU.parentArrow.freeMap);
                var newNextTool = [pusp.tool[0], // XXX Should be??
                            dstPU.isCovar ? toolAnchor : nextTool,
                            dstPU.isCovar ? nextTool : toolAnchor];
                var dstDetacher = scheme.queryDetach(
                    [dstPU.parentArrow.name, dstPU.isCovar? [2] : [1]]); //XXX should be??
                var topOfStack = [dstParentArrowN, // TODO: should be ?
                                  [pusp.tool[0],   // TODO: should be ?
                                   toolAnchor, step1],
                                  newNextTool];
                assertEqual("dst detach", topOfStack, pusp.stack.pop());
                var detached = dstDetacher.detach(topOfStack, work);
                pusp.pushNewSteps("detached:", detached.newSteps);
                var popped = pusp.stack.pop();
                assertEqual("dst detached", detached.result, popped);
                pusp.stack.push(detached.nowOnStack);
                nextTool = newNextTool;
            } else {
                pusp.pushNewSteps("axmp:", [nameDep(work, axMp)]);
                var top = pusp.stack.pop();
                var popped = pusp.stack.pop();
                // TODO: PICKUP: use detacher intrface instead
                if (DEBUG) console.log("  work: ", JSON.stringify(work));
                assertEqual("axmp", top[3-detacher.argNum], popped);
                pusp.stack.push(top[detacher.argNum]);
            }
            pusp.tool = nextTool;
            pusp.toolPath = concatArr(toolPathPrefix, [nextToolArg]);

            if (true || DEBUG) checkInvariant(pusp);
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
    // cb will be called with (var, pathFromRoot, Root)
    function eachVarOnce(exps, cb) {
        var seen = {};
        function visit(exp, path, root) {
            if (!Array.isArray(exp)) {
                if (!seen[exp]) {
                    seen[exp] = 1;
                    cb(exp, path, root);
                }
            } else {
                exp.slice(1).forEach((x, i) => {path.push(i+1); visit(x, path, root); path.pop();});
            }
        }
        exps.forEach(exp => visit(exp, [], exp));
    }

    // Visits each free var in each exp as many times as it appears, in left-to-right depth-first order
    // TODO: this is an error-prone api since exps will be confused for an exp
    // cb will be called with (var, bound, pathFromRoot, Root)
    function eachFreeVar(exps, freeMaps, cb) {
        // var -> number of levels bound
        var bound = {};
        function visit(exp, path, root) {
            if (!Array.isArray(exp)) {
                if (!bound[exp]) {
                    cb(exp, clone(bound), path, root);
                }
            } else {
                var freeMap = freeMaps[exp[0]];
                var bindingVar;
                var nonbindingArgNum;
                freeMap.forEach((bindingList,i) => {
                    if (Array.isArray(bindingList)) {
                        if (bindingVar != undefined) {
                            throw new Error("TODO: I don't yet support a term with multiple binding vars: " + exp[0]);
                        }
                        bindingVar = exp[i+1];
                        if (bindingList.length > 1) {
                            throw new Error("TODO: I don't yet support a bindingList with multiple entries: " + bindingList);
                        } else if (bindingList.length == 1) {
                            // TODO: test this codepath with [/]
                            nonbindingArgNum = bindingList[0];
                        }
                        if (!bound.hasOwnProperty(bindingVar)) {
                            bound[bindingVar] = 0;
                        }
                    }
                });
                exp.slice(1).forEach((x, i) => {
                    path.push(i+1);
                    if (i != nonbindingArgNum) bound[bindingVar]++;
                    visit(x, path, root);
                    if (i != nonbindingArgNum) bound[bindingVar]--;
                    path.pop();
                });
            }
        }
        exps.forEach(exp => visit(exp, [], exp));
    }
    // Reset the dummy counter to use the first available dummy not in optFact.
    function resetDummies(optFact) {
        dummyNum = 0;
        if (optFact && optFact.Skin.VarNames) {
            var usedVars = {};
            optFact.Skin.VarNames.forEach(v => { usedVars[v] = 1; });
            while (usedVars[newDummy()]) {
            }
            dummyNum--;
        }
    }
    function newDummy() {
        dummyNum++;
        //alpha is 03b1
        var codePoint = 0x03b0 + dummyNum;
        return String.fromCodePoint(codePoint);
        //return "DUMMY_" + dummyNum;
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
                while (!Array.isArray(x) && (dummyMap[x] != undefined)) {
                    x = dummyMap[x];
                }
                return Array.isArray(x) ? replaceDummies(x) : x;
            } else {
                throw new Error("hmm")
            }
        }
        if ((typeof workOrExp == 'number') || Array.isArray(workOrExp)) {
            return replaceDummies(workOrExp);
        } else if (workOrExp.ensureFree) {
            var oldFreeLists = workOrExp.Core[Fact.CORE_FREE];
            var freePairsToEnsure = [];
            oldFreeLists.forEach(function(freeList) {
                var oldTv = freeList[0];
                var newTerm = replaceDummies(oldTv);
                eachVarOnce([newTerm], function(newTermVar, pathFromRoot) {
                    freeList.slice(1).forEach(function(bv) {
                        var newBV = replaceDummies(bv);
                        if (Array.isArray(newBV)) {
                            throw new Error("Matched binding var " + bv + " to term " + JSON.stringify(newBV));
                        } else if (newBV == newTermVar) {
                            // TODO: check freemap
                            throw new Error("Freeness violation! Matched binding var " + bv + " to " + newBV + ";" +
                                            " matched term var " + oldTv + " at zpath " + JSON.stringify(pathFromRoot)
                                            + " in " + JSON.stringify(newTerm) + " to termVar " + newTermVar);
                        } else {
                            freePairsToEnsure.push([newTermVar, newBV]);
                        }
                    });
                });
            });
            workOrExp.setFree([]);
            // NOW we mutate the work. TOD: Still seems a bit early.
            freePairsToEnsure.forEach(pair => workOrExp.ensureFree(pair[0], pair[1]));

            workOrExp.Core[Fact.CORE_STMT] = replaceDummies(
                workOrExp.Core[Fact.CORE_STMT])
            workOrExp.Core[Fact.CORE_HYPS] =
                workOrExp.Core[Fact.CORE_HYPS].map(replaceDummies);
            workOrExp.Tree.Proof =
                workOrExp.Tree.Proof.map(replaceDummies);

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
    // specifying dummy vars and adding Free constraints. (TODO: not true!)
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
        var varMap = clone(optVarMap||{});
        var workExp = zpath(work.Core[Fact.CORE_HYPS][0], hypPath);
        var factExp = fact.Core[Fact.CORE_STMT];
        var factPath = stmtPath.slice();
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
                                "\nFactPath: " + factPath +
                                "\nWant:  " + JSON.stringify(thing1) +
                                " === " + JSON.stringify(thing2));
            }
        }

        function checkVarMapForFreeness(freeList) {
            var newExp = varMap[freeList[0]];
            if (newExp == undefined) {
                return;
            }
            var varsAppearing = {};
            eachFreeVar([newExp], work.FreeMaps, function(v, bound, pathFromRoot) {
                varsAppearing[v] = pathFromRoot.slice();
            });
            freeList.slice(1).forEach(function(freeVar) {
                var newVar = varMap[freeVar];
                if (newVar === undefined) {
                    throw new Error("Could not find var " + freeVar + 
                                    " in varMap " + JSON.stringify(varMap));
                } else if (Array.isArray(newVar)) {
                    // This should not be possible.
                    throw new Error("Substituting term " + JSON.stringify(newVar) + 
                                    " for binding var " + freeVar +
                                    " (was " + freeList[0] +")" +
                                    " in " + JSON.stringify(fact));
                }
                if (varsAppearing.hasOwnProperty(newVar)) {
                    throw new Error(
                        "Freeness Violation:\n  Found var " + newVar +
                            " (was " + freeVar +")\n free in exp " +
                            JSON.stringify(newExp) +
                            " (was " + freeList[0] +") at zpath " + 
                            JSON.stringify(varsAppearing[newVar]));
                }
            });
        }

        function mapVarTo(factVarName, workExp) {
            varMap[factVarName] = workExp;
        }
        function recurse(workSubExp, factSubExp, factSubPath, alreadyMapped) {
            if (!alreadyMapped && !Array.isArray(factSubExp) &&
                (varMap[factSubExp] != undefined)) {
                return recurse(workSubExp, varMap[factSubExp], factSubPath, true);
            }
            if (factSubPath.length > 0) {
                if (!Array.isArray(factSubExp)) {
                    throw new Error("fact path too long: " + factSubPath);
                }
                if (factSubExp.length <= factSubPath[0]) {
                    throw new Error("fact exp too short: " + JSON.stringify(factSubExp));
                }
                return recurse(workSubExp, factSubExp[factSubPath.shift()], factSubPath, alreadyMapped);
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
                        recurse(workSubExp[i], factSubExp[i], [], alreadyMapped);
                        debugPath.pop();
                    }
                }
            }
        }
        recurse(workExp, factExp, factPath, false);
        // XXX PICKUP: this mutates work despite our doc promising not to. Move it below cVMFF?
        undummy(work, dummyMap);
        //console.log("Unified: " + JSON.stringify(varMap));
        for (var x in varMap) if (varMap.hasOwnProperty(x)) {
            varMap[x] = undummy(varMap[x], dummyMap);
        }
        eachVarOnce([fact.Core[Fact.CORE_STMT]], function(v) {
            if (!varMap.hasOwnProperty(v)) {
                varMap[v] = work.nameVar(newDummy());
            }
        });
        fact.Core[Fact.CORE_FREE].forEach(checkVarMapForFreeness);

        return varMap;
    }

    // Returns an array of pushUps to push the given toolOp/toolArg up the tree
    // to the top, and a detacher to finish it off. Each pushUp can be passed to
    // applyPushUpToPusp along with (pusp, work).
    function getPushUps(work, workPath, toolOp, toolArg, goalAnchorPath) {
        // At each level of the goal tree, we need to query for and apply a
        // pushUp theorem.  However, in order to know *which* pushUp theorem to
        // apply, we need both the goal's operator at the level above, and the
        // result of the pushUp query from the level below.  Each query is
        // [goalOp, goalArgNum, toolOp, toolArgNum];

        var pushUps = [];
        var goalTerm = work.Core[Fact.CORE_HYPS][0];
        var myToolOp = toolOp;
        var myToolArg = toolArg;
        var anchorArrow = null;
        for (var workI = workPath.length - 1; workI >= 0; workI--) {
            var pathToParentOp = clone(workPath);
            pathToParentOp.splice(workI, workPath.length - workI, 0);
            var goalOp = work.Skin.TermNames[zpath(goalTerm, pathToParentOp)];
            var goalArg = workPath[workI];
            var pu;
            if ((goalAnchorPath != undefined) && (workI == goalAnchorPath.length - 1)) {
                
                // Work has: A ~ B
                // Now on the stack: A ~ (C > B) if myToolArg is  2, so
                // Distribute to: (A ~ C) > (A ~ B) and resume pushing
                // if myToolArg is 1,
                // Now on the stack: A ~ (B > C)
                // Distribute to: (A ~ B) > (A ~ C) and resume pushing
                pu = scheme.queryDistribute(goalOp, goalArg, myToolOp, myToolArg);
                if (pu.grease) {
                    throw new Error("TODO: handle greased distribute");
                }
                anchorArrow = goalOp;
                myToolArg = pu.isCovar ? myToolArg : 3 - myToolArg;
            } else {
                pu = scheme.queryPushUp([goalOp, goalArg, myToolOp, myToolArg]);
                if (DEBUG && (JSON.stringify([goalOp, goalArg, myToolOp, myToolArg]) ==
                              '["&exist;",2,"&harr;",1]')) {
                    console.log("XXXX Found distribute: " + (pu.grease ? 1 : 0));
                }
                myToolArg = (pu.isCovar ? 2 : 1);
            }
            pushUps.push(pu);
            myToolOp = pu.parentArrow.name;
        }

        // Now, since the invariant holds and goalPath = [], and
        // tool[toolPath[0]] == goal, so just detach.
        var detacher = scheme.queryDetach([myToolOp, [myToolArg]]);
        return {pushUps: pushUps,
                detacher: detacher,
                anchorArrow: anchorArrow
               };
    }
    
    // Returns an map of {k: [operatator, argNum, opaque]} describing which theorems,
    // given the current set of known pushUps, could be applied to the given
    // work at the given path.  If you want, you can pass the opaque part back
    // to applyFact to maybe speed things up?
    // TODO: add anchor support
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
    //
    // Optionally takes a varMap, which is a map from vars in the fact to target
    // vars in the work. If given, this will constrain the unification.
    //
    // Optionally takes a list of anchors. Here the semantics of anchors:
    //
    // #. If optAnchors is missing or empty, then factPath must be [1] or
    //    [2]. The fact must have a binary root. The subterm at workPath will be
    //    replaced with the other side of the fact (i.e. the subterm at [2] or
    //    [1], respectively).
    //
    // #. Otherwise: optAnchors must contain a single element, anchPath, a path
    //    to a subterm in the work, called the "anchor". factPath must be [a,b]
    //    where both a and b are 1 or 2. The fact's ops at [0] and at [a,0] must
    //    both be binary. The fact subterm at [2-a] will be unified with the
    //    anchor. The subterm at workPath will be replaced by the term at
    //    [a,2-b]. workPath and anchPath must have a common prefix P (possibly
    //    []) which points to a subterm with a binary op. anchPath must be P+[1]
    //    or P+[2].
    function applyFact(work, workPath, fact, factPath, optVarMap, optAnchors) {
        if (!Array.isArray(factPath)) {
            throw new Error("Bad factPath: " + JSON.stringify(factPath));
        }
        optAnchors = optAnchors || [];
        if (optAnchors.length == 0) {
            if ((factPath.length != 1) ||
                ((factPath[0] != 1) && (factPath[0] != 2))) {
                throw new Error("factPath must be [1] or [2] without anchor.");
            }
        } else if (optAnchors.length > 1) {
            throw new Error("Multiple anchors not implemented");
        } else if (!Array.isArray(optAnchors[0])) {
            throw new Error("Each anchor must be a zpath: " + JSON.stringify(optAnchors[0]));
        } else {
            if ((factPath.length != 2) ||
                ((factPath[0] != 1) && (factPath[0] != 2)) ||
                ((factPath[1] != 1) && (factPath[1] != 2))) {
                throw new Error("factPath must be [1|2, 1|2] with anchor.");
            }
            // TODO: more validation on anchor paths
        }
        if (!Array.isArray(workPath)) {
            throw new Error("Bad workPath " + workPath);
        }

        var anchorPath;
        var factAntecedentPath;
        if (optAnchors.length == 1) {
            anchorPath = optAnchors[0];
            factAntecedentPath = [3 - factPath[0]];
            optVarMap = getMandHyps(work, anchorPath, fact, factAntecedentPath,
                                    optVarMap);
        }
        /**
         * XXX Worked example of an anchor:
Fact: (1 a (2 b c))

conc: (3 a (4 c d))
hyp:  (3 a (4 b d))

steps:
hyp
;; (3 a (4 b d))
a b c fact
;; (3 a (4 b d))  (1 a (2 b c))
2x4x: (5 (2 A B) (6 (4 A C) (4 B C)))
b c d 2x4x
;; (3 a (4 b d))  (1 a (2 b c))  (5 (2 b c) (6 (4 b d) (4 c d)))
1y5y: (7 (5 A B) (8 (1 C A) (1 C B)))
(2 b c)  (6 (4 b d) (4 c d))  a  1y5y  mp7i    mp8i
;; (3 a (4 b d))  (1 a (6 (4 b d) (4 c d)))
1z6z: (9 (1 A (6 B C)) (10 (3 A B) (3 A C)))
a  (4 b d)  (4 c d)  1z6z  mp9i    mp10i
;; (3 a (4 c d))
*/
        var varMap = getMandHyps(work, workPath, fact, factPath, optVarMap);
        if (DEBUG) {console.log("# MandHyps: " + JSON.stringify(varMap));}
        // If that didn't throw, we can start mutating
        // PushUpScratchPad
        var pusp = {};
        pusp.newSteps = [];
        pusp.stack = []; // Only used for assertions
        pusp.pushNewSteps = function(debugTag, steps) {
            pusp.newSteps.push.apply(pusp.newSteps, steps);
            if (DEBUG) {
                console.log("Adding new steps " + debugTag + JSON.stringify(steps));
            }
        };

        if (DEBUG) console.log("Vars from " + JSON.stringify(fact));
        eachVarOnce([fact.Core[Fact.CORE_STMT]], function(v) {
            pusp.pushNewSteps("vars:",[varMap[v]]);
        });
        pusp.pushNewSteps("fact:", [nameDep(work, fact)]);

        // Now on the proof stack: an instance of fact, with factPath equalling
        // a subexp of work.

        // #. invoke sequence of pushup theorems, ensuring presence in Deps
        pusp.tool = globalSub(fact, varMap, work);       // what's on the stack
        pusp.stack.push(pusp.tool);
        pusp.toolPath = clone(factPath);                 // path to subexp A
        pusp.goal = clone(work.Core[Fact.CORE_HYPS][0]); // what to prove
        pusp.goalPath = clone(workPath);                 // path to subexp B
        pusp.toolAnchorPath = factAntecedentPath;
        pusp.goalAnchorPath = anchorPath;
        // invariant: subexp A == subexp B
        var toolOp = work.Skin.TermNames[
            (zpath(pusp.tool,
                   factPath.slice(0, factPath.length - 1)))[0]];
        var pushUps = getPushUps(work, workPath,
                                 toolOp, factPath[factPath.length - 1],
                                 pusp.goalAnchorPath);
        // Now apply the pushups from the bottom up, and finally detach.
        pushUps.pushUps.forEach(function(pu, index) {
            pu.applyToPusp(pusp, work);
        })
        var detachment = pushUps.detacher.detach(pusp.tool, work);
        pusp.pushNewSteps("detachment1:", detachment.newSteps);
        work.Core[Fact.CORE_HYPS][0] = detachment.result;
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
            if (DEBUG) {
                console.debug("Walking " + JSON.stringify(newExp) +
                              " to ensure these are not free in it:" + freeList.slice(1).map(x => varMap[x]));
            }
            eachFreeVar([newExp], work.FreeMaps, function(newV, bound) {
                freeList.slice(1).forEach(function(origBV) {
                    var bV = varMap[origBV];
                    if (newV == bV) {
                        // Shouldn't happen; this is checked for in mandHyps
                        throw new Error("Freeness violation!");
                    }
                    if (!bound[bV]) {
                        if (DEBUG) console.debug("  ensureFree " + newV);
                        work.ensureFree(newV, bV);
                    }
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
        var step0 = work.Tree.Proof.shift();
        if ("Hyps.0" != step0) { throw new Error("Expected proof to start with Hyps.0; got " + step0); }
        newSteps.unshift(step0);
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
                throw new Error("Missing FreeMap for term " + t + " in " + JSON.stringify(work));
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
                        var bVar = mapExp(v)
                        if (bVar == termVar) {
                            throw new Error("Freeness violation! bVar=" + bVar);
                        }
                        out.ensureFree(termVar, bVar);
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
        scheme.factsByMark[fact.getMark()] = fact;
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
                detach: function(tool, work) {
                    return {newSteps: [nameDep(work, this.fact)],
                            result: tool[1],
                            nowOnStack: tool[2]
                           };
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
                    detach: function(tool, work) {
                        return {newSteps: [tool[1],
                                           tool[2],
                                           nameDep(work, this.fact),
                                           nameDep(work, rarrAxmp.fact),
                                           nameDep(work, rarrAxmp.fact)],
                                result: tool[1],
                                nowOnStack: tool[2]};
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
                    detach: function(tool, work) {
                        return {newSteps: [tool[1],
                                           tool[2],
                                           nameDep(work, this.fact),
                                           nameDep(work, rarrAxmp.fact),
                                           nameDep(work, rarrAxmp.fact)],
                                result: tool[2],
                                nowOnStack: tool[1]};
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
            // Can't use pushUp theorems with hyps or free constraints.
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
            // with anything that can be detached. Detacher.detach() now returns
            // pusp.tool[1] instead of putting it directly into the hyps.
            return;
        }

        if (!Array.isArray(stmt[1]) ||
            (stmt[1].length != 3) || (stmt[1][1] != 0)) {
            // Antecedent must be a binary operation on two args
            return;
        }
        var anteArrow;
        var isDistribute = false;
        var anteArg1;
        var anteArg2;
        var greaser;

        if (!Array.isArray(stmt[2]) || (stmt[2].length != 3) ||
            (!Array.isArray(stmt[2][1])) || (!Array.isArray(stmt[2][2])) ||
            (stmt[2][1].length != stmt[2][2].length) ||
            (stmt[2][1][0] != stmt[2][2][0])
           ) {
            // Consequent must be an binary operation on two terms with
            // identical operations
            return;
        }

        if (stmt[1][2] == 1) {
            // This is a greaseless pushUp
            anteArrow = terms[stmt[1][0]];
            anteArg1 = 0;
            anteArg2 = 1;
        } else if (Array.isArray(stmt[1][2]) &&
                   (stmt[1][2].length == 3) &&
                   (stmt[1][2][1] == 1) &&
                   (stmt[1][2][2] == 2)) {
            // This could be a valid distribute and/or a "greased" antecedent
            if (greaser = scheme.greaseMemo[terms[stmt[1][0]]]) {
                // Handle greasing forall
                anteArrow = terms[stmt[1][2][0]];
                anteArg1 = 1;
                anteArg2 = 2;
                var childArity = stmt[2][1].length;
                // Need to figure out which arg of the child corresponds to the binding var in ax-gen.
                var bindingVar = stmt[1][1];
                var greasedArgOfChild = null;
                for (var arg = 1; arg < stmt[2][1].length; arg++) {
                    if (stmt[2][1][arg] == bindingVar) {
                        if (null !== greasedArgOfChild) {
                            throw new Error("Repeated binding var " + bindingVar + " in greasechild args");
                        }
                        greasedArgOfChild = arg;
                    }
                }
                if (null === greasedArgOfChild) {
                    throw new Error("Binding var " + bindingVar + " not found in greasechild args:" + JSON.stringify(stmt));
                }

                grease = function(pusp, work) {
                    var greaseOp = terms[stmt[1][0]];

                    // Assume the greased pushup is:
                    // (1. x (a 2> b)) 3> ((4. ... a ...) 5> (4. ... b ...))
                    // currently, (a 2> b) is on the proofstack.
                    // The newSteps ends with (a, b, ... ...).
                    var arr = pusp.newSteps;
                    // splice out the binding var, since it will need to move to the front of the mandhyps
                    var x = arr.splice(arr.length - childArity + greasedArgOfChild + 1,1)[0];
                    // need to scan back past all childArity args and a, b
                    var insertIndex = arr.length - (childArity - 2) - 1;
                    // insert the greaser step here, with x for its mandhyp
                    var greaseDep = nameDep(work, greaser.fact);
                    var stepsToInsert = [x, greaseDep];
                    var opNum = work.nameTerm(greaseOp,
                                              fact.FreeMaps[stmt[1][0]]);
                    pusp.stack.push([opNum, x, pusp.stack.pop()]);
                    if (pusp.toolAnchorPath != undefined) {
                        // grease must be distributed
                        // TODO: this is super fragile
                        var rarr = work.Skin.TermNames[pusp.tool[0]];
                        var axmp = nameDep(work, scheme.detachMemo[[rarr, [2]]].fact);
                        var mark = '[[],[0,[1,0,[0,1,2]],[0,[1,0,1],[1,0,2]]],[]];' +
                            JSON.stringify([rarr, greaseOp]);
                        var dist = scheme.factsByMark[mark];
                        if (!dist) throw new Error("No dist by mark " + mark);
                        var top = pusp.stack.pop();
                        stepsToInsert.push(
                            x,
                            top[2][1],
                            top[2][2],
                            nameDep(work, dist),
                            axmp);
                        mark = '[[],[0,0,[1,1,0]],[[0,1]]];' + JSON.stringify([rarr, greaseOp]);
                        var drop = scheme.factsByMark[mark];
                        if (!drop) throw new Error("No drop by mark " + mark);
                        eachFreeVar([top[2][1]], work.FreeMaps,
                                    function(newV, bound) {
                                        // TODO: what is bound?
                                        work.ensureFree(newV,x);
                                    });
                        // TODO: check anchor for freeness constraint
                        stepsToInsert.push(
                            top[2][1],
                            x,
                            nameDep(work, drop));

                        mark = '[[],[0,[0,0,1],[0,[0,1,2],[0,0,2]]],[]];' + JSON.stringify([rarr]);
                        var syl = scheme.factsByMark[mark];
                        if (!drop) throw new Error("No syl by mark " + mark);
                        stepsToInsert.push(
                            top[2][1],
                            [opNum, x, top[2][1]],
                            [opNum, x, top[2][2]],
                            nameDep(work, syl),
                            axmp, axmp
                        );
                        pusp.stack.push([pusp.tool[0],
                                         top[2][1],
                                         [top[0], top[1], top[2][2]]]);
                    }
                    stepsToInsert.push(x);
                    stepsToInsert.unshift(insertIndex, 0);
                    arr.splice.apply(arr,stepsToInsert);

                    if (DEBUG) console.log("adding grease step " + greaseDep + " at " + insertIndex + "; pusp now:" + JSON.stringify(pusp));
                    return {opNum: opNum, bindingVar: x};
                };
                grease.greasedArgOfChild = greasedArgOfChild;
            } else {
                // this is a Distribute, which can be used as the PushUp that detaches an anchor.
                // TODO: unify Distribute with Grease? is
                // a Greased thm basically just Distributing the implicit
                // universal quantifier?
                // TODO: fair to treat a Distribute as a PushUp?
                if ((stmt[1][0] != stmt[2][1][0]) ||
                    (stmt[1][0] != stmt[2][2][0])) {
                    console.log("TODO Fancy distribute not handled: " + JSON.stringify(fact));
                    return;
                }
                isDistribute = true;
                if (DEBUG){
                    console.log("Discovered distribute? " + JSON.stringify(fact));
                }
                anteArrow = terms[stmt[1][2][0]];
                anteArg1 = 1;
                anteArg2 = 2;
            }
        } else {
            // Not a valid pushUp
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
        if (DEBUG) {
            console.log("Discovered pushup: " + JSON.stringify([childArrow.name, whichArg, anteArrow, "*"]) +
                        " child=" + childArrow.name + "/" + whichArg + 
                        " ante=" + anteArrow + " isCov?" + isCov + " parent=" + parentArrow.name + " : " + JSON.stringify(fact.getMark()));
        }
        if (!isDistribute) {
            var halfMemo = scheme.pushUpHalfMemo[[childArrow.name, whichArg]];
            if (!halfMemo) {
                halfMemo = {};
                scheme.pushUpHalfMemo[[childArrow.name, whichArg]] = halfMemo;
            }
        }
        for (var i = 1; i <= 2; i++) {
            if (JSON.stringify([childArrow.name, whichArg, anteArrow, i]) ==
                '["&forall;",2,"&rarr;",1]XXX') {
                console.log("Discovered pushup: " + JSON.stringify([childArrow.name, whichArg, anteArrow, "*"]) +
                        " child=" + childArrow.name + "/" + whichArg + 
                            " ante=" + anteArrow + " isCov?" + isCov + " parent=" + parentArrow.name + " : " + JSON.stringify(fact.getMark())
                           + " grease=" + grease);
            }
            var pushUp = new PushUp(
                detacher, childArrow, whichArg, i,
                (isDistribute || i == 2) ? isCov : !isCov,
                parentArrow, grease, fact, isDistribute);
            if (isDistribute) {
                scheme.distributeMemo[[childArrow.name, whichArg, anteArrow, i]] = pushUp;
            } else {
                halfMemo[[anteArrow, i]] = [anteArrow, i];
                //console.log("pushup: " + [childArrow.name, whichArg, anteArrow, i] +
                //            " -> " + JSON.stringify(fact.getMark()));
                scheme.pushUpMemo[[childArrow.name, whichArg, anteArrow, i]] = pushUp;
            }
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
    module.exports.resetDummies = resetDummies;
    module.exports.DEBUG = function(d) {DEBUG = d;};
})(module);
