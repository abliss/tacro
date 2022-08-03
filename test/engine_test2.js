var Fact = require('../script/fact.js');

function startWork(fact) {

    var work = new Fact(fact);
    if (work.Core[Fact.CORE_HYPS].length == 0) {
        work.setHyps([work.Core[Fact.CORE_STMT]]);
    }
    work.FreeMap = fact.FreeMaps.slice(0, work.getCoreTermNames().length - 1);
    work.Skin.HypNames = ["Hyps.0"];
    work.setProof(["Hyps.0"]);

    if (!work.Tree.Cmd) {
        work.setCmd("thm");
    }
    return work;
}


function verify(dump) {
    var Engine = require('../script/engine.js');
    dump.deps.forEach(function(dep) {Engine.onAddFact(new Fact(dep))});
    var work = Engine.canonicalize(startWork(dump.goal));
    dump.steps.forEach(function(step) {
        step.args = step.args.map(function(arg){
            if (arg && arg.Core) {
                return new Fact(arg);
            } else {
                return arg;
            }
        });
        step.args.unshift(work);
        work = Engine[step.func].apply(Engine, step.args);
    });
    work.verify();
    Engine.onAddFact(work);
    console.log("Checked " + work.getMark());
}

verify({"goal":{"Core":[[],[0,0,[0,0,0]],[]],"Skin":{"TermNames":["→"]},"FreeMaps":[[]]},"steps":[{"func":"applyFact","args":[[],{"Core":[[],[0,0,[0,1,0]],[]],"Skin":{"TermNames":["→"]},"FreeMaps":[[]]},[2],{"0":[0,0,0],"1":0,"2":0,"3":0},null]},{"func":"ground","args":[{"Core":[[],[0,0,0],[]],"Skin":{"TermNames":["→"]},"FreeMaps":[[]]}]}],"deps":[{"Core":[[],[0,0,[0,1,0]],[]],"Skin":{"TermNames":["→"]},"FreeMaps":[[]]},{"Core":[[0,[0,0,1]],1,[]],"Skin":{"TermNames":["→"]},"FreeMaps":[[]]},{"Core":[[],[0,0,0],[]],"Skin":{"TermNames":["→"]},"FreeMaps":[[]]}]});

verify({"goal":{"Core":[[],[0,0,[0,0,0]],[]],"Skin":{"TermNames":["→"]},"FreeMaps":[[]]},"steps":[{"func":"applyFact","args":[[],{"Core":[[],[0,0,[0,1,0]],[]],"Skin":{"TermNames":["→"]},"FreeMaps":[[]]},[2],{"0":[0,0,0],"1":0,"2":0,"3":0},null]},{"func":"applyFact","args":[[],{"Core":[[],[0,[0,0,1],[0,[0,1,2],[0,0,2]]],[]],"Skin":{"TermNames":["→"]},"FreeMaps":[[]]},[2],{"0":1,"1":[0,0,1],"2":2,"3":0,"4":1},null]},{"func":"ground","args":[{"Core":[[],[0,0,0],[]],"Skin":{"TermNames":["→"]},"FreeMaps":[[]]}]}],"deps":[{"Core":[[],[0,[0,0,1],[0,[0,1,2],[0,0,2]]],[]],"Skin":{"TermNames":["→"]},"FreeMaps":[[]]},{"Core":[[0,[0,0,1]],1,[]],"Skin":{"TermNames":["→"]},"FreeMaps":[[]]},{"Core":[[],[0,0,[0,1,0]],[]],"Skin":{"TermNames":["→"]},"FreeMaps":[[]]},{"Core":[[],[0,0,0],[]],"Skin":{"TermNames":["→"]},"FreeMaps":[[]]}]});
