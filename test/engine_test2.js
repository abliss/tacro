var Fact = require('../script/fact.js');
var Engine = require('../script/engine.js');
var Fs = require('fs');
var He = require('he');
var marks = {};
var score = 0;
var skipped = 0;
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
    var engine = new Engine();
        // TODO: the engine won't discover pushup theorems if they are added
        // before their respective detachers. Maybe we should have the gamestate
        // assign each mark an ordinal for when it was discovered?  For now we
        // just add everything twice, and hope nothing needs 2 other
        // dependencies to be added first.
    dump.deps.forEach(function(dep) {engine.onAddFact(new Fact(dep))});
    dump.deps.forEach(function(dep) {engine.onAddFact(new Fact(dep))});
    var work = engine.canonicalize(startWork(dump.goal));
    dump.steps.forEach(function(step) {
        step.args = step.args.map(function(arg){
            if (arg && arg.Core) {
                return new Fact(arg);
            } else {
                return arg;
            }
        });
        step.args.unshift(work);
        work = engine[step.func].apply(engine, step.args);
     });
    work.verify();
    engine.onAddFact(work);
    console.log(`${score}: Checked: ${work.getMark()}`);
}

function getLand(filename) {
    // Uses eval instead of json to allow comments and naked keys.
    // This is almost certainly a terrible idea.
    return eval("("+Fs.readFileSync(filename,'utf8')+")");
}

function check(land) {
    (land.axioms||[]).forEach((ax)=>{
        var mark = He.decode(new Fact(ax).getMark());
        marks[mark] = 1;
    });

    land.goals.forEach((goal)=>{
        var goalMark = He.decode((new Fact(goal)).getMark());
        var goalFp = Engine.fingerprint(goalMark);
        var soln;
        try {
            soln = Fs.readFileSync(`solutions/tacro-${goalFp}.txt`,'utf8');
        } catch (e) {
            console.log(`${score}: Skipping ${goalMark}`);
            skipped++;
        }
        if (soln) {    
            var soln = eval("("+soln+")");
            soln.deps.forEach((dep)=>{
                var mark = (new Fact(dep).getMark());
                if (!marks[mark]) {
                    throw new Error("unknown mark " + mark);
                }
            });
            verify(soln);
        }
        marks[goalMark] = 1;
        score++;
        
    });
}

if (true) {
    Fs.readdirSync("../data/").forEach((filename)=>{
        console.log("==== " + filename + " ====");
        if (filename.startsWith("land_")) {
            check(getLand("../data/" + filename));
        }
    });
    console.log(`${skipped} skipped.`);
}

