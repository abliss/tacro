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
        work.FreeMap = fact.FreeMaps.slice(0, work.getCoreTermNames().length - 1);

    }
    work.Skin.HypNames = ["Hyps.0"];
    work.setProof(["Hyps.0"]);

    if (!work.Tree.Cmd) {
        work.setCmd("thm");
    }
    return work;
}


function verify(dump, goalMark, goalFp, solnNum) {
    var engine = new Engine();
        // TODO: the engine won't discover pushup theorems if they are added
        // before their respective detachers. Maybe we should have the gamestate
        // assign each mark an ordinal for when it was discovered?  For now we
        // just add everything twice, and hope nothing needs 2 other
        // dependencies to be added first.
    dump.deps.forEach(function(dep) {engine.onAddFact(new Fact(dep))});
    dump.deps.forEach(function(dep) {engine.onAddFact(new Fact(dep))});
    var work = engine.canonicalize(startWork(dump.goal));
    dump.steps.forEach(function(step, i) {
        step.args = step.args.map(function(arg){
            if (arg && arg.Core) {
                return new Fact(arg);
            } else {
                return arg;
            }
        });
        step.args.unshift(work);
        var canon;
        try {
            work = engine[step.func].apply(engine, step.args);
            //canon = engine.canonicalize(work)
            //Engine.verifyFact(canon);
        } catch(e) {
            if (!e.hasOwnProperty("definiens")) {
                console.error(`error with work after step ${i}: ` + JSON.stringify(work.Corel) + "\n canon: " + JSON.stringify(canon));
                throw e;
            }
        }
    });
    
    work = engine.canonicalize(work);
    Engine.verifyFact(work);
    engine.onAddFact(work);
    if (work.getMark() !== goalMark) {
        throw new Error(
            `mark mismatch: ${work.getMark()} !== ${goalMark}`);
    }
    solnNum = (solnNum > 0 ? "_"+solnNum : "");
    console.log(`${score}: Checked: ${work.getMark()} ${goalFp}${solnNum}`);
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

    land.goals.forEach((goal, stepNum)=>{
        goal.Core[Fact.CORE_HYPS]=[]; // remove hyps from defthms
        var goalMark = He.decode((new Fact(goal)).getMark());
        var goalFp = Engine.fingerprint(goalMark);
        var solns = [];
        ["","_1"].forEach((suffix) => {
            try {
                solns.push(Fs.readFileSync(`solutions/tacro-${goalFp}${suffix}.txt`,'utf8'));
            } catch (e) {
            }
        });
        if (solns.length == 0) {
            console.log(`${score}: Skipping ${goalMark} ${goalFp}`);
            skipped++;
        } else {
            solns.forEach(function(soln, solnNum) {
                try {
                    var soln = eval("("+soln+")");
                    soln.deps.forEach((dep)=>{
                        var mark = He.decode((new Fact(dep).getMark()));                        if (!marks[mark]) {
                            console.log("Missing mark: " + mark);
                            //throw new Error("unknown mark " + mark);
                        }
                    });
                    verify(soln, goalMark, goalFp, solnNum);
                } catch (e) {
                    e.message = `Checking ${goalFp} ${solnNum} step ${stepNum}` + e.message;
                    throw e;
                }
            });
        }
        marks[goalMark]=1;
        score++;
    });
}
/*
console.log(JSON.stringify(Engine.subTerms(["&rarr;","&exist;","&and;","&equals;","min","&forall;","&le;","&upsilon;","&sect;","&not;"].map(He.decode),
                [7,2,[5,0,[0,[6,[8,0],2],[9,1]]]])))
*/


var broken;
try {
    broken = Fs.readFileSync(`solutions/tacro-broken.txt`,'utf8');
} catch (e) {
    // no broken file
}
if (broken) {
    verify(JSON.parse(broken));
} else {
    Fs.readdirSync("../data/").forEach((filename)=>{
        console.log("==== " + filename + " ====");
        if (filename.startsWith("land_")) {
            check(getLand("../data/" + filename));
        }
    });
    console.log(`${skipped} skipped.`);
}
