// Hackish for now.

var Fact = require('./fact.js');
var Engine = require('./engine.js');
var state = {};

function removeClass(node, className) {
    while (node.className.match(className)) {
        node.className = node.className.replace(className,'');
    }
}

function newVarNamer() {
    var names = ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L'];
    var map = {};
    return function(obj) {
        if (!map[obj]) {
            map[obj] = names.shift();
        }
        return map[obj];
    };
}

function makeTree(doc, fact, exp, path, inputTot, varNamer, spanMap, cb, tag) {
    var termSpan;
    spanMap[path] = termSpan;
    var width = 0;
    var height = 0;

    if (Array.isArray(exp)) {
		termSpan = doc.createElement("span");
        var termName = fact.Skin.TermNames[exp[0]];
        var arity = exp.length - 1;
        var children = [];
        for (var i = 1; i <= arity; i++) {
            path.push(i);
            children.push(makeTree(doc, fact, exp[i], path, arity, varNamer,
								   spanMap, cb, tag));
            path.pop();
        }
        switch (arity) {
        case 2:
            var rowSpan = doc.createElement("span");
            path.push("r");
            spanMap[path] = rowSpan;
            path.pop();
            termSpan.appendChild(rowSpan);
            rowSpan.className += " hyprow";
            var opSpan = doc.createElement("a");
            path.push("0");
            spanMap[path] = opSpan;
			opSpan.href = "#" + tag + "=" + path;
			opSpan.onclick = cb(path);
            path.pop();
            rowSpan.appendChild(children[0].span);
            rowSpan.appendChild(opSpan);
            opSpan.className += " operator";
            var txtSpan = doc.createElement("span");
            opSpan.appendChild(txtSpan);
            opSpan.className += " txtBox";
            txtSpan.innerHTML = termName;
            txtSpan.className = " txt";
            width = children[0].width + children[1].width;
            height = children[0].height + children[1].height;
            var opWidth = children[1].width;
            var opHeight = children[0].height;
            opSpan.style.height = "100%";
            children[0].span.style.height = "100%";
            rowSpan.style.height = "" + (100 * children[0].height / height) + "%";
            children[1].span.style.height = "" + (100 * children[1].height / height) + "%";

            rowSpan.style.width = "100%";
            children[0].span.style.width = "" + (100 * children[0].width / width) + "%";
            opSpan.style.width =  "" + (100 * children[1].width / width) + "%";
            children[1].span.style.width = opSpan.style.width;
            termSpan.appendChild(children[1].span);
            break;
        default:
            console.log("TODO: XXX Only arity 2 supported");
            throw new Error("TODO: XXX Only arity 2 supported");
        }
    } else {
		termSpan = doc.createElement("a");
		termSpan.href = "#" + tag + "=" + path;
		termSpan.onclick = cb(path);
        termSpan.className += " variable";
        termSpan.className += " var" + varNamer(exp);
        width = 1;
        height = 1;
        var txtSpan = doc.createElement("span");
        txtSpan.className = " txt";
        txtSpan.style.width="100%";
        txtSpan.style.height="100%";
        termSpan.appendChild(txtSpan);
        termSpan.className += " txtBox";
        var innerHTML = varNamer(exp);
        var whichChild = path[path.length - 1];
        for (var i = path.length  - 1; (i >= 0) && path[i] == whichChild; i--) {
            if (whichChild == 1) {
                innerHTML = innerHTML + ")";
            } else if (whichChild == 0) {
                innerHTML = "(" + innerHTML;
            }
        }
        txtSpan.innerHTML = innerHTML;
    }
    termSpan.className += " term";
    termSpan.className += " depth" + path.length;
    if (path.length > 0) {
        var inputNum = path[path.length - 1];
        termSpan.className += " input" + inputNum + "of" + inputTot;
    }
    return ({span:termSpan, width:width, height:height});
}

function makeThmBox(fact, exp, cb, tag) {
    var termBox = document.createElement("span");
    termBox.className += " termbox";
    var spanMap = {};
    var tree = makeTree(document, fact, exp, [], -1, newVarNamer(), spanMap,
						cb, tag);
    termBox.appendChild(tree.span);
    tree.span.style.width = "100%";
    tree.span.style.height = "100%";
    termBox.style.width = "" + (2 * tree.width) + "em";
    termBox.style.height ="" + (2 * tree.height) + "em";
    termBox.spanMap = spanMap;
    termBox.tree = tree;
    return termBox;
}


function size(thmBox, ems) {
    thmBox.style.width = ems + "em";
    thmBox.style.height = ems + "em";
    thmBox.tree.span.style["font-size"] = "" + (50 * ems / thmBox.tree.width) + "%";
}

function addToShooter(factData) {
	var fact = new Fact(factData);
	Engine.onAddFact(fact);
	if (fact.Core[Fact.CORE_HYPS].length == 0) {
		var box;
		var factOnclickMaker = function(path) {
			var factPath = path.slice();
			if (factPath[factPath.length-1] == 0) {
				factPath.pop();
			}
			return function() {
				try {
					if (state.workPath != null) {
						console.log("calling applyFact: " +
									JSON.stringify(state.work) + "\n" +
									JSON.stringify(state.workPath) + "\n" +
									JSON.stringify(fact) + "\n" +
									JSON.stringify(factPath) + "\n");
						state.work = Engine.applyFact(state.work,
													  state.workPath,
													  fact, factPath);
						delete state.workPath;
					} else if (factPath.length==0) {
						console.log("calling ground: " +
									JSON.stringify(state.work) + "\n" +
									JSON.stringify(fact) + "\n");
						var thm = Engine.ground(state.work, fact);
						addToShooter(thm);
						nextGoal();
					} else {
						console.log("wtf? " + JSON.stringify(factPath));
					}
				} catch (e) {
					console.log("Error in applyFact: " + e);
					console.log(e.stack);
				}
				redraw();
			};
		}
		box = makeThmBox(fact, fact.Core[Fact.CORE_STMT], factOnclickMaker,"f");
		size(box, 4);
		document.getElementById("shooterTape").appendChild(box);
	} // TODO: handle axioms with hyps
}

var allLands = require('./all_lands.js');
var landMap = {};
var landDepMap = {}; // XXX
allLands.forEach(function(land) {
	landMap[land.name] = land;
	landDepMap[land.depends[0]] = land;
});

state.land = landDepMap[undefined];
state.land.axioms.forEach(addToShooter);


function workOnclickMaker(path) {
	var goalPath = path.slice();
	if (goalPath[goalPath.length-1] == 0) {
		goalPath.pop();
	}
	return function() {
		state.workPath = goalPath;
	}
};

function startWork(fact) {
    var work = new Fact(fact);
    work.setHyps([work.Core[Fact.CORE_STMT]]);
    work.Skin.HypNames = ["Hyps.0"];
    if (!work.Tree.Cmd) {
        work.setCmd("thm");
    }
    work.setProof(["Hyps.0"]);
    return Engine.canonicalize(work);
}

function nextGoal() {
	state.goalNum++;
	if (state.goalNum >= state.land.goals.length) {
		alert("no more goals");
		//TODO: load next land
	} else {
		state.work = startWork(state.land.goals[state.goalNum]);
	}
}

function redraw() {
	var well = document.getElementById("well");
	well.removeChild(well.firstChild);
	console.log("Redrawing: " + JSON.stringify(state.work));
	var box = makeThmBox(state.work,
						 state.work.Core[Fact.CORE_HYPS][0],
						 workOnclickMaker,
						 "g");
	size(box, box.tree.width * 2);
	well.appendChild(box);
}


state.goalNum = -1;
nextGoal();

redraw();
