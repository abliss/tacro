// Hackish for now.

var Fact = require('./fact.js');
var Engine = require('./engine.js');
var state;
var STATE_KEY = "lastState-v05";

// ==== Stubs for node.js usage ====
if (typeof document == 'undefined') {
	function Node() {};
	Node.prototype = {
		style: {},
		appendChild: function(){},
		removeChild: function(){},
	};

	document = {
		createElement:function() {return new Node();},
		getElementById:function() {return new Node();},
	};

	window = {
		addEventListener: function(){},
	};

	history = {
		pushState: function(){},
	}
}

if (typeof localStorage === "undefined" || localStorage === null) {
  var LocalStorage = require('node-localstorage').LocalStorage;
  localStorage = new LocalStorage('./scratch');
}

// ==== END stubs ====

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

function makeTree(doc, fact, exp, path, inputTot, varNamer, spanMap, cb) {
    var termSpan;
    spanMap[path] = termSpan;
    var width = 0;
    var height = 0;

    if (Array.isArray(exp)) {
		termSpan = doc.createElement("span");
        var termName = fact.Skin.TermNames[exp[0]];
		if (!termName) throw new Error("Bad term " + exp);
        var arity = exp.length - 1;
        var children = [];
        for (var i = 1; i <= arity; i++) {
            path.push(i);
            children.push(makeTree(doc, fact, exp[i], path, arity, varNamer,
								   spanMap, cb));
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
			//opSpan.href = "#" + tag + "=" + path;
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
            console.log("TODO: XXX Only arity 2 supported:" + termName);
            throw new Error("TODO: XXX Only arity 2 supported: " + termName);
        }
    } else {
		termSpan = doc.createElement("a");
		//termSpan.href = "#" + tag + "=" + path;
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

function makeThmBox(fact, exp, cb) {
    var termBox = document.createElement("span");
    termBox.className += " termbox";
    var spanMap = {};
    var tree = makeTree(document, fact, exp, [], -1, newVarNamer(), spanMap,
						cb);
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
	var fact = Engine.canonicalize(new Fact(factData));
	localStorage.setItem(fact.Skin.Name, JSON.stringify(fact));
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
					state.url = "#f=" + path + ";" + fact.Skin.Name;
					if (state.workPath != null) {
						console.log("calling applyFact: " +
									JSON.stringify(state.work) + "\n" +
									JSON.stringify(state.workPath) + "\n" +
									JSON.stringify(fact) + "\n" +
									JSON.stringify(factPath) + "\n");
						setWork(Engine.applyFact(state.work,
												 state.workPath,
												 fact, factPath));
						delete state.workPath;
						state.url = "";
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
					alert(e);
				}
				redraw();
			};
		}
		box = makeThmBox(fact, fact.Core[Fact.CORE_STMT], factOnclickMaker);
		size(box, 4);
		document.getElementById("shooterTape").appendChild(box);
		currentLand().thms.push(fact.Skin.Name);
	} // TODO: handle axioms with hyps
}


function workOnclickMaker(path) {
	var goalPath = path.slice();
	if (goalPath[goalPath.length-1] == 0) {
		goalPath.pop();
	}
	return function() {
		state.workPath = goalPath;
		state.url = "#g=" + goalPath;
		save();
	}
}

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

function setWork(work) {
	state.work = work;
	state.workHash = Engine.fingerprint(work);
	save();
}

function save() {
	var lastHash = state.lastHash || "";
	delete state.lastHash;
	var hash = Engine.fingerprint(state);
	localStorage.setItem(hash, JSON.stringify(state));
	localStorage.setItem(STATE_KEY, hash);
	localStorage.setItem("parentOf-" + hash, lastHash);
	state.lastHash = hash;
	history.pushState(state, "state", "#s=" + hash + state.url);
}

function currentLand() {
	return state.lands[state.lands.length-1];
}
function nextGoal() {
	var land = currentLand();
	var goal = land.goals.shift();
	if (!goal) {
		var nextLand = landDepMap[land.name]; // XXX
		if (nextLand) {
			enterLand(nextLand);
			goal = nextGoal();
		} else {
			alert("No more lands! You win! Now go write a land.");
		}
	}
	state.work = startWork(goal);
	save();
}

function redraw() {
	var well = document.getElementById("well");
	well.removeChild(well.firstChild);
	console.log("Redrawing: " + JSON.stringify(state.work));
	var box = makeThmBox(state.work,
						 state.work.Core[Fact.CORE_HYPS][0],
						 workOnclickMaker);
	size(box, box.tree.width * 2);
	well.appendChild(box);
}

function loadState(flat) {
	state = flat;
	state.work = new Fact(state.work);
}

function enterLand(landData) {
	var land = {
		name:landData.name,
		thms:[],             // hash values
		goals:[],            // structs
	};
	state.lands.push(land);
	land.goals = landData.goals.slice();
	landData.axioms.forEach(addToShooter);
}

var allLands = require('./all_lands.js');
var landMap = {};
var landDepMap = {}; // XXX
allLands.forEach(function(land) {
	landMap[land.name] = land;
	landDepMap[land.depends[0]] = land;
});


window.addEventListener('popstate', function(ev) {
	console.log("popstate to " + ev.state);
	if (ev.state) {
		loadState(ev.state);
		redraw();
	}
});
var stateHash = localStorage.getItem(STATE_KEY);
if (stateHash) {
	loadState(JSON.parse(localStorage.getItem(stateHash)));
	state.lands.forEach(function(land) {
		console.log("Processing land " + land.name);
		land.thms.forEach(function(thmName) {
			var factData = JSON.parse(localStorage.getItem(thmName));
			console.log("adding " + thmName + "=" + JSON.stringify(factData));
			addToShooter(factData);
		})
	});
} else {
	state = {
		lands: [],
	};
	var firstLand = landDepMap[undefined]; // XXX
	enterLand(firstLand);
	nextGoal();
	state.url = "";
}

save();
redraw();
