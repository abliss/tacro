// Hackish for now.

var Fact = require('./fact.js');
var Engine = require('./engine.js');
var state;
var stateHash;
var STATE_KEY = "lastState-v12";
var SIZE_MULTIPLIER = 3;
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
        /*
        if (!map[obj]) {
            map[obj] = names.shift();
        }
        return map[obj];
        */
        return names[obj];
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
            opSpan.className += " operator arity2";
            var txtSpan = doc.createElement("span");
            opSpan.appendChild(txtSpan);
            opSpan.className += " txtBox";
            txtSpan.innerHTML = termName;
            txtSpan.className = " txt";
            width = children[0].width + children[1].width;
            height = children[0].height + children[1].height;
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
        case 1:
            var opSpan = doc.createElement("a");
            path.push("0");
            spanMap[path] = opSpan;
            //opSpan.href = "#" + tag + "=" + path;
            opSpan.onclick = cb(path);
            path.pop();
            termSpan.appendChild(opSpan);
            opSpan.className += " operator arity1";
            var txtSpan = doc.createElement("span");
            opSpan.appendChild(txtSpan);
            opSpan.className += " txtBox";
            txtSpan.innerHTML = termName;
            txtSpan.className = " txt";
            width = 1 + children[0].width;
            height = 1 + children[0].height;
            opSpan.style.width = "100%";
            opSpan.style.height = "" + (100 / height) + "%";
            children[0].span.style.height = "" + (100 * children[0].height / height) + "%";
            children[0].span.style.width = "" + (100 * children[0].width / width) + "%";

            termSpan.appendChild(children[0].span);
            break;
        default:
            console.log("TODO: XXX Only arity 1-2 supported:"+termName);
            throw new Error("TODO: XXX Only arity 1-2 supported: "+termName);
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

function addToShooter(factData, land) {
    if (!land) land = currentLand();
    var fact = Engine.canonicalize(new Fact(factData));
    localStorage.setItem(fact.Skin.Name, JSON.stringify(fact));
    Engine.onAddFact(fact);
    switch (fact.Core[Fact.CORE_HYPS].length) {
    case 0:
        var box;
        var factOnclickMaker = function(path) {
            var factPath = path.slice();
            if (factPath[factPath.length-1] == 0) {
                factPath.pop();
            }
            switch (factPath.length) {
            case 0:
                return function(ev) {
                    try {
                        state.url = "#f=" + path + ";" + fact.Skin.Name;
                        console.log("calling ground: " +
                                    JSON.stringify(state.work) + "\n" +
                                    JSON.stringify(fact) + "\n");
                        var thm = Engine.ground(state.work, fact);
                        var newFact = addToShooter(thm);
                        currentLand().thms.push(newFact.Skin.Name);
                        message("");
                        nextGoal();
                    } catch (e) {
                        console.log("Error in ground: " + e);
                        console.log(e.stack);
                        message(e);
                    }
                    redraw();
				    ev.stopPropagation()
                };
            case 1:
                return function(ev) {
                    try {
                        setWork(Engine.applyFact(state.work,
                                                 state.workPath,
                                                 fact, factPath));
                        message("");
                        delete state.workPath;
                        state.url = "";
                    } catch (e) {
                        console.log("Error in applyFact: " + e);
                        console.log(e.stack);
                        message(e);
                    }
                    redraw();
				    ev.stopPropagation()
                };
            default:
                // Don't bother clickifying these; engine doesn't support
                return null;
            }
        };
        box = makeThmBox(fact, fact.Core[Fact.CORE_STMT], factOnclickMaker);
        size(box, 2 * SIZE_MULTIPLIER);
        landPaneMap[land.name].appendChild(box);
        break;
    case 1:
        // Adding generify to the shooter
        var box;
        var factOnclickMaker = function(path) {
            return null;
        };
        var hyp0box = makeThmBox(fact, fact.Core[Fact.CORE_HYPS][0], factOnclickMaker);
        var stmtbox = makeThmBox(fact, fact.Core[Fact.CORE_STMT], factOnclickMaker);
        size(hyp0box, 2 * SIZE_MULTIPLIER);
        size(stmtbox, 2 * SIZE_MULTIPLIER);
        landPaneMap[land.name].appendChild(hyp0box);
        hyp0box.appendChild(stmtbox);
        hyp0box.onclick = function(ev) {
            try {
                setWork(Engine.applyInference(state.work, fact));
                message("");
                delete state.workPath;
                state.url = "";
            } catch (e) {
                console.log("Error in applyInference: " + e);
                console.log(e.stack);
                message(e);
            }
            redraw();
			ev.stopPropagation()
        };
        break;
    default:
        console.log("Skipping inference: " + JSON.stringify(fact.Core));
    } // TODO: handle axioms with hyps
    return fact;
}


function workOnclickMaker(path) {
    var goalPath = path.slice();
    if (goalPath[goalPath.length-1] == 0) {
        goalPath.pop();
    }
    return function(e) {
        state.workPath = goalPath;
        state.url = "#g=" + goalPath;
        save();
		e.stopPropagation();
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
    var hash = Engine.fingerprint(state);
    if (hash != stateHash) {
        localStorage.setItem(hash, JSON.stringify(state));
        localStorage.setItem(STATE_KEY, hash);
        localStorage.setItem("parentOf-" + hash, stateHash);
        localStorage.setItem("childOf-" + stateHash, hash);
        console.log("XXXX Setting " + "childOf-" + stateHash + " = " + hash);
        stateHash = hash;
        history.pushState(state, "state", "#s=" + hash + state.url);
    }
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
            return nextGoal();
        } else {
            message("No more lands! You win! Now go write a land.");
        }
    }
    state.work = startWork(goal);
    save();
    return goal;
}

function redraw() {
    var well = document.getElementById("well");
    console.log("Redrawing: " + JSON.stringify(state.work));
    try {
        var box = makeThmBox(state.work,
                             state.work.Core[Fact.CORE_HYPS][0],
                             workOnclickMaker);
        size(box, box.tree.width * SIZE_MULTIPLIER);
        well.removeChild(well.firstChild);
        well.appendChild(box);
    } catch (e) {
        message(e);
    }
}

function loadState(flat) {
    state = flat;
    state.work = new Fact(state.work);
    message("");
}

function enterLand(landData) {
    var land = {
        name:landData.name,
        thms:[],             // hash values
        goals:[],            // structs
    };
    state.lands.push(land);
    addLandToUi(land);
    land.goals = landData.goals.slice();
	if (landData.axioms) {
		landData.axioms.forEach(function(data) {
			var fact = addToShooter(data);
			land.thms.push(fact.Skin.Name);
		});
	}
    currentLand().thms.push.apply(currentLand(), landData.axioms);
}

function addLandToUi(land) {
    var tab = document.createElement("button");
    document.getElementById("shooterTabs").appendChild(tab);
    tab.className = "tab";
    tab.innerHTML = land.name.replace(/[<]/g,"&lt;");
    var pane = document.createElement("span");
    document.getElementById("shooterTape").appendChild(pane);
    landPaneMap[land.name] = pane;
    pane.className = "pane pane" + land.name;
    tab.onclick = function() {
        if (currentPane) {currentPane.style.display="none";}
        pane.style.display="inline-block";
        currentPane = pane;
    };
    tab.onclick();
}

function message(msg) {
    if (msg) {console.log("Tacro: " + msg);}
    document.getElementById("message").innerText = msg;
}

var allLands = require('./all_lands.js');
var landMap = {};
var landDepMap = {}; // XXX
var landPaneMap = {};
var currentPane;

allLands.forEach(function(land) {
    landMap[land.name] = land;
    landDepMap[land.depends[0]] = land;
});


window.addEventListener('popstate', function(ev) {
    console.log("popstate to " + ev.state);
    if (ev.state) {
        loadState(ev.state);
        save();
        redraw();
    }
});
document.getElementById("rewind").onclick = function() {
    var parentHash = localStorage.getItem("parentOf-" + stateHash);
    console.log("XXXX Rewinding from " + stateHash + "  to " + parentHash);
    if (parentHash) {
        loadState(JSON.parse(localStorage.getItem(parentHash)));
        stateHash = parentHash;
        redraw();
        // Don't save() or we'll get stuck in a loop
        document.getElementById("forward").style.visibility="visible";
    }
    return false;
};
document.getElementById("forward").onclick = function() {
    var childHash = localStorage.getItem("childOf-" + stateHash);
    console.log("XXXX Forwarding from " + stateHash + " to " + childHash);
    if (childHash) {
        loadState(JSON.parse(localStorage.getItem(childHash)));
        stateHash = childHash;
        redraw();
        // Don't save() or we'll get stuck in a loop
    } else {
        document.getElementById("forward").style.visibility="hidden";
    }
    return false;
}
var stateHash = localStorage.getItem(STATE_KEY);
if (stateHash) {
    loadState(JSON.parse(localStorage.getItem(stateHash)));
    state.lands.forEach(function(land) {
        console.log("Processing land " + land.name + " #" + land.thms.length);
        addLandToUi(land);
        land.thms.forEach(function(thmName) {
            var factData = JSON.parse(localStorage.getItem(thmName));
            //console.log("adding " + thmName + "=" + JSON.stringify(factData));
            var fact = addToShooter(factData, land);
        })
    });
} else {
    state = {
        lands: [],
        url:"",
    };
    var firstLand = landDepMap[undefined]; // XXX
    enterLand(firstLand);
    nextGoal();
    state.url = "";
}

function cheat(n) {
    while (n > 0) {
        var thm = new Fact(state.work);
        thm.Tree.Proof=[];
        thm.Tree.Cmd = 'stmt'
        thm.setHyps([]);
        var newFact = addToShooter(thm);
        currentLand().thms.push(newFact.Skin.Name);
        message("");
        nextGoal();
        n--;
        redraw();
        save();
    }
}
save();
redraw();
