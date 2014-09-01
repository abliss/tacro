// Hackish for now.
var Fact = require('./fact.js');
var Engine = require('./engine.js');
var Storage = require('./storage.js');

var storage = new Storage(Engine.fingerprint);
var log = {};
var state;
var lastStateFp = null;
var STATE_KEY = "lastState-v13";
var USERID_KEY = "tacro-userid";
var SIZE_MULTIPLIER = 3;
var urlNum = 0;
var selectedNode = null;
var workBox;
// ==== Stubs for node.js usage ====
if (typeof document == 'undefined') {
    function Node() {};
    Node.prototype = {
        style: {},
        appendChild: function(){},
        removeChild: function(){},
        sheet: { insertRule: function(){}},
    };

    document = {
        createElement:function() {return new Node();},
        getElementById:function() {return new Node();},
        createTextNode:function() {return new Node();},
        head: new Node(),
    };

    window = {
        addEventListener: function(){},
        location: {search: ""},
    };

    history = {
        pushState: function(){},
    }
}

// ==== END stubs ====

if (window.location.search.match("CLEAR")) {
    localStorage.clear();
}
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
        if (!termName) throw new Error("Bad term " + JSON.stringify(exp));
        var arity = exp.length - 1;
        var children = [];
        for (var i = 1; i <= arity; i++) {
            path.push(i);
            var subTree = makeTree(doc, fact, exp[i], path, arity, varNamer,
                                   spanMap, cb);
            subTree.span.className += " tool" + cssEscape(termName);
            spanMap[path] = subTree.span;
            children.push(subTree);
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
            //opSpan.href = "#" + tag + "=" + path;
            rowSpan.appendChild(children[0].span);
            rowSpan.appendChild(opSpan);
            path.push("0");
            spanMap[path] = opSpan;
            opSpan.onclick = cb(path);
            path.pop();
            opSpan.className += " operator " +" arity2";
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
            //opSpan.href = "#" + tag + "=" + path;
            termSpan.appendChild(opSpan);
            path.push("0");
            spanMap[path] = opSpan;
            opSpan.onclick = cb(path);
            path.pop();
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
        case 0:
            var opSpan = doc.createElement("a");
            //opSpan.href = "#" + tag + "=" + path;
            termSpan.appendChild(opSpan);
            path.push("0");
            spanMap[path] = opSpan;
            opSpan.onclick = cb(path);
            path.pop();
            opSpan.className += " operator arity1";
            var txtSpan = doc.createElement("span");
            opSpan.appendChild(txtSpan);
            opSpan.className += " txtBox";
            txtSpan.innerHTML = termName;
            txtSpan.className = " txt";
            width = 1;
            height = 1;
            opSpan.style.width = "100%";
            opSpan.style.height = "100%";
            break;
        default:
            console.log("TODO: XXX Only arity 0-2 supported:"+termName);
            throw new Error("TODO: XXX Only arity 0-2 supported: "+termName);
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
    var namer = newVarNamer();
    var tree = makeTree(document, fact, exp, [], -1, namer, spanMap, cb);
    termBox.appendChild(tree.span);
    tree.span.style.width = "100%";
    tree.span.style.height = "100%";
    termBox.style.width = "" + (2 * tree.width) + "em";
    termBox.style.height ="" + (2 * tree.height) + "em";
    termBox.spanMap = spanMap;
    spanMap[[]] = tree.span;
    termBox.tree = tree;
    
    var nullCb = function(){};
    fact.Core[Fact.CORE_FREE].forEach(function(fm) {
        var fmSpan = document.createElement("span");
        fmSpan.className = "freemap";
        termBox.appendChild(fmSpan);
        fm.forEach(function(v) {
            var vTree = makeTree(document, fact, v, [], -1, namer, {}, nullCb);
            fmSpan.appendChild(vTree.span);
        });
    });
    return termBox;
}


function size(thmBox, ems) {
    thmBox.style.width = ems + "em";
    thmBox.style.height = ems + "em";
    thmBox.tree.span.style["font-size"] = "" + (50 * ems / thmBox.tree.width) + "%";
}

function cssEscape(str) {
    // TODO: collisions
    return encodeURIComponent(str).replace(/%/g,"_");
}
function registerNewTool(toolOp) {
    var styleEl = document.createElement('style');
    // Apparently some version of Safari needs the following line? I dunno.
    styleEl.appendChild(document.createTextNode(''));
    document.head.appendChild(styleEl);
    var styleSheet = styleEl.sheet;
    for (var arg = 1; arg <= 2; arg++) {
        var rule = "#shooter.tool" + cssEscape(toolOp) + "_" + arg +
            " .depth1.input" + arg + "of2.tool" + cssEscape(toolOp) +
            " { border: 2px solid black; }";
        console.log("XXXX Inserting rule " + rule);
        styleSheet.insertRule(rule, 0);
    }

}

function addToShooter(factData, land) {
    if (!factData) {
        throw new Error("Bad fact: "+ factData);
    }
    if (!land) land = currentLand();
    var fact = Engine.canonicalize(new Fact(factData));
    var factFp = storage.fpSave("fact", fact);
    var newTool = Engine.onAddFact(fact);
    if (newTool) {
        registerNewTool(newTool);
    }
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
                        state.url = "#u=" + (urlNum++) + "/" +
                            "#f=" + path + ";" +
                            fact.Skin.Name;
                        /*
                        console.log("calling ground: " +
                                    JSON.stringify(state.work) +
                                    "\n" + JSON.stringify(fact) + "\n");
                        */
                        var thm = Engine.ground(state.work, fact);
                        var newFactFp = addToShooter(thm);
                        currentLand().thms.push(newFactFp);
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
    return factFp;
}


function workOnclickMaker(path) {
    var goalPath = path.slice();
    if (goalPath[goalPath.length-1] == 0) {
        goalPath.pop();
    }
    return function(e) {
        state.workPath = goalPath;
        // Highlight usable tools.
        // TODO: move this somewhere else
        var usableTools = Engine.getUsableTools(state.work, state.workPath);
        var className = "";
        for (var k in usableTools) if (usableTools.hasOwnProperty(k)) {
            var v = usableTools[k];
            className += " tool" + cssEscape(v[0]) + "_" + v[1];
        }
        document.getElementById("shooter").className = className;
        state.url = "#u=" + (urlNum++) + "/#g=" + goalPath;
        save();
        redrawSelection();
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
    var stateFp = storage.fpSave("state", state);
    if (stateFp != log.now) {
        var oldNow = log.now;
        log.now = stateFp;
        var logFp = storage.fpSave("log", log);
        log.parent = logFp;
        storage.local.setItem("childOf/" + oldNow, logFp);
        storage.local.setItem(STATE_KEY, logFp);
        if (storage.user) {
            storage.remote.child("users").child(storage.user.uid).
                child(STATE_KEY).set(logFp);
        }
        history.pushState(logFp, "state", "#s=" + stateFp + "/" + state.url);
    }
}

function currentLand() {
    return state.lands[state.lands.length-1];
}
function nextGoal() {
    var land = currentLand();
    var goal = land.goals.shift();
    if (!goal) {
        delete land.goals;
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

function redrawSelection() {
    if (selectedNode) {
        selectedNode.className += "NOT";
    }
    if (typeof state.workPath !== 'undefined') {
        selectedNode = workBox.spanMap[state.workPath];
        if (!selectedNode) {
            throw new Error("Selected node not found:" + state.workPath);
        }
        selectedNode.className += " selected";
    }
}
function redraw() {
    var well = document.getElementById("well");
    try {
        var box = makeThmBox(state.work,
                             state.work.Core[Fact.CORE_HYPS][0],
                             workOnclickMaker);
        size(box, box.tree.width * SIZE_MULTIPLIER);
        well.removeChild(well.firstChild);
        well.appendChild(box);
        workBox = box;
        redrawSelection();
    } catch (e) {
        message(e);
    }
}

function loadState(flat) {
    state = flat;
    state.work = new Fact(state.work);
    message("");
}

function loadLogFp(logFp, cb) {
    storage.fpLoad("log", logFp, function(logObj) {
        storage.fpLoad("state", logObj.now, function(stateObj) {
            log = logObj;
            loadState(stateObj);
            redraw();
            // TODO: should popstate? double-undo problem.
            history.pushState(logFp, "state",
                              "#s=" + logObj.now + "/" + state.url);
            document.getElementById("forward").style.visibility="visible";
            if (cb) {cb();}
        });
    });
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
            var factFp = addToShooter(data);
            land.thms.push(factFp);
        });
    }
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

function cheat(n) {
    while (n > 0) {
        var thm = new Fact(state.work);
        thm.Tree.Proof=[];
        thm.Tree.Cmd = 'stmt'
        thm.setHyps([]);
        var factFp = addToShooter(thm);
        currentLand().thms.push(factFp);
        message("");
        nextGoal();
        n--;
        redraw();
        save();
    }
}
function exportFacts() {

    console.log("==== EXPORT BEGIN ====");
    state.lands.forEach(function(land) {
        land.thms.forEach(function(thmFp) {
            var factData = storage.fpLoad("fact",thmFp);
            if (factData.length < 4000) {
                console.log("addFact(" + factData + ")");
            } else {
                console.log("addFact(" + factData.substring(0,4000));
                while (factData.length > 0) {
                    factData = factData.substring(4000);
                    console.log("        " + factData.substring(0, 4000));
                }
                console.log("      )");
            }
        });
    });
   
    console.log("==== EXPORT END ====");
}




window.addEventListener('popstate', function(ev) {
    console.log("popstate to " + ev.state);
    if (ev.state) {
        loadLogFp(ev.state);
    }
});
document.getElementById("rewind").onclick = function() {
    var parentFp = log.parent;
    if (parentFp) {
        loadLogFp(parentFp);
    }
    return false;
};
document.getElementById("forward").onclick = function() {
    var childLogFp = storage.local.getItem("childOf/" + log.now);
    if (childLogFp) {
        loadLogFp(childLogFp);
    } else {
        document.getElementById("forward").style.visibility="hidden";
    }
    return false;
};


function firebaseLoginLoaded() {
    console.log("Firebase Login loaded.");
    storage.authInit(FirebaseSimpleLogin, function(user) {
        if (user) {
            // user authenticated
            var loginNode = document.getElementById("login");
            loginNode.disabled = false;
            loginNode.innerText = user.displayName;
            loginNode.onclick = function() {
                storage.authLogout();
                return false;
            }
            storage.remote.child("users").child(user.uid).child(STATE_KEY).
                on('value', function(snap) {
                    var logFp = snap.val();
                    console.log("Found remote logFp: " + logFp);
                });
        } else {
            // user is logged out
            document.getElementById("login").innerText = "guest";
            resetLoginLink();
        }
    });
}


function resetLoginLink() {
    var link = document.getElementById("login");
    link.disabled = false;
    link.onclick = function() {
        storage.authLogin();
        return false;
    };
}

var landMap = {};
var landDepMap = {}; // XXX
var landPaneMap = {};
var currentPane;

var logFp = storage.local.getItem(STATE_KEY);
if (logFp) {
    loadLogFp(logFp, function() {
        state.lands.forEach(function(land) {
            addLandToUi(land);
            land.thms.forEach(function(thmFp) {
                storage.fpLoad("fact", thmFp, function(thmObj) {
                    addToShooter(thmObj, land);
                });
            });
        });
        if (window.location.search.match("CHEAT")) {
            cheat(1);
        }
    });
} else {
    state = {
        lands: [],
        url:"",
    };
}

storage.remoteGet("checked/lands", function(lands) {
    var numLands = 0;
    for (var n in lands) if (lands.hasOwnProperty(n)) {
        numLands++;
        land = JSON.parse(lands[n].land);
        landMap[land.name] = land;
        if (land.depends && land.depends.length > 0) {
            landDepMap[land.depends[0]] = land; // TODO: multidep
        } else {
            landDepMap[undefined] = land;
            if (!state) {
                state = {
                    lands:[],
                    url: "",
                }
            }
            if (state.lands.length == 0) {
                enterLand(land);
                nextGoal();
                state.url = "";
                save();
                redraw();
            }
        }
    }
    console.log("Got checked lands: " + numLands);
});
