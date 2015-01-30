// Hackish for now.
var Fact = require('./fact.js');
var Engine = require('./engine.js');
var Storage = require('./storage.js');
var Move = require('./move.js');
var TreeMaker = require('./treeMaker.js');

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
var factToShooterBox = {};
var deferredUntilRedraw = [];
var landMap = {};
var landDepMap = {}; // XXX
var currentPane;


Error.stackTraceLimit = Infinity;
function fbEscape(str) {
    return encodeURIComponent(str).replace(/\./g,"%2E");
}

var varColors = [
    "#9370db",
    "#70db93",
    "#f13e44",
    "#cc4a14",
    "#99583d",
    "#3d983d",
    "#3d9898",
];


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


function makeThmBox(fact, exp, cb) {
    var termBox = document.createElement("span");
    termBox.className += " termbox";
    var tree = TreeMaker({
        fact: fact,
        exp: exp,
        callback: cb
    });
    termBox.appendChild(tree);
    termBox.spanMap = tree.spanMap;
    termBox.tree = tree;
    /*
    var nullCb = function(){};
    fact.Core[Fact.CORE_FREE].forEach(function(fm) {
        var fmSpan = document.createElement("span");
        fmSpan.className = "freemap";
        termBox.appendChild(fmSpan);
        fm.forEach(function(v) {
            var vTree = makeTree(document, fact, v, [], -1, namer);
            fmSpan.appendChild(vTree.span);
        });
    });
    */
    return termBox;
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
        var rule = ".tool" + cssEscape(toolOp) + "_" + arg +
            " .shooter .depth1.input" + arg + "of2.tool" + cssEscape(toolOp) +
            " { border: 2px solid black; cursor:pointer;}";

        styleSheet.insertRule(rule, 0);
    }

}

function setWorkPath(wp) {
    var className = "";
    if (typeof wp == 'undefined') {
        delete state.workPath;
    } else {
        state.workPath = wp;
        var usableTools = Engine.getUsableTools(state.work, state.workPath);
        for (var k in usableTools) if (usableTools.hasOwnProperty(k)) {
            var v = usableTools[k];
            className += " tool" + cssEscape(v[0]) + "_" + v[1];
        }
    }
    document.body.className = className;
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
            if (path.length != 1) {
                return null;
            }
            var factPath = path.slice();
            return function(ev) {
                console.log("ApplyFact " + fact.Skin.Name);
                    doAnimate(fact, box, factPath,
                              state.work, workBox, state.workPath, function() {
                try {
                                  var newWork = Engine.applyFact(
                                      state.work, state.workPath,
                                      fact, factPath);
                                  message("");
                                  state.url = "";
                                  setWorkPath();
                                  setWork(newWork);
                                  redraw();
                } catch (e) {
                    console.log("Error in applyFact: " + e);
                    console.log(e.stack);
                    message(e);
                }
                              });
                ev.stopPropagation();
            };
        };
        box = makeThmBox(fact, fact.Core[Fact.CORE_STMT], factOnclickMaker);
        box.className += " shooter";
        landMap[land.name].pane.appendChild(box);
        var turnstile = document.createElement("span");
        turnstile.className = "turnstile";
        turnstile.innerText = "\u22a2";
        turnstile.onclick = function(ev) {
            try {
                state.url = "#u=" + (urlNum++) + "/" + "#f=" + fact.Skin.Name;
                var thm = Engine.ground(state.work, fact);
                var newFactFp = addToShooter(thm);
                currentLand().thms.push(newFactFp.local);
                if (storage.user) {
                    // TODO: numbers goals backwards and doesn't carry over
                    // anonymously-won points when logging in.
                    storage.remote.child("users").
                        child(storage.user.uid).
                        child("points").
                        child(fbEscape(currentLand().name)).
                        child(currentLand().goals.length).
                        set(newFactFp.remote);
                }

                message("");
                setWorkPath();
                nextGoal();
                redraw();
            } catch (e) {
                console.log("Error in ground: " + e);
                console.log(e.stack);
                message(e);
            }
            ev.stopPropagation()
        };
    
        box.appendChild(turnstile);
        factToShooterBox[fact.Skin.Name] = {
            fact: fact,
            box: box,
            land: land.name,
            turnstile: turnstile
        };
        box.id = "shooter-" + fact.Skin.Name;
        break;
    case 1:
        // Adding generify to the shooter
        var box;
        var factOnclickMaker = function(path) {
            return null;
        };
        var hyp0box = makeThmBox(fact, fact.Core[Fact.CORE_HYPS][0],factOnclickMaker);
        var stmtbox = makeThmBox(fact, fact.Core[Fact.CORE_STMT], factOnclickMaker);
        landMap[land.name].pane.appendChild(hyp0box);
        hyp0box.appendChild(stmtbox);
        hyp0box.onclick = function(ev) {
            try {
                setWork(Engine.applyInference(state.work, fact));
                message("");
                setWorkPath();
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
        setWorkPath(goalPath);
        // Highlight usable tools.
        // TODO: move this somewhere else
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
    var stateKey = storage.fpSave("state", state);
    var stateFp = stateKey.local;
    if (stateFp != log.now) {
        var oldNow = log.now;
        log.now = stateFp;
        var logFp = storage.fpSave("log", log).local;
        log.parent = logFp;
        storage.local.setItem("childOf/" + oldNow, logFp);
        storage.local.setItem(STATE_KEY, logFp);
        if (storage.user) {
            storage.remote.child("users").child(storage.user.uid).
                child("state").set(stateKey.remote);
        }
        history.pushState(logFp, STATE_KEY, "#s=" + stateFp + "/" + state.url);
    }
}

function currentLand() {
    return state.lands[state.lands.length-1];
}
function nextGoal() {
    var land = currentLand();
    if (!land.goals || (land.goals.length == 0)) {
        delete land.goals;
        var nextLand = landDepMap[land.name]; // XXX
        if (nextLand) {
            enterLand(nextLand);
            return nextGoal();
        } else {
            message("No more lands! You win! Now go write a land.");
            return;
        }
    }
    var goal = land.goals.shift();
    state.work = startWork(goal);
    save();
    return;
}

function onNextRedraw(f) {
    deferredUntilRedraw.push(f);
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
    deferredUntilRedraw.forEach(function(f) { f(); });
    deferredUntilRedraw.splice(0, deferredUntilRedraw.length);
    var well = document.getElementById("well");
    try {
        var box = makeThmBox(state.work,
                             state.work.Core[Fact.CORE_HYPS][0],
                             workOnclickMaker);
        well.removeChild(well.firstChild);
        well.appendChild(box);
        workBox = box;
        redrawSelection();
        Engine.forEachGroundableFact(state.work, function(w, f) {
            message("Groundable: " + f.Skin.Name);
            message("Ground out!");
            var box = factToShooterBox[f.Skin.Name];
            box.turnstile.style.display = "block";
            landMap[box.land].tab.className = "tab groundable";
            onNextRedraw(function() {
                box.turnstile.style.display = "none";
                landMap[box.land].tab.className = "tab";
            });
        });
    } catch (e) {
        message(e);
    }
}

function loadState(flat) {
    state = flat;
    state.work = new Fact(state.work);
    setWorkPath(state.workPath);
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
            var factFp = addToShooter(data).local;
            land.thms.push(factFp);
        });
    }
}

function addLandToUi(land) {
    console.log("XXX adding land to ui: " + land.name);
    if (landMap[land.name] && landMap[land.name].pane) {
        console.log("Warning: Skipping already-added land " + land.name);
        return;
    }
    var tab = document.createElement("button");
    document.getElementById("shooterTabs").appendChild(tab);
    tab.className = "tab";
    tab.innerHTML = land.name.replace(/[<]/g,"&lt;");
    var pane = document.createElement("span");
    document.getElementById("shooterTape").appendChild(pane);
    if (!landMap[land.name]) {
        landMap[land.name] = {land:land};
    }
    landMap[land.name].pane = pane;
    landMap[land.name].tab = tab;
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
        var factFp = addToShooter(thm).local;
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
            storage.fpLoad("fact",thmFp, function(fact) {
                var factData = JSON.stringify(fact);
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
    });
}





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

function getPageCoords(node) {
    var x = 0;
    var y = 0;
    do {
        y += node.offsetTop;
        x += node.offsetLeft;
    } while ((node = node.offsetParent));
    return [x,y];
}

// Forwards to reallyDoAnimate, but sets a timeout to make sure onDone always gets
// called.
function doAnimate(fact, factBox, factPath, work, workBox, workPath, onDone) {
    var complete = false;
    var timeout;
    var callback = function() {
        if (!complete) {
            complete = true;
            onDone();
            if (timeout) {
                window.clearTimeout(timeout);
            }
        }
    }
    try {
        var steps = reallyDoAnimate(fact, factBox, factPath, work, workBox, workPath, callback);
        timeout = window.setTimeout(function() {
            if (!complete) {
                console.log("Timeout in reallyDoAnimate! ");
                onDone();
            }
        }, (steps + 1) * Move.defaults.duration);
    } catch (e) {
        console.log("Error in reallyDoAnimate: " + e);
        console.log(e.stack);
        onDone();
    }
}

function reallyDoAnimate(fact, factBox, factPath, work, workBox, workPath, onDone) {
    onDone();
}

//XXX

/*
window.setTimeout(function() {

    setWorkPath([]);
    redrawSelection();
    var sbox = factToShooterBox["neHAKB"];
    state.work = startWork(
        {Core:[[],[0,[0,[0,0,1],2],[0,1,2]],[]],
         Skin:{TermNames:["&rarr;"]},
         FreeMaps:[[]]});
    state.workPath = [];
    redraw();
    doAnimate(sbox.fact, sbox.box, [2],
              state.work, workBox, state.workPath,
              function(){message("XXX done");});
}, 400);


/*
*/
function loadLands(lands) { // TODO: this has become totally gefucked
    var numLands = 0;
    for (var n in lands) if (lands.hasOwnProperty(n)) {
        numLands++;
        land = JSON.parse(lands[n].land);
        if (!landMap[land.name]) {
            landMap[land.name] = {land:land};
        }
        if (land.depends && land.depends.length > 0) {
            landDepMap[land.depends[0]] = land; // TODO: multidep
        } else {
            landDepMap[undefined] = land;
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
}
// ==== STARTUP ====

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
        loadLands(JSON.parse(storage.local.getItem("my-checked-lands")));
        var match = window.location.search.match(/CHEAT=(\d+)/);
        if (match) {
            cheat(match[1]);
        }
    });
} else {
    state = {
        lands: [],
        url:"",
    };
    storage.remoteGet("checked/lands", function(lands) {
        storage.local.setItem("my-checked-lands", JSON.stringify(lands));
        loadLands(lands);
    });
}
