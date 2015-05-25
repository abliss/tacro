// Hackish for now.
var Fact = require('./fact.js');
var Engine = require('./engine.js');
var Storage = require('./storage.js');
var Move = require('./move.js');
var TreeMaker = require('./treeMaker.js');
var Chat = require('./chat.js');

var storage = new Storage(Engine.fingerprint);
var chat = new Chat(storage, Engine.fingerprint, document.getElementById('chatPane'),
                    document.getElementById('chatInput'));
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
var panes = [];
var termToPane = {};
var shooterTreeWidth = 16; // XXXX in VW. sync with stairs.less
var workTreeWidth = 50; // XXXX in VW. sync with stairs.less
var usableTools = {};
var auto = window.location.search.match(/auto/) ? true : false;
var reflexives = {};
var thms = {};

Error.stackTraceLimit = Infinity;

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

/* {
        fact: fact,
        exp: exp,
        onclick: onclick,
        width: maxWidth,
        height: maxHeight,
        editable:editable,
    }
*/
function makeThmBox(opts) {
    if (opts.editable) {
        opts.getSpecifyOptions = function() { return state.specifyOptions; }
    }
    var termBox = document.createElement("span");
    termBox.className += " termbox";
    var tree = TreeMaker(opts);
    termBox.appendChild(tree.div);
    termBox.spanMap = tree.spanMap;
    termBox.tree = tree;
    /*
      // TODO: XXX: freevars
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
function addCssRule(rule) {
    var styleEl = document.createElement('style');
    // Apparently some version of Safari needs the following line? I dunno.
    styleEl.appendChild(document.createTextNode(''));
    document.head.appendChild(styleEl);
    var styleSheet = styleEl.sheet;
    styleSheet.insertRule(rule, 0);
    console.log("Added Rule: " + rule);
}
function registerNewTool(toolOp) {
    for (var arg = 1; arg <= 2; arg++) {
        var rule = ".tool" + cssEscape(toolOp) + "_" + arg +
            " .shooter .tool" + cssEscape(toolOp) +
            ".apply" + arg + " { display:inline-block;}";
        addCssRule(rule);
    }
    
}

function setWorkPath(wp) {
    var className = "";
    if (typeof wp == 'undefined') {
        delete state.workPath;
        if (workBox) delete workBox.pathTermArr;
    } else {
        state.workPath = wp;
        var pathExp = zpath(state.work.Core[Fact.CORE_HYPS][0], wp);
        if (workBox) workBox.pathTermArr = expToTermArr.bind(state.work)(pathExp);
        usableTools = Engine.getUsableTools(state.work, state.workPath);
        for (var k in usableTools) if (usableTools.hasOwnProperty(k)) {
            var v = usableTools[k];
            className += " tool" + cssEscape(v[0]) + "_" + v[1];
        }
    }
    // TODO: XXX: will be slow
    for (var k in factToShooterBox) if (factToShooterBox.hasOwnProperty(k)) {
        factToShooterBox[k].box.tree.onchange();
    }
    document.body.className = className;

    redrawSelection();
}

// A Facet is a Fact which can be / has been specified by some amount.
function Facet(factData) {
    var fact = Engine.canonicalize(new Fact(factData));
    fact.Skin.VarNames = fact.Skin.VarNames.map(function(x,i) {
        return "&#" + (i + 0x2460) + ";";
    });

    this.fact = fact;
    // Find the var at the given path. Replace all instances of it with the
    // named term or variable. Iff name is a term, its arity must be
    // specified. The new term will get that many new children variables.
    this.specify = function(varNum, name, arity, freeMap) {
        
    }
}

function workPathHighlighter(tool, path, isHover) {
    var suffix = path.slice(1);
    function getWorkPath() {
        if (state.workPath) {
            if ((path.length == 0) || !usableTools[[tool, path[0]]]) {
                return null;
            }
            if ((state.workPath.length > 0) && (suffix.length > 0)) {
                return "" + state.workPath + "," + suffix;
            } else {
                return suffix;
            }
        } else {
            return path;
        }
    }
    if (!workBox) return;
    var n = workBox.spanMap[getWorkPath()];
    if (!n) return;
    if (isHover) {
        n.className += " fakeHover";
    } else {
        n.className = n.className.replace(/ fakeHover/, '');
    }
}

// TODO: XXX expecst this=fact
function expToTermArr(exp) {
    if (Array.isArray(exp)) {
        var args = exp.slice(1).map(expToTermArr.bind(this));
        args.unshift(this.Skin.TermNames[exp[0]]);
        return args;
    } else {
        return exp;
    }
}

// NB: not the same as orcat's xpath definition. Pass 0 to get the term.
// TODO: XXX
function zpath(exp, path) {
    var a = exp, l = path.length, i = 0;
    for (i = 0; i < l; i++) {
        a=a[path[i]];
    }
    return a;
}

function getWorkTermArr() {
    var exp = state.work.Core[Fact.CORE_HYPS][0];
    return expToTermArr.bind(state.work)(exp);
}

function groundOut() {
    try {
        var fact = this;
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
                child(storage.escape(currentLand().name)).
                child(currentLand().goals.length).
                set(newFactFp.remote);
        }

        var span = document.getElementById("achieved");
        span.style.display = '';
        window.setTimeout(function() {span.className = "animated";}, 10);
        window.setTimeout(function() {span.className = "";
                                      span.style.display = 'none';}, 1200);
        /* XXX: sync with css */

        message("");
        setWorkPath([]);
        nextGoal();
        redraw();
    } catch (e) {
        console.log("Error in ground: " + e);
        console.log(e.stack);
        message(e);
    }
}

function addToShooter(factData, land) {
    if (!factData) {
        throw new Error("Bad fact: "+ factData);
    }
    if (!land) land = currentLand();
    var facet = new Facet(factData);
    knowTerms(facet.fact);

    var fact = facet.fact;

    var factFp = storage.fpSave("fact", facet.fact);
    if (thms[factFp.local]) {
        console.log("XXXX Skipping duplicate fact " + factFp.local);
        return factFp;
    }
    thms[factFp.local] = facet.fact;

    var newTool = Engine.onAddFact(facet.fact);
    if (newTool) {
        registerNewTool(newTool);
    }
    switch (factData.Core[Fact.CORE_HYPS].length) {
        case 0:
        break;
        case 1: {
            var box = makeThmBox({
                fact:fact,
                exp:fact.Core[Fact.CORE_STMT],
                size:shooterTreeWidth,
                onmouseover: workPathHighlighter,
                onchange: onchange,
                editable:true});
            // TODO: display hyp somehow
            box.className += " shooter";
            box.onclick = function() {
                var varMap = null;
                if (!auto) {
                    varMap = box.tree.getVarMap(state.work);
                }
                var newWork = Engine.applyInference(state.work, fact, varMap);
                message("");
                state.url = "";
                setWorkPath([]);
                setWork(newWork);
                redraw();
            };
            var pane = panes[panes.length-1];
            pane.pane.insertBefore(box, pane.pane.firstChild);
        }
        default:
        console.log("Skipping inference: " + JSON.stringify(fact.Core));
        return factFp;
    }
    if ((JSON.stringify(fact.Core) === '[[],[0,0,0],[]]')) {
        var reflexiveTerm = fact.Skin.TermNames[0];
        console.log("Reflexive found:" + reflexiveTerm);
        addCssRule('.name'+cssEscape(reflexiveTerm) + " .depth1.arg1 {" +
                "border-right: 1px solid red;}");
        addCssRule('.name'+cssEscape(reflexiveTerm) + " .depth1.arg2 {" +
                "border-left: 1px solid red;}");
        reflexives[reflexiveTerm] = fact;
        return factFp;
    }
    var box;
    function onchange() {
        if (!workBox) return;
        // TODO: UGLY!! expects this to be treeMaker's root object
        var tree = this;
        var expTermArr = tree.getTermArr();
        var boxString = JSON.stringify(expTermArr);
        for (var k in usableTools) if (usableTools.hasOwnProperty(k)) {
            var v = usableTools[k];
            var tool = v[0];
            var argNum = v[1];
            if (expTermArr[0] != tool) continue;
            var button = box.deployButtons[argNum];
            if (!button) continue;
            if (auto ||
                ((JSON.stringify(expTermArr[argNum]) ===
                  JSON.stringify(workBox.pathTermArr)) &&
                 !boxString.match(/null/))) {
                button.className += " matched";
                button.removeAttribute('disabled');
            } else {
                button.className = button.className.replace(/ matched/g,'');
                button.setAttribute('disabled', 'disabled');
            }

        }

    }
    box = makeThmBox({
        fact:fact, 
        exp:fact.Core[Fact.CORE_STMT],
        size:shooterTreeWidth,
        onmouseover: workPathHighlighter,
        onchange: onchange,
        editable:true});
    box.className += " shooter";
    box.className += " cmd_" + fact.Tree.Cmd;
    var pane = panes[panes.length-1];
    pane.pane.insertBefore(box, pane.pane.firstChild);
    box.style["max-height"] = "0vh";
    // TODO: animate to proper max-height
    window.requestAnimationFrame(function(){box.style["max-height"]="100vh";});

    
    function applyChild(argNum) {
        console.log("ApplyFact " + fact.Skin.Name + " arg " + argNum);
        // TODO: PICKUP: undummy
        try {
            var varMap = null;
            if (!auto) {
                varMap = box.tree.getVarMap(state.work);
            }
            var newWork = Engine.applyFact(state.work, state.workPath,
                                           fact, [argNum], varMap);
            message("");
            state.url = "";
            setWorkPath([]);
            setWork(newWork);
            redraw();
        } catch (e) {
            console.log("Error in applyFact: " + e);
            console.log(e.stack);
            message(e);
        }
    }
    
    // Undo button
    var undo = box.spanMap[[]].appendChild(document.createElement("button"));
    undo.className = "undo";
    undo.innerHTML = "&laquo;";

    // Apply buttons (left and right)
    // TODO: assumes all tools are (at most) binary
    box.deployButtons = [];
    [1,2].forEach(function(argNum) {
        var apply = box.appendChild(
            document.createElement("button"));
        apply.disabled = "disabled";
        apply.className = "applyButton apply" + argNum +
            " tool" + cssEscape(fact.Skin.TermNames[0]);
        apply.innerHTML = "&Rarr;";
        apply.onclick = applyChild.bind(null, argNum);
        box.deployButtons[argNum] = apply;
    });
    factToShooterBox[fact.Skin.Name] = {
        fact: fact,
        box: box,
        land: land.name,
    };
    box.id = "shooter-" + fact.Skin.Name;

    return factFp;
}


function workOnclick(path, ev) {
    var goalPath = path.slice();
    if (goalPath[goalPath.length-1] == 0) {
        goalPath.pop();
    }
    setWorkPath(goalPath);
    // Highlight usable tools.
    // TODO: move this somewhere else
    state.url = "#u=" + (urlNum++) + "/#g=" + goalPath;
    save();
    ev.stopPropagation();
}

function startWork(fact) {
    var work = new Fact(fact);
    if (work.Core[Fact.CORE_HYPS].length == 0) {
        work.setHyps([work.Core[Fact.CORE_STMT]]);
        work.Skin.HypNames = ["Hyps.0"];
        work.setProof(["Hyps.0"]);
    }
    if (!work.Tree.Cmd) {
        work.setCmd("thm");
    }
    work = Engine.canonicalize(work);
    work.Skin.VarNames = work.Skin.VarNames.map(function(x,i) {
        return "&#" + (i + 0x24D0) + ";";
    });
    return work;
}

function knowTerms(fact) {
    var newTerms = {};
    var numNewTerms = 0;
    fact.Skin.TermNames.forEach(function(termName, termNum) {
        if (!state.knownTerms.hasOwnProperty(termName) &&
            !newTerms.hasOwnProperty(termName)) {
            newTerms[termNum] =  true;
            numNewTerms++;
            var termObj = {text:termName,
                           freeMap:fact.FreeMaps[termNum],
                           arity:-1 // updated in scan() below
                          };
            state.knownTerms[termName] = termObj;
            state.specifyOptions.Terms.push(termObj);
        }
        if (!termToPane[termName]) {
            termToPane[termName] = new Pane(termName);
        }
    });
    function scan(exp) {
        if (numNewTerms > 0&& Array.isArray(exp)) {
            if (newTerms[exp[0]]) {
                var termNum = exp[0];
                var termName = fact.Skin.TermNames[termNum];
                state.knownTerms[termName].arity = exp.length - 1;
                newTerms[termNum] = false;
                numNewTerms--;
            }
            exp.slice(1).map(scan);
        }
    }
    // TODO: it is possible that a new term could be introduced only in a
    // dependency. But this should never happen in tacro.
    scan(fact.Core[Fact.CORE_STMT]);
    fact.Core[Fact.CORE_HYPS].forEach(scan);
    return newTerms;
}

function setWork(work) {
    state.work = work;
    state.workHash = Engine.fingerprint(work);
    var ground = document.getElementById('ground');
    ground.setAttribute('disabled','disabled');
    ground.className = "disabled";
    ground.onclick = null;
    for (var k in reflexives) if (reflexives.hasOwnProperty(k)) {
        var idFact = reflexives[k]; 
        try {
            // TODO: should not be using exceptions for this
            Engine.getMandHyps(state.work, [], idFact, []);
            ground.removeAttribute('disabled');
            ground.className = "enabled";
            ground.onclick = groundOut.bind(idFact);
        } catch (e) {
            // can't ground this way
        }
    }
    // TODO: might we need an extra var here?
    state.specifyOptions.Vars = work.Skin.VarNames;
    chat.setWork(work);
    // TODO: XXX: will be slow
    for (var k in factToShooterBox) if (factToShooterBox.hasOwnProperty(k)) {
        factToShooterBox[k].box.tree.onchange();
    }
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
    knowTerms(goal);
    setWork(startWork(goal));
    setWorkPath([]);
    return;
}

function onNextRedraw(f) {
    deferredUntilRedraw.push(f);
}
function redrawSelection() {
    if (!workBox) return;
    if (selectedNode) {
        d3.select(selectedNode).classed("selected", false);
    }
    if (typeof state.workPath  !== 'undefined') {
        selectedNode = workBox.spanMap[state.workPath];
        if (!selectedNode) {
            throw new Error("Selected node not found:" + state.workPath);
        }
        d3.select(selectedNode).classed("selected", true);
    }
}
function redraw() {
    deferredUntilRedraw.forEach(function(f) { f(); });
    deferredUntilRedraw.splice(0, deferredUntilRedraw.length);
    var well = document.getElementById("well");
    try {
        var box = makeThmBox({
            fact:state.work,
            exp:state.work.Core[Fact.CORE_HYPS][0],
            onclick:workOnclick,
            size:workTreeWidth, 
            editable:false});
        well.removeChild(well.firstChild);
        well.appendChild(box);
        workBox = box;
        setWorkPath(state.workPath);
        /*
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
        */
    } catch (e) {
        message(e);
    }
}

function loadState(flat) {
    state = flat;
    setWork(new Fact(state.work));
    message("");
}

function loadLogFp(logFp, cb) {
    storage.fpLoad("log", logFp, function(logObj) {
        storage.fpLoad("state", logObj.now, function(stateObj) {
            log = logObj;
            loadState(stateObj);
            // TODO: should popstate? double-undo problem.
            history.pushState(logFp, "state",
                              "#s=" + logObj.now + "/" + state.url);
            document.getElementById("forward").style.visibility="visible";
            if (cb) {cb();}
            redraw();
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
    land.goals = landData.goals.slice();
    if (landData.axioms) {
        landData.axioms.forEach(function(data) {
            var factFp = addToShooter(data).local;
            land.thms.push(factFp);
        });
    }
}

function Pane(newTerm) {
    console.log("XXXX New pane " + newTerm);
    var tab = document.createElement("button");
    tab.addEventListener("click", function() {
        var doc = window.document; var docEl = doc.documentElement; var requestFullscreen = docEl.requestFullscreen || docEl.mozRequestFullScreen || docEl.webkitRequestFullScreen || docEl.webkitRequestFullscreen || docEl.msRequestFullscreen;
        //requestFullscreen.call(docEl);
    });
    document.getElementById("shooterTabs").appendChild(tab);
    tab.className = "tab";
    tab.innerHTML = newTerm.replace(/[<]/g,"&lt;");
    var pane = document.createElement("span");
    document.getElementById("shooterTape").appendChild(pane);
    pane.className = "pane"
    function onclick() {
        if (currentPane) {currentPane.style.display="none";}
        pane.style.display="inline-block";
        currentPane = pane;
    }
    tab.addEventListener("click", onclick);
    onclick();
    this.pane = pane;
    panes.push(this);
}

function message(msg) {
    if (msg) {console.log("Tacro: " + msg);}
    document.getElementById("message").innerText = msg;
}

function cheat(n) {
    while (n > 0) {
        var thm = new Fact(state.work);
        thm.Tree.Proof=[];
        //thm.Tree.Cmd = 'stmt'
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
            loginNode.addEventListener("click", function() {
                storage.authLogout();
                return false;
            });
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

function ChatListener(pane) {
    
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
            land.thms.forEach(function(thmFp) {
                storage.fpLoad("fact", thmFp, function(thmObj) {
                    addToShooter(thmObj, land);
                    redraw();
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
        specifyOptions: {
            Vars:[],
            Terms:[]
        },
        knownTerms: {},
    };
    storage.remoteGet("checked/lands", function(lands) {
        storage.local.setItem("my-checked-lands", JSON.stringify(lands));
        loadLands(lands);
    });
}
