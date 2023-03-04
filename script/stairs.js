// Hackish for now.
!function() {

    Error.stackTraceLimit = Infinity;
    function Ui(harness) {
        const Ui = this;
    // ==== Stubs for node.js usage ====
        if (typeof harness !== 'undefined') {
            function Node() {};
            Node.prototype = {
                style: {},
                appendChild: function(n){this.firstChild = n; return n},
                removeChild: function(){delete this.firstChild; },
                sheet: { insertRule: function(){}},
                addEventListener: function(){},
                setAttribute: function(){},
                insertBefore: function(){},
                removeAttribute: function(){},
                click: function(){},
                className:"",
            };
            Blob= function(data, type) {this.data=data; this.type=type};
            if (typeof URL.createObjectURL == 'undefined') {
                URL.createObjectURL = function(blob){return {blob}};
            }

            Ui.Node=function() {};
            Ui.document= {
                createElement:function() {return new Node();},
                getElementById:function() {return new Node();},
                createTextNode:function() {return new Node();},
                head: new Node(),
                body: new Node(),
            };
            Ui.window= {
                addEventListener: function(){},
                location: {search: ""},
                requestAnimationFrame:function(){},
                setTimeout:setTimeout,
            };
            Ui.history= { pushState: function(){}, };
            Ui.d3= {
                "select":function(){return {classed:function(){}}},
                layout:{ tree:function(){
                    return {nodeSize:function(){},
                            separation:function(){},
                            nodes:function(){},
                           }; }, } };

            Ui.cssEscape= function(str){
                return encodeURIComponent(str).replace(/%/g,"_");
            };
            Ui.groundButton= new Node();

            d3 = Ui.d3 // TODO: use module dependencies for treeMaker
            document = Ui.document
            window = Ui.window
        } else {

            Ui.Node=Node;
            Ui.document=document;
            Ui.window=window;
            Ui.history=history;
            Ui.d3=d3;
            Ui.cssEscape=function(str) {
                // TODO: collisions; pass this to treeMaker.js
                return encodeURIComponent(str).replace(/%/g,"_");
            };
            Ui.groundButton=document.getElementById('ground');
        }

        Ui.TreeMaker = require('./treeMaker.js');
        Ui.selectedNode = null;
        Ui.workBox;
        Ui.factToShooterBox = {};
        Ui.deferredUntilRedraw = [];
        Ui.currentPane;
        Ui.panes = [];
        Ui.termToPane = {};
        Ui.shooterTreeWidth = 16; // XXXX in VW. sync with stairs.less
        Ui.workTreeWidth = 50; // XXXX in VW. sync with stairs.less
    }

    Ui.prototype.makeThmBox = function(opts) {
        const Ui = this;
        if (opts.editable) {
            opts.getSpecifyOptions = function() { return Ui.Game.state.specifyOptions; }
        }
        // XXX sync with css
        opts.redrawDelay = opts.redrawDelay || Ui.opts.redrawDelay || 1050;
        var termBox = Ui.document.createElement("span");
        termBox.className += " termbox";
        var tree = Ui.TreeMaker(opts);
        termBox.appendChild(tree.div);
        termBox.spanMap = tree.spanMap;
        termBox.tree = tree;
        /*
        // TODO: XXX: freevars
        var nullCb = function(){};
        fact.Core[Fact.CORE_FREE].forEach(function(fm) {
        var fmSpan = Ui.document.createElement("span");
        fmSpan.className = "freemap";
        termBox.appendChild(fmSpan);
        fm.forEach(function(v) {
        var vTree = makeTree(Ui.document, fact, v, [], -1, namer);
        fmSpan.appendChild(vTree.span);
        });
        });
        */
        return termBox;
    };


    Ui.prototype.addCssRule = function(rule) {
        const Ui = this;
        var styleEl = Ui.document.createElement('style');
        // Apparently some version of Safari needs the following line? I dunno.
        styleEl.appendChild(Ui.document.createTextNode(''));
        Ui.document.head.appendChild(styleEl);
        var styleSheet = styleEl.sheet;
        styleSheet.insertRule(rule, 0);
        console.log("Added Rule: " + rule);
    };
    Ui.prototype.registerNewTool = function(toolOp) {
        const Ui = this;
        for (var arg = 1; arg <= 2; arg++) {
            var rule = ".tool" + Ui.cssEscape(toolOp) + "_" + arg +
                " .shooter .tool" + Ui.cssEscape(toolOp) +
                ".apply" + arg + " { display:inline-block;}";
            Ui.addCssRule(rule);
        }
        
    };

    Ui.prototype.workPathHighlighter = function(tool, path, isHover) {
        const Ui = this;
        var suffix = path.slice(1);
        function getWorkPath() {
            if (Ui.Game.state.workPath) {
                if ((path.length == 0) || !Ui.Game.usableTools[[tool, path[0]]]) {
                    return null;
                }
                if ((Ui.Game.state.workPath.length > 0) && (suffix.length > 0)) {
                    return "" + Ui.Game.state.workPath + "," + suffix;
                } else {
                    return suffix;
                }
            } else {
                return path;
            }
        }
        if (!Ui.workBox) return;
        var n = Ui.workBox.spanMap[getWorkPath()];
        if (!n) return;
        if (isHover) {
            n.className += " fakeHover";
        } else {
            n.className = n.className.replace(/ fakeHover/, '');
        }
    };

    Ui.prototype.addToShooter = function(factData, land) {
        const Ui = this;
        if (!factData) {
            throw new Error("Bad fact: "+ factData);
        }
        if (!land) land = Ui.Game.currentLand();
        var facet = Ui.Game.makeFacet(factData);
        Ui.Game.knowTerms(facet.fact);

        var fact = facet.fact;

        var factFp = Ui.Game.storage.fpSave("fact", facet.fact);
        if (Ui.Game.thms[factFp.local]) {
            console.log("XXXX Skipping duplicate fact " + factFp.local);
            return factFp;
        }
        Ui.Game.thms[factFp.local] = facet.fact;

        var newTool = Ui.Game.engine.onAddFact(facet.fact);
        if (newTool) {
            Ui.message("New root unlocked: " + newTool);
            Ui.registerNewTool(newTool);
        }
        switch (factData.Core[Ui.Game.Fact.CORE_HYPS].length) {
        case 0:
            break;
        case 1: {
            var box = Ui.makeThmBox({
                fact:fact,
                exp:fact.Core[Ui.Game.Fact.CORE_STMT],
                size:Ui.shooterTreeWidth,
                onmouseover: Ui.workPathHighlighter.bind(Ui),
                onchange: onchange,
                editable:true,
            });
            // TODO: display hyp somehow
            box.className += " shooter";
            box.onclick = function() {
                var varMap = box.tree.getVarMap(Ui.Game.state.work);
                var dumpStep = {func: "applyInference",
                                args: [Ui.Game.stripFact(fact), varMap]};
                var newWork = Ui.Game.engine.applyInference(Ui.Game.state.work, fact, varMap);
                Ui.message("");
                Ui.Game.state.url = "";
                Ui.Game.setWorkPath([]);
                Ui.Game.setAnchorPath();
                Ui.Game.setWork(newWork);
                Ui.Game.save(dumpStep);
                Ui.redraw();
            };
            var pane = Ui.panes[Ui.panes.length-1];
            pane.pane.insertBefore(box, pane.pane.firstChild);
        }
        default:
            console.log("Skipping inference: " + JSON.stringify(fact.Core));
            return factFp;
        }
        if ((JSON.stringify(fact.Core) === '[[],[0,0,0],[]]')) {
            var reflexiveTerm = fact.Skin.TermNames[0];
            console.log("Reflexive found:" + reflexiveTerm);
            Ui.addCssRule('.name'+Ui.cssEscape(reflexiveTerm) + " .depth1.arg1 {" +
                          "border-right: 1px solid red;}");
            Ui.addCssRule('.name'+Ui.cssEscape(reflexiveTerm) + " .depth1.arg2 {" +
                          "border-left: 1px solid red;}");
            Ui.Game.reflexives[reflexiveTerm] = fact;
        }
        var box;
        function onchange() {
            if (!Ui.workBox) return;
            // TODO: UGLY!! expects this to be treeMaker's root object
            var tree = this;
            var expTermArr = tree.getTermArr();
            var boxString = JSON.stringify(expTermArr);
            if (Ui.Game.state.anchorPath) { // XXX anchorUsableTools
                box.deployButtons.forEach(button => {
                    button.className += " matched";
                    button.removeAttribute('disabled');
                });
            }
            for (var k in Ui.Game.usableTools) if (Ui.Game.usableTools.hasOwnProperty(k)) {
                var v = Ui.Game.usableTools[k];
                var tool = v[0];
                var argNum = v[1];
                if (expTermArr[0] != tool) continue;
                var button = box.deployButtons[argNum];
                if (!button) continue;
                if (Ui.Game.auto ||
                    ((JSON.stringify(expTermArr[argNum]) ===
                      JSON.stringify(Ui.workBox.pathTermArr)) &&
                     !boxString.match(/null/))) {
                    button.className += " matched";
                    button.removeAttribute('disabled');
                } else {
                    button.className = button.className.replace(/ matched/g,'');
                    button.setAttribute('disabled', 'disabled');
                }

            }

        }
        box = Ui.makeThmBox({
            fact:fact,
            exp:fact.Core[Ui.Game.Fact.CORE_STMT],
            size:Ui.shooterTreeWidth,
            onmouseover: Ui.workPathHighlighter.bind(Ui),
            onchange: onchange,
            editable:true});
        box.className += " shooter";
        box.className += " cmd_" + fact.Tree.Cmd;
        var pane = Ui.panes[Ui.panes.length-1];
        pane.pane.insertBefore(box, pane.pane.firstChild);
        box.style["max-height"] = "0vh";
        // TODO: animate to proper max-height
        Ui.window.requestAnimationFrame(function(){box.style["max-height"]="100vh";});

        function applyChild(argNum) {
            // TODO: PICKUP: undummy
            try {
                var varMap = box.tree.getVarMap(Ui.Game.state.work);
                var factPath = (Ui.Game.state.anchorPath ? [2, argNum] : [argNum]);
                var anchors = Ui.Game.state.anchorPath ? [Ui.Game.state.anchorPath] : undefined;
                var dumpStep =
                    {func:"applyFact",
                     args: [Ui.Game.state.workPath,
                            Ui.Game.stripFact(fact),
                            factPath,
                            varMap,
                            anchors]
                    };
                var newWork = Ui.Game.engine.applyFact(Ui.Game.state.work, Ui.Game.state.workPath,
                                                    fact,
                                                    factPath,
                                                    varMap,
                                                    anchors);
                Ui.message("");
                Ui.Game.state.url = "";
                Ui.Game.setWorkPath([]);
                Ui.Game.setAnchorPath();
                Ui.Game.setWork(newWork);
                Ui.Game.save(dumpStep);
                Ui.redraw();
            } catch (e) {
                console.log("Error in applyFact: " + e);
                console.log(e.stack);
                Ui.message(e);
            }
        }

        // Apply buttons (left and right)
        // TODO: assumes all tools are (at most) binary
        box.deployButtons = [];
        [1,2].forEach(function(argNum) {
            var apply = box.appendChild(
                Ui.document.createElement("button"));
            apply.disabled = "disabled";
            apply.className = "applyButton apply" + argNum +
                " tool" + Ui.cssEscape(fact.Skin.TermNames[0]);
            apply.innerHTML = "&Rarr;";
            apply.onclick = applyChild.bind(null, argNum);
            box.deployButtons[argNum] = apply;
        });
        Ui.factToShooterBox[fact.getMark()] = {
            fact: fact,
            box: box,
            land: land.name,
        };
        box.id = "shooter-" + fact.Skin.Name;
        return factFp;
    };


    Ui.prototype.workOnclick = function(path, ev) {
        const Ui = this;
        var goalPath = path.slice();
        if (goalPath[goalPath.length-1] == 0) {
            goalPath.pop();
        }
        Ui.Game.setWorkPath(goalPath);
        // Highlight usable tools.
        // TODO: move this somewhere else
        Ui.Game.state.url = "#u=" + (Ui.Game.urlNum++) + "/#g=" + goalPath;
        Ui.Game.save();
        ev.stopPropagation();
    };
    Ui.prototype.redrawSelection = function() {
        const Ui = this;
        if (!Ui.workBox) return;
        if (Ui.selectedNode) {
            d3.select(Ui.selectedNode).classed("selected", false);
        }
        if (typeof Ui.Game.state.workPath  !== 'undefined') {
            Ui.selectedNode = Ui.workBox.spanMap[Ui.Game.state.workPath];
            if (!Ui.selectedNode) {
                throw new Error("Selected node not found:" + Ui.Game.state.workPath);
            }
            d3.select(Ui.selectedNode).classed("selected", true);
        }
    };
    Ui.prototype.redraw = function() {
        const Ui = this;
        Ui.deferredUntilRedraw.forEach(function(f) { f(); });
        Ui.deferredUntilRedraw.splice(0, Ui.deferredUntilRedraw.length);
        var well = Ui.document.getElementById("well");
        try {
            var box = Ui.makeThmBox({
                fact:Ui.Game.state.work,
                exp:Ui.Game.state.work.Core[Ui.Game.Fact.CORE_HYPS][0],
                onclick:Ui.workOnclick.bind(Ui),
                size:Ui.workTreeWidth,
                editable:false});
            well.removeChild(well.firstChild);
            well.appendChild(box);
            Ui.workBox = box;
            Ui.Game.setWorkPath(Ui.Game.state.workPath);
            Ui.Game.updateGroundButton();
        } catch (e) {
            Ui.message(e);
        }
    };

    Ui.prototype.newPane = function(newTerm) {
        const Ui = this;
        var tab = Ui.document.createElement("button");
        tab.addEventListener("click", function() {
            var doc = Ui.document; var docEl = doc.documentElement; var requestFullscreen = docEl.requestFullscreen || docEl.mozRequestFullScreen || docEl.webkitRequestFullScreen || docEl.webkitRequestFullscreen || docEl.msRequestFullscreen;
            //requestFullscreen.call(docEl);
        });
        Ui.document.getElementById("shooterTabs").appendChild(tab);
        tab.className = "tab";
        tab.innerHTML = newTerm.replace(/[<]/g,"&lt;");
        var pane = Ui.document.createElement("span");
        Ui.document.getElementById("shooterTape").appendChild(pane);
        pane.className = "pane"
        function onclick() {
            if (Ui.currentPane) {Ui.currentPane.style.display="none";}
            pane.style.display="inline-block";
            Ui.currentPane = pane;
        }
        tab.addEventListener("click", onclick);
        onclick();
        const paneObj = {pane};
        Ui.panes.push(paneObj);
        if (Ui.panes.length == 3) {
            Ui.Game.auto = true;
            Ui.message("Automatic Activation mode enabled! Manual Training/promoting is now optional.");
        }
        return paneObj
    };

    Ui.prototype.message = function(msg) {
        const Ui = this;
        if (msg) {console.log("Tacro: " + JSON.stringify(msg));}
        if (msg.stack) {
            console.log(msg.stack);
        }
        if (msg.href) {
            Ui.document.getElementById("message").innerText = "";
            Ui.document.getElementById("message").appendChild(msg);
        } else {
            Ui.document.getElementById("message").innerText = msg;
        }
    };
    Ui.prototype.startup = function(opts) {
        const Ui = this;
        Ui.Game = new Game(Ui, opts);
        Ui.opts = opts || {};
        var gotoMatch = Ui.window.location.search.match(/goto=(\d+)/);
        if (gotoMatch) {
            localStorage.clear();
        }
        Ui.window.addEventListener('popstate', function(ev) {
            console.log("popstate to " + ev.state);
            if (ev.state) {
                Ui.Game.loadLogFp(ev.state);
            } else {
                var match = Ui.window.location.hash.match(/CHEAT=(\d+)/);
                if (match) {
                    Ui.Game.cheat(match[1]);
                }
                if (Ui.window.location.search.match(/auto=1/)) {
                    Ui.Game.auto = true;
                }
            }
        });
        Ui.document.getElementById("anchor").onclick = function() {
            if (Ui.Game.state.anchorPath == undefined) {
                Ui.Game.setAnchorPath(Ui.Game.state.workPath.slice());;
            } else {
                Ui.Game.setAnchorPath(undefined);
            }
        };

        Ui.document.getElementById("rewind").onclick = Ui.rewind = function() {
            var parentFp = Ui.Game.log.parent;
            if (parentFp) {
                Ui.Game.storage.fpLoad("log", parentFp, function(logObj) {
                    if (logObj.parent) {
                        Ui.Game.loadLogFp(logObj.parent);
                    }
                });
            }
            return false;
        };

        Ui.document.getElementById("forward").onclick = Ui.forward = function() {
            var childLogFp = Ui.Game.storage.local.getItem("childOf/" + Ui.Game.log.parent);
            if (childLogFp) {
                Ui.Game.loadLogFp(childLogFp);
            } else {
                Ui.document.getElementById("forward").style.visibility="hidden";
            }
            return false;
        };

        var logFp = Ui.Game.storage.local.getItem(Ui.Game.STATE_KEY);
        if (logFp) {
            // restore
            Ui.Game.loadLogFp(logFp, function() {
                Ui.Game.state.lands.forEach(function(land) {
                    land.thms.forEach(function(thmFp) {
                        Ui.Game.storage.fpLoad("fact", thmFp, function(thmObj) {
                            Ui.addToShooter(thmObj, land);
                            Ui.redraw();
                        });
                    });
                });
                Ui.Game.loadLands(JSON.parse(Ui.Game.storage.local.getItem("my-checked-lands")));

            });
        } else {
            //init
            Ui.Game.state = {
                lands: [],
                url:"",
                specifyOptions: {
                    Vars:[],
                    Terms:[]
                },
                knownTerms: {},
            };
            Ui.Game.storage.remoteGet("checked/lands", function(lands) {
                Ui.Game.storage.local.setItem("my-checked-lands", JSON.stringify(lands));
                Ui.Game.loadLands(lands);
                if (gotoMatch) {
                    Ui.Game.cheat(Number(gotoMatch[1]));
                    Ui.window.location.search = "";
                }
            });

        }
    };

    function Game(Ui, opts) {
        const Game = this;
        this.Ui = Ui;
        Game.Fact = require('./fact.js');
        var Engine = require('./engine.js');
        Game.Engine = Engine;
        Game.engine = new Engine();
        const Storage = require('./storage.js');
        Game.storage = new Storage(Game.engine.fingerprint, true, opts.scratchDir)
        var Chat = require('./chat.js');
        Game.chat = new Chat(
            Game.storage, Game.engine.fingerprint, Ui.document.getElementById('chatPane'),
            Ui.document.getElementById('chatInput'),
            function chatFilter(msg) {
                var match;
                if (match = msg.match(/^\//)) {
                    try {
                        function clear() {
                            localStorage.clear();
                        }

                        Ui.message(eval(msg.substring(1)));
                    } catch (e) {
                        Ui.message(e);
                    }
                    return false;
                }
                return true;
            },
            Game.Fact
        );
        Game.log = {};
        Game.state;
        Game.MAX_STATES=100;
        Game.STATE_KEY = "lastState-v13";
        Game.urlNum = 0;
        Game.landMap = {};
        Game.landDepMap = {}; // XXX
        Game.usableTools = {};
        Game.auto = false;
        Game.reflexives = {};
        Game.thms = {};
        Game.currentGoal = null;
    }
    Game.prototype.setAnchorPath = function(anchorPath) {
        const Game = this;
        const Ui = this.Ui;
        Game.state.anchorPath = anchorPath;
        if (Game.state.anchorPath == undefined) {
            Ui.document.getElementById("anchor").innerText = "anchor";
            Ui.document.body.className =
                Ui.document.body.className.replace(/enableAllTools /g, "");
        } else {
            // XXX anchorUsableTools : should only enable usable tools
            Ui.document.body.className = "enableAllTools " + Ui.document.body.className;
            Ui.document.getElementById("anchor").innerText = "unanchor";
        }
    };

    Game.prototype.setWorkPath = function(wp) {
        const Game = this;
        const Ui = this.Ui;
        var className = Game.state.anchorPath ? "enableAllTools " : ""; // XXX anchorUsableTools
        if (typeof wp == 'undefined') {
            delete Game.state.workPath;
            if (Ui.workBox) delete Ui.workBox.pathTermArr;
        } else {
            // NB: not the same as orcat's xpath definition. Pass 0 to get the term.
            // TODO: XXX
            function zpath(exp, path) {
                var a = exp, l = path.length, i = 0;
                for (i = 0; i < l; i++) {
                    a=a[path[i]];
                }
                return a;
            }

            Game.state.workPath = wp;
            var pathExp = zpath(Game.state.work.Core[Game.Fact.CORE_HYPS][0], wp);
            // TODO: XXX expects this=fact
            function expToTermArr(exp) {
                if (Array.isArray(exp)) {
                    var args = exp.slice(1).map(expToTermArr.bind(this));
                    args.unshift(this.Skin.TermNames[exp[0]]);
                    return args;
                } else {
                    return exp;
                }
            }

            if (Ui.workBox) Ui.workBox.pathTermArr = expToTermArr.bind(Game.state.work)(pathExp);
            Game.usableTools = Game.engine.getUsableTools(Game.state.work, Game.state.workPath);
            for (var k in Game.usableTools) if (Game.usableTools.hasOwnProperty(k)) {
                var v = Game.usableTools[k];
                //console.log("XXXX Usable tool:" + " tool" + Ui.cssEscape(v[0]) + "_" + v[1]);
                className += " tool" + Ui.cssEscape(v[0]) + "_" + v[1];
            }
        }
        // TODO: XXX: will be slow
        for (var k in Ui.factToShooterBox) if (Ui.factToShooterBox.hasOwnProperty(k)) {
            Ui.factToShooterBox[k].box.tree.onchange();
        }
        Ui.document.body.className = className;

        Ui.redrawSelection();
    };

    // A Facet is a Fact which can be / has been specified by some amount.
    Game.prototype.makeFacet = function(factData) {
        const Game = this;
        const Ui = this.Ui;
        var fact = Game.engine.canonicalize(new Game.Fact(factData));
        fact.Skin.VarNames = fact.Skin.VarNames.map(function(x,i) {
            return "&#" + (i + 0x2460) + ";";
        });
        // Find the var at the given path. Replace all instances of it with the
        // named term or variable. Iff name is a term, its arity must be
        // specified. The new term will get that many new children variables.
        var specify = function(varNum, name, arity, freeMap) {
            //TODO: implement
        }
        return {fact, specify};
    };


    Game.prototype.verifySolution = function(soln) {
        const Game = this;
        var Engine = require('./engine.js');
        var engine = new Engine();
        // TODO: the engine won't discover pushup theorems if they are added
        // before their respective detachers. Maybe we should have the gamestate
        // assign each mark an ordinal for when it was discovered?  For now we
        // just add everything twice, and hope nothing needs 2 other
        // dependencies to be added first.
        soln.deps.forEach(function(dep) {engine.onAddFact(new Game.Fact(dep))});
        soln.deps.forEach(function(dep) {engine.onAddFact(new Game.Fact(dep))});
        var work = engine.canonicalize(Game.startWork(soln.goal));
        var goalName = engine.fingerprint((new Game.Fact(soln.goal)).getMark());
        soln.steps.forEach(function(step) {
            step.args = step.args.map(function(arg){
                if (arg && arg.Core) {
                    return new Game.Fact(arg);
                } else {
                    return arg;
                }
            });
            step.args.unshift(work);
            try {
                work = engine[step.func].apply(engine, step.args);
            } catch (e) {
                throw new Error("at logfp " + step.logFp + ":" + e, e);
            } finally {
                step.args.shift();
            }
        });
        Game.Engine.verifyFact(engine.canonicalize(work));
        // TODO:should not be doing this on every step!
        engine.onAddFact(work);
        return {goalName};
    }
    Game.prototype.verifyDump = function() {
        const Game = this;
        const Ui = this.Ui;
        Game.dump(Game.log, Game.state.work,
                  function(dump) {
                      try {
                          Game.verifySolution(dump);
                          //console.log("Verified dump.")
                      } catch (e) {
                          Ui.message("dump verify failed: \n" + dump.walkName + "\n" + JSON.stringify(dump) + "\n" + e + "\n" + e.stack);
                      }
                  });
    };
    Game.prototype.groundOut = function(fact) {
        const Game = this;
        const Ui = this.Ui;
        try {
            Game.state.url = "#u=" + (Game.urlNum++) + "/" + "#f=" + fact.Skin.Name;
            // Make a protective clone in case ground() mutates but verify fails.
            var workClone = new Game.Fact(JSON.parse(JSON.stringify(Game.state.work)));
            var thm = Game.engine.ground(workClone, fact);
            thm.verify();
            if (Game.currentGoal == null || thm == null) {
                console.warn("null goal " + JSON.stringify(thm));
            } else {
                // NOTE: we used to assert that the Cores matched, but then some
                // special goal start off with a Hyp, and the grounded-out version
                // doesn't have any Hyps. So just assert the Stmt and Dvs match.
                var expected = JSON.stringify(Game.currentGoal.Core.slice(1));
                var actual = JSON.stringify(thm.Core.slice(1));
                if (expected != actual) {
                    throw new Error("Core mismatch! Wanted " + expected
                                    + " found " + actual)
                };
            }
            var finalStep = {func: "ground", args:[Game.stripFact(fact)]};
            Game.dump(Game.log, thm,
                      function(obj) {
                          obj.steps.push(finalStep);
                          try {
                              const {goalName} = Game.verifySolution(obj);
                              console.log("verified ground " + goalName);
                              var out = JSON.stringify(obj);
                              if (typeof(Blob)!=='undefined') {
                                  var msg = Ui.document.createElement('a');
                                  msg.href = URL.createObjectURL(new Blob([out], {type: 'text/plain'}));
                                  msg.innerText = "download solution";
                                  msg.download=`tacro-${goalName}.txt`;
                                  Ui.message(msg);
                                  msg.click();
                              } else if (navigator.clipboard) {
                                  navigator.clipboard.writeText(out)
                                      .then(() => { Ui.message("Dump copied"); })
                                      .catch((e) => { Ui.message("Couldn't copy: " + e); });;
                              }
                          } catch (e) {
                              Ui.message("dump verify failed: " + "\n" + JSON.stringify(obj) + "\n" + e + "\n" + e.stack);
                          }}

                      );
            var newFactFp = Ui.addToShooter(thm);
            Game.currentLand().thms.push(newFactFp.local);
            if (Game.storage.user) {
                // TODO: numbers goals backwards and doesn't carry over
                // anonymously-won points when logging in.
                Game.storage.remote.child("users").
                    child(Game.storage.user.uid).
                    child("points").
                    child(Game.storage.escape(Game.currentLand().name)).
                    child(Game.currentLand().goals.length).
                    set(newFactFp.remote);
            }

            var span = Ui.document.getElementById("achieved");
            span.style.display = '';
            Ui.window.setTimeout(function() {span.className = "animated";}, 10);
            Ui.window.setTimeout(function() {span.className = "";
                                             span.style.display = 'none';}, 1200);
            /* XXX: sync with css */


            Ui.message("");
            Game.setWorkPath([]);
            Game.setAnchorPath();
            Game.currentLand().goals.shift();
            Game.nextGoal();
            Ui.redraw();
        } catch (e) {
            console.log("Error in ground: " + e);
            console.log(e.stack);
            Ui.message(e);
        }
    };
    Game.prototype.stripFact = function(fact) {
        const Game = this;
        const Ui = this.Ui;
        return {Core:fact.Core,
                Skin:{TermNames:fact.Skin.TermNames},
                FreeMaps:fact.FreeMaps};
    };

    Game.prototype.startWork = function(fact) {
        const Game = this;
        const Ui = this.Ui;
        var work = new Game.Fact(fact);
        if (work.Core[Game.Fact.CORE_HYPS].length == 0) {
            work.setHyps([work.Core[Game.Fact.CORE_STMT]]);
        }
        work.FreeMap = fact.FreeMaps.slice(0, work.getCoreTermNames().length - 1);
        work.Skin.HypNames = ["Hyps.0"];
        work.setProof(["Hyps.0"]);

        if (!work.Tree.Cmd) {
            work.setCmd("thm");
        }
        work = Game.engine.canonicalize(work);
        work.Skin.VarNames = work.Skin.VarNames.map(function(x,i) {
            return "&#" + (i + 0x24D0) + ";";
        });
        return work;
    };

    Game.prototype.knowTerms = function(fact) {
        const Game = this;
        const Ui = this.Ui;
        var newTerms = {};
        var numNewTerms = 0;
        fact.Skin.TermNames.forEach(function(termName, termNum) {
            if (!Game.state.knownTerms.hasOwnProperty(termName) &&
                !newTerms.hasOwnProperty(termName)) {
                newTerms[termNum] =  true;
                numNewTerms++;
                var termObj = {text:termName,
                               freeMap:fact.FreeMaps[termNum],
                               arity:-1 // updated in scan() below
                              };
                Game.state.knownTerms[termName] = termObj;
                Game.state.specifyOptions.Terms.push(termObj);
            }
            if (!Ui.termToPane[termName]) {
                Ui.termToPane[termName] = Ui.newPane(termName);
            }
        });
        function scan(exp) {
            if (numNewTerms > 0&& Array.isArray(exp)) {
                if (newTerms[exp[0]]) {
                    var termNum = exp[0];
                    var termName = fact.Skin.TermNames[termNum];
                    Game.state.knownTerms[termName].arity = exp.length - 1;
                    newTerms[termNum] = false;
                    numNewTerms--;
                }
                exp.slice(1).map(scan);
            }
        }
        // TODO: it is possible that a new term could be introduced only in a
        // dependency. But this should never happen in tacro.
        scan(fact.Core[Game.Fact.CORE_STMT]);
        fact.Core[Game.Fact.CORE_HYPS].forEach(scan);
        return newTerms;
    };

    Game.prototype.verifyWork = function(fact) {
        const Game = this;
        const Ui = this.Ui;
        try {
            return Game.Engine.verifyWork(fact);
        } catch (e) {
            if ((fact.Tree.Cmd == "defthm") && (fact.Core[Game.Fact.CORE_HYPS].length > 0)) {
                // TODO: The verifier is persnickety about defthms with
                // hyps. E.g. the fresh goal of proving df-subst. For now, just skip
                // this.
                return e.context;
            }
        }
    };

    Game.prototype.updateGroundButton = function() {
        const Game = this;
        const Ui = this.Ui;
        var ground = Ui.groundButton;
        ground.setAttribute('disabled','disabled');
        ground.className = "disabled";
        ground.onclick = undefined;
        for (var k in Game.reflexives) if (Game.reflexives.hasOwnProperty(k)) {
            var idFact = Game.reflexives[k];
            try {
                // TODO: should not be using exceptions for this
                var workClone = new Game.Fact(JSON.parse(JSON.stringify(Game.state.work)));
                Game.engine.getMandHyps(workClone, [], idFact, [], null, true);
                ground.removeAttribute('disabled');
                ground.className = "enabled";
                ground.onclick = Game.groundOut.bind(Game, idFact);
                break;
            } catch (e) {
                // can't ground this way
                // TODO: need some way to tell the user why. Especially for
                // definition dummy var issues.
            }
        }
    };

    Game.prototype.setWork = function(work) {
        const Game = this;
        const Ui = this.Ui;
        var verified = Game.verifyWork(work);
        // Check for drift from planned FreeVar set. It would be nice to keep these
        // in lockstep but that requires more sophisticted dummy-tracking than we
        // currently do.
        if (Game.currentGoal) {
            var goalFree = Game.currentGoal.Core[Game.Fact.CORE_FREE]
            // The engine sometimes spits out spurious FreeVar constraints of one
            // bindingVar in another. Trim them out before comparing. See the proof
            // of finds for example.
            var bindingVars = verified ? verified.bindingVars : {};
            var workFree = work.Core[Game.Fact.CORE_FREE]
                .filter(f=>!(f[0] in bindingVars));
            var expected = JSON.stringify(goalFree);
            var actual = JSON.stringify(workFree);
            if (expected != actual) {
                Ui.message('FreeVar drift: want ' + expected + " have " + actual);
            }
        }
        Game.state.work = work;
        Game.state.workHash = Game.engine.fingerprint(work);
        Game.updateGroundButton();
        // TODO: might we need an extra var here?
        Game.state.specifyOptions.Vars = work.Skin.VarNames;
        Game.chat.setWork(work);
        // TODO: XXX: will be slow
        for (var k in Ui.factToShooterBox) if (Ui.factToShooterBox.hasOwnProperty(k)) {
            Ui.factToShooterBox[k].box.tree.onchange();
        }
    };

    Game.prototype.save = function(optDumpStep) {
        const Game = this;
        const Ui = this.Ui;
        var stateKey = Game.storage.fpSave("state", Game.state);
        var stateFp = stateKey.local;
        if (stateFp != Game.log.state) {
            Game.log.state = stateFp;
            Game.log.step = optDumpStep;
            var logFp = Game.storage.fpSave("log", Game.log).local;
            Game.storage.local.setItem("childOf/" + Game.log.parent, logFp);
            Game.log = {parent:logFp};
            Game.storage.local.setItem(Game.STATE_KEY, logFp);
            if (Game.storage.user) {
                Game.storage.remote.child("users").child(Game.storage.user.uid).
                    child("state").set(stateKey.remote);
            }
            Ui.history.pushState(logFp, Game.STATE_KEY, "#s=" + stateFp + "/" + Game.state.url);
        }
        Game.verifyDump(Game.log);
    };
    var walkName = 0;
    Game.prototype.dump = function(logObj1, finishedFact, callback) {
        const Game = this;
        const Ui = this.Ui;
        var deps = finishedFact.Tree.Deps.map(function(dep) {
            return {Core:dep[0], Skin:{TermNames:dep[1].map(function(i){
                return finishedFact.Skin.TermNames[i];
            })}, FreeMaps:dep[1].map(function(i){
                return finishedFact.FreeMaps[i];
            })};
        });
        var steps = [];
        function walkLogObj(walkName, fp, logObj) {
            var step = logObj.step;
            if (step && step.goal) {
                callback(({walkName, goal: step.goal, steps, deps}));
            } else {
                if (step) {
                    step.logFp = fp;
                    steps.unshift(step);
                }
                if (logObj.parent) {
                    Game.storage.fpLoad("log", logObj.parent, walkLogObj.bind(null, walkName, logObj.parent));
                } else {
                    Ui.message("Incomplete dump.");
                }
            }
        }
        walkName++;
        walkLogObj(walkName, "start", logObj1);
    };

    Game.prototype.currentLand = function() {
        const Game = this;
        const Ui = this.Ui;
        return Game.state.lands[Game.state.lands.length-1];
    };
    Game.prototype.nextGoal = function() {
        const Game = this;
        const Ui = this.Ui;
        var land = Game.currentLand();
        if (!land.goals || (land.goals.length <= 0)) {
            delete land.goals;
            var nextLand = Game.landDepMap[land.name]; // XXX
            if (nextLand) {
                Game.enterLand(nextLand);
                return Game.nextGoal();
            } else {
                Ui.message("No more lands! You win! Now go write a land.");
                return;
            }
        }
        Game.currentGoal = land.goals[0];
        Game.knowTerms(Game.currentGoal);
        Game.setWork(Game.startWork(Game.currentGoal));
        Game.save({goal:Game.currentGoal});
        Game.setWorkPath([]);
        Game.setAnchorPath();
        Game.engine.resetDummies(Game.state.work);
        return;
    };

    Game.prototype.loadState = function(flat) {
        const Game = this;
        const Ui = this.Ui;
        Game.state = flat;
        Game.setWork(new Game.Fact(Game.state.work));
        Game.setAnchorPath(flat.anchorPath);
        if (Game.currentLand() &&
            Game.currentLand().goals) {
            Game.currentGoal = Game.currentLand().goals[0];
            Ui.message("");
        } else {
            Ui.message("no goals in current land");
        }
    };

    Game.prototype.loadLogFp = function(logFp, cb) {
        const Game = this;
        const Ui = this.Ui;
        Game.storage.fpLoad("log", logFp, function(logObj) {
            Game.storage.fpLoad("state", logObj.state, function(stateObj) {
                Game.log = {parent:logFp};
                Game.expireOldStates(Game.MAX_STATES, logObj);
                Game.loadState(stateObj);
                // TODO: should popstate? double-undo problem.
                Ui.history.pushState(logFp, "state",
                                     "#s=" + logObj.state + "/" + Game.state.url);
                Ui.document.getElementById("forward").style.visibility="visible";
                if (cb) {cb();}
                Ui.redraw();
            });
        });
    };
    Game.prototype.enterLand = function(landData) {
        const Game = this;
        const Ui = this.Ui;
        var land = {
            name:landData.name,
            thms:[],             // hash values
            goals:[],            // structs
        };
        Game.state.lands.push(land);
        land.goals = landData.goals.slice();
        if (landData.axioms) {
            landData.axioms.forEach(function(data) {
                var factFp = Ui.addToShooter(data).local;
                land.thms.push(factFp);
            });
        }
    };


    Game.prototype.cheat = function(n) {
        const Game = this;
        const Ui = this.Ui;
        while (n > 0) {
            var thm = new Game.Fact(Game.state.work);
            thm.Tree.Proof=[];
            //thm.Tree.Cmd = 'stmt'
            thm.setHyps([]);
            var factFp = Ui.addToShooter(thm).local;
            Game.currentLand().thms.push(factFp);
            Ui.message("");
            Game.currentLand().goals.shift();
            Game.nextGoal();
            n--;
            Ui.redraw();
            Game.save();
        }
    };
    Game.prototype.exportFacts = function() {
        const Game = this;
        const Ui = this.Ui;

        console.log("==== EXPORT BEGIN ====");
        Game.state.lands.forEach(function(land) {
            land.thms.forEach(function(thmFp) {
                Game.storage.fpLoad("fact",thmFp, function(fact) {
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
    };




    // called from index.html
    Game.prototype.firebaseLoginLoaded = function() {
        const Game = this;
        const Ui = this.Ui;
        console.log("Firebase Login loaded.");
        Game.storage.authInit(FirebaseSimpleLogin, function(user) {
            if (user) {
                // user authenticated
                var loginNode = Ui.document.getElementById("login");
                loginNode.disabled = false;
                loginNode.innerText = user.displayName;
                loginNode.addEventListener("click", function() {
                    Game.storage.authLogout();
                    return false;
                });
                Game.storage.remote.child("users").child(user.uid).child(Game.STATE_KEY).
                    on('value', function(snap) {
                        var logFp = snap.val();
                        console.log("Found remote logFp: " + logFp);
                    });
            } else {
                // user is logged out
                Ui.document.getElementById("login").innerText = "guest";
                //resetLoginLink
                var link = Ui.document.getElementById("login");
                link.disabled = false;
                link.onclick = function() {
                    Game.storage.authLogin();
                    return false;
                };
            }
        });
    };





    Game.prototype.loadLands = function(lands) { // TODO: this has become totally gefucked PICKUP;
        const Game = this;
        const Ui = this.Ui;
        var numLands = 0;
        for (var n in lands) if (lands.hasOwnProperty(n)) {
            numLands++;
            land = JSON.parse(lands[n].land);
            if (!Game.landMap[land.name]) {
                Game.landMap[land.name] = {land:land};
            }
            if (land.depends && land.depends.length > 0) {
                Game.landDepMap[land.depends[0]] = land; // TODO: multidep
            } else {
                Game.landDepMap[undefined] = land;
                if (Game.state.lands.length == 0) {
                    Game.enterLand(land);
                    Game.nextGoal();
                    Game.state.url = "";
                    Game.save();
                    Ui.redraw();
                }
            }
        }
        console.log("Got checked lands: " + numLands);
    }

    Game.prototype.expireOldStates = function(maxStates, logObj) {
        const Game = this;
        const Ui = this.Ui;
        if (logObj) {
            var parentFp = logObj.parent;
            var stateFp = logObj.state;
            if (maxStates <= 0) {
                console.info("removing state " + stateFp);
                Game.storage.fpRm("log", parentFp);
                Game.storage.fpRm("state", stateFp);
            }
            if (parentFp) {
                Game.storage.fpLoad("log", parentFp,
                                    Game.expireOldStates.bind(Game, maxStates-1));
            }
        }
    };


    if (typeof define === "function" && define.amd) define(tm); else if (typeof module === "object" && module.exports) module.exports = {Game:Game,Ui:Ui};
}();

