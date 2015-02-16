!function(d3) {
    var nodeSize = 3 // XXX Sync with stairs.less
    ,radius = nodeSize * (3/8) //XXX
    ,UNIT = "vw"
    ,optGroupLabels = {
        'Vars' : 'Train',
        'Terms' : 'Promote'
    }
    function makeTerm(txt) {
        var s = document.createElement("span");
        s.innerHTML = txt;
        return s;
    }

    function populateSelect(specifyOptionsProvider, select) {
        var specifyOptions = specifyOptionsProvider();
        var oldValue = select.value;
        while (select.lastChild != select.firstChild) {
            select.removeChild(select.lastChild);
        }
        for (var k in specifyOptions) if (specifyOptions.hasOwnProperty(k)) {
            var og = select.appendChild(document.createElement("optGroup"));
            og.label = optGroupLabels.hasOwnProperty(k) ?
                optGroupLabels[k] : k;
            og.className = k;
            specifyOptions[k].forEach(function(o, i) {
                var opt = og.appendChild(
                    document.createElement("option"));
                opt.value = JSON.stringify([k, i]);
                if (opt.value == oldValue) {
                    opt.selected = "selected";
                }
                opt.innerHTML = o;
            });
        }
    }
    
    // TODO: ugly: varMap managed here but created elsewhere
    function makeVar(varMap, txt, path, opts) {
        if (txt === undefined) throw new Error("undef");
        if (!varMap.hasOwnProperty(txt)) {
            varMap[txt] = [];
        }
        var s = document.createElement("select");
        varMap[txt].push(s);
        s.className = "select";
        var ph = s.appendChild(document.createElement("option"));
        ph.innerHTML = txt;
        ph.className = 'placeholder';
        ph.selected = 'selected';
        ph.disabled = 'disabled';
        if (!opts.editable) {
            s.disabled = "disabled";
            return s;
        }
        
        var populator = populateSelect.bind(null, opts.getSpecifyOptions);
        s.addEventListener("focus", populator.bind(null, s));
        s.addEventListener("change", function(ev) {
            var value = JSON.parse(s.value);
            if (value !== null) {
                varMap[txt].forEach(function(select) {
                    if (select !== s) {
                        populator(select);
                        select.value = s.value;
                    }
                });
                //XXX opts.onChange(path, value[0], value[1]);
            }
        });

        return s;
    }
    
    function makeGraph(exp, groupDiv, spanMap, opts) {
        var ancestors = [{div: groupDiv, path:[], tool: null, numArgs: null}];
        function recurse(exp, i) {
            var parent = ancestors[ancestors.length-1];
            var n = {
                exp: exp,
                path: parent.path.slice(),
                div: document.createElement("div"),
                height: 1
            };
            if (i !== undefined) {
                n.path.push(i + 1);
            }
            parent.div.appendChild(n.div);
            spanMap[n.path] = n.div;
            if (opts.onclick) {
                n.div.addEventListener("click", function(ev) {
                    opts.onclick(ev, n.path);
                });
            }
            
            n.div.className = "depth" + (n.path.length) +
                " input" + (i+1) + "of" + parent.numArgs +
                " tool" + parent.tool
            if (Array.isArray(exp)) {
                var termName = opts.fact.Skin.TermNames[exp[0]];
                n.tool = cssEscape(termName);
                n.span = makeTerm(termName);
                n.div.appendChild(n.span);
                n.div.className += " treeKids" + (exp.length - 1);
                n.numArgs = exp.length - 1;
                ancestors.push(n);
                n.children = exp.slice(1).map(recurse);
                n.children.map(function(c) {
                    n.height = Math.max(n.height, c.height + 1);
                });
                ancestors.pop();
            } else {
                n.span = makeVar(opts.varMap, opts.fact.Skin.VarNames[exp], n.path,
                                 opts);
                n.div.appendChild(n.span);
                n.div.className += " treeLeaf treeText" + exp;
            }
            return n;
        }
        return recurse(exp);
    }
    
    /**
     * Make a tree, i.e. a two-dimensional hierarchical display of an expression. 
     *
     * @param fact the Fact object for looking up operator names, etc.
     * @param exp the expression to draw
     * @param nodeSize dimensions of one node. Exclusive of treeSize
     * @param treeSize dimenions of whole tree. Exclusive of nodeSize
     * @return a DOM element containing the tree
     */
    var tm = function(opts) {
        var fact = opts.fact
        ,exp = opts.exp
        ,d3tree = d3.layout.tree()
        ,nodes = null
        ,links = null
        ,root = document.createElement("div")
        ,linkGroup = document.createElement("div")
        ,nodeGroup = document.createElement("div")

        opts.varMap = {} // varName -> [select node]

        root.setAttribute("class", "root");
        root.appendChild(linkGroup);
        root.appendChild(nodeGroup);
        linkGroup.setAttribute("class", "linkGroup");
        nodeGroup.setAttribute("class", "nodeGroup");
        root.spanMap = {};

        d3tree.nodeSize([nodeSize, nodeSize]);
        d3tree.separation(function(a,b) {
            return a.parent == b.parent ? 1 : 1.5;
        });
        // Turning a term into a graph structure for d3. Also constructing
        // nested divs to mirror the graph structure.
        var graph = makeGraph(exp, nodeGroup, root.spanMap, opts);
        
        d3tree.nodes(graph);

        // Walk tree, positioning and sizing container divs. Grows sets
        // node.divRect, and grows parentRect to contain it.
        function measureDivs(parentRect, node) {
            var myRect = {top: node.y - nodeSize / 2,
                          left: node.x - nodeSize / 2,
                          right:node.x + nodeSize / 2,
                          bottom:node.y + nodeSize / 2};
            if (node.children) {
                myRect = node.children.reduce(measureDivs, myRect);
                node.divRect = myRect;
            } else {
                node.divRect = myRect;
            }
            parentRect.top = Math.min(parentRect.top, myRect.top);
            parentRect.left = Math.min(parentRect.left, myRect.left);
            parentRect.right = Math.max(parentRect.right, myRect.right);
            parentRect.bottom = Math.max(parentRect.bottom, myRect.bottom);
            return parentRect;
        }
        var rect = {left:Infinity, right:-Infinity, bottom:-Infinity, top: Infinity};
        measureDivs(rect, graph, 0);
        rect.width = (rect.right - rect.left);
        rect.height = (rect.bottom - rect.top);
        // make fit within bounds. TODO: this is not exactly right
        var largerDim = (rect.width > rect.height) ? "width" : "height";
        var scale = opts.size / rect[largerDim];
        nodeGroup.style["font-size"] = 0.5 * nodeSize * scale + UNIT;
        nodeGroup.style.width = linkGroup.style.width = scale * rect.width + UNIT;
        nodeGroup.style.height = linkGroup.style.height = scale * rect.height + UNIT;
        nodeGroup.style.left = nodeGroup.style.top = 0;
        var origins = [rect]
        function positionDivs(node, index) {
            node.div.style.width = scale * (node.divRect.right - node.divRect.left) + UNIT;
            node.div.style.height = scale * (node.divRect.bottom - node.divRect.top) + UNIT;
            node.div.style["z-index"] = graph.height - node.height; // TODO:imperfect
            var origin = origins[origins.length-1];
            node.div.style.left = scale * (node.divRect.left - origin.left) + UNIT;
            node.div.style.top = scale * (node.divRect.top - origin.top) + UNIT;
            if (Array.isArray(node.exp)) {
                // term nodes sized and positioned here.
                // var nodes (leaves) positiend and sized through CSS.
                node.span.style.left = scale * (node.x - radius - node.divRect.left) + UNIT;
                node.span.style.top = scale * (node.y - radius - node.divRect.top) + UNIT;
                node.span.style.width =
                    node.span.style.height =
                    scale * radius * 2 + UNIT;
                if (node.children) {
                    origins.push(node.divRect);
                    node.children.map(positionDivs);
                    origins.pop();
                }
            }
            if (node.parent) {
                // LINKS
                var link = document.createElement("div");
                linkGroup.appendChild(link);
                link.className = "link";
                link.style.left = scale * (node.parent.x - rect.left) + UNIT;
                link.style.top = scale * (node.parent.y - rect.top) + UNIT;
                link.style.height = scale * (node.y - node.parent.y) + UNIT;
                // Matrix: should keep 0,0 constant, and move (0,y) to (n.x-p.x,y).
                var matrix = [1, 0,
                    (node.x - node.parent.x) / (node.y - node.parent.y), 1,
                    0, 0];
                link.style.transform = 'matrix(' + matrix.join(',') + ')';
                
            }
        }
        positionDivs(graph);
        return root;
    };
    
    tm.addTerm = function(termName) {
    };
    
    if (typeof define === "function" && define.amd) define(tm); else if (typeof module === "object" && module.exports) module.exports = tm;
    this.tm = tm;
}(d3);
