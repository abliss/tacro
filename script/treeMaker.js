!function(d3) {
    var NODE_SIZE = 3 // XXX Sync with stairs.less
    ,RADIUS = NODE_SIZE * (3/8) //XXX
    ,UNIT = "vw"
    ,optGroupLabels = {
        'Vars' : 'Train',
        'Terms' : 'Promote'
    }

    
    function makeTerm(txt) {
        var s = document.createElement("span");
        s.innerHTML = txt;
        s.className = "termSpan";
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
    function makeVar(txt, path) {
        if (txt === undefined) throw new Error("undef");
        var s = document.createElement("select");
        s.className = "select";
        var ph = s.appendChild(document.createElement("option"));
        ph.innerHTML = txt;
        ph.className = 'placeholder';
        ph.selected = 'selected';
        ph.disabled = 'disabled';
        return s;
    }
    
    // Container for a mutable, d3-compatible graph-structure with mapped
    // HTML DOM nodes.
    function Node(parent, exp, argNumFromZero) {
        this.exp = exp;
        this.div = document.createElement("div");
        this.children = [];
        this.height = 0;
        this.div.className = Array.isArray(exp) ? "term" : "var";
        if (!parent) {
            this.path = [];
            return this;
        }
        this.path = parent.path.slice();
        this.path.push(argNumFromZero + 1);
        this.link = this.div.appendChild(document.createElement("div"));
        this.link.className = "link";
        parent.div.appendChild(this.div);
        parent.children.push(this);
    }

    function makeGraph(parent, exp, i) {
        var n = new Node(parent, exp, i);
        if (Array.isArray(exp)) {
            exp.slice(1).reduce(makeGraph, n);
        }
        if (parent) {
            parent.height = Math.max(parent.height, n.height + 1);
        }
        return parent || n;
    }
    
    // Walk tree, positioning and sizing container divs. Grows sets
    // node.divRect, and grows parentRect to contain it.
    function measureDivs(parentRect, node) {
        if (!parentRect) {
            parentRect = {left:Infinity, right:-Infinity,
                          bottom:-Infinity, top: Infinity};
        }
        var myRect = {top: node.y - NODE_SIZE / 2,
                      left: node.x - NODE_SIZE / 2,
                      right:node.x + NODE_SIZE / 2,
                      bottom:node.y + NODE_SIZE / 2};
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

    function positionDivs(origin, scale, node, index) {
        node.div.style.width = scale * (node.divRect.right - node.divRect.left) + UNIT;
        node.div.style.height = scale * (node.divRect.bottom - node.divRect.top) + UNIT;
        // TODO:imperfect. Sync 100 with css.
        node.div.style["z-index"] = 100 - node.height;
        node.div.style.left = scale * (node.divRect.left - origin.left) + UNIT;
        node.div.style.top = scale * (node.divRect.top - origin.top) + UNIT;
        if (Array.isArray(node.exp)) {
            // term nodes sized and positioned here.
            // var nodes (leaves) positiend and sized through CSS.
            node.span.style.left = scale * (node.x - RADIUS - node.divRect.left) + UNIT;
            node.span.style.top = scale * (node.y - RADIUS - node.divRect.top) + UNIT;
            node.span.style.width =
                node.span.style.height =
                scale * RADIUS * 2 + UNIT;
            if (node.children) {
                node.children.map(positionDivs.bind(null, node.divRect, scale));
            }
        }
        if (node.link) {
            node.link.style.right = scale * (node.divRect.right - node.x) + UNIT;
            //scale * (node.parent.divRect.left - origin.left) + UNIT;
            node.link.style.bottom = scale * (node.divRect.bottom - node.y) + UNIT;
            node.link.style.height = scale * (node.y - node.parent.y) + UNIT;
            // Matrix: should keep 0,0 constant, and move (0,y) to (n.left-p.left,y).
            // Requires transform-origin 100% 100%.
            var matrix = [1, 0,
                          (node.x - node.parent.x) / (node.y - node.parent.y), 1,
                          0, 0];
            node.link.style.transform = 'matrix(' + matrix.join(',') + ')';
        }
    }

    /**
     * Make a tree, i.e. a two-dimensional hierarchical display of an expression. 
     *
     * @param opts.fact the Fact object for looking up operator names, etc.
     * @param opts.exp the expression to draw
     * @param opts.onclick
     * @param opts.size
     * @param opts.editable
     * @param opts.getSpecifyOptions
     * @return a DOM element containing the tree
     */
    var tm = function(opts) {
        var fact = opts.fact
        ,exp = opts.exp
        ,d3tree = d3.layout.tree()
        ,nodes = null
        ,root = document.createElement("div")

        opts.varMap = {} // varName -> [select node]

        root.setAttribute("class", "root");

        // Turning a term into a graph structure for d3. Also constructing
        // nested divs to mirror the graph structure.
        var graph = makeGraph(null, exp);
        root.appendChild(graph.div);

        d3tree.nodeSize([NODE_SIZE, NODE_SIZE]);
        d3tree.separation(function(a,b) {
            return a.parent == b.parent ? 1 : 1.5;
        });
        var nodes = d3tree.nodes(graph);
        
        root.spanMap = {};
        var varMap = {};
        nodes.forEach(function(node) {
            root.spanMap[node.path] = node.div;
            if (opts.onclick) { // TODO: XXX
                node.div.addEventListener("click", function(ev) {
                    opts.onclick(ev, node.path);
                });
            }
            if (Array.isArray(node.exp)) {
                var text = opts.fact.Skin.TermNames[node.exp[0]];
                node.div.className += " name" + cssEscape(text);
                node.span = node.div.appendChild(makeTerm(text));
            } else {
                var varNum = node.exp;
                var text = opts.fact.Skin.VarNames[varNum];
                node.div.className += " name" + varNum;
                node.span = node.div.appendChild(makeVar(text, node.path));

                if (!opts.editable) {
                    node.span.disabled = "disabled";
                }       
                if (!varMap.hasOwnProperty(varNum)) {
                    varMap[varNum] = [];
                }
                varMap[varNum].push(node.span);
                var populator = populateSelect.bind(null, opts.getSpecifyOptions);
                node.span.addEventListener("focus", populator.bind(null, node.span));
                node.span.addEventListener("change", function(ev) {
                    //var value = JSON.parse(select.value);
                    //XXX opts.onChange(path, value[0], value[1]);
                    if (node.span.value !== "null") {
                        varMap[varNum].forEach(function(select2) {
                            if (select2 !== node.span) {
                                populator(select2);
                                select2.value = node.span.value;
                            }
                        });
                    }
                });
            }
        });
        
        var rect = measureDivs(null, graph);
        rect.width = (rect.right - rect.left);
        rect.height = (rect.bottom - rect.top);
        // make fit within bounds. TODO: this is not exactly right
        var largerDim = (rect.width > rect.height) ? "width" : "height";
        var scale = opts.size / rect[largerDim];
        root.style["font-size"] = 0.5 * NODE_SIZE * scale + UNIT;
        root.style.width = scale * rect.width + UNIT;
        root.style.height = scale * rect.height + UNIT;
        root.style.left = root.style.top = 0;
        positionDivs(rect, scale, graph);
        return root;
    };
    
    if (typeof define === "function" && define.amd) define(tm); else if (typeof module === "object" && module.exports) module.exports = tm;
    this.tm = tm;
}(d3);
