!function(d3) {
    var NODE_SIZE = 3 // XXX Sync with stairs.less
    ,RADIUS = NODE_SIZE * (3/8) //XXX
    ,UNIT = "vw"
    ,optGroupLabels = {
        'Vars' : 'Train',
        'Terms' : 'Promote'
    },  d3tree = d3.layout.tree();

    d3tree.nodeSize([NODE_SIZE, NODE_SIZE]);
    d3tree.separation(function(a,b) {
        return a.parent == b.parent ? 1 : 1.5;
    });
    
    // Container for a mutable, d3-compatible graph-structure with mapped
    // HTML DOM nodes.
    function Node(parent, exp, argNumFromZero) {
        this.exp = exp;
        this.div = document.createElement("div");
        this.children = [];
        this.height = 0;
        this.div.className = Array.isArray(exp) ? "term" : "var";
        if (!(parent instanceof Node)) {
            this.path = [];
            this.root = parent;
            parent.node = this;
            return this.decorate();;
        }
        this.root = parent.root;
        this.path = parent.path.slice();
        this.path.push(argNumFromZero + 1);
        this.link = this.div.appendChild(document.createElement("div"));
        this.link.className = "link";
        parent.div.appendChild(this.div);
        parent.children.push(this);
        return this.decorate();
    }

    Node.prototype.makeTerm = function(txt) {
        var s = document.createElement("span");
        s.innerHTML = txt;
        s.className = "termSpan";
        return s;
    }
   
    Node.prototype.makeVar = function(txt) {
        if (txt === undefined) throw new Error("undef");
        var s;
        if (this.root.getSpecifyOptions) {
            s = document.createElement("select");
            var ph = s.appendChild(document.createElement("option"));
            ph.innerHTML = txt;
            ph.className = 'placeholder';
            ph.selected = 'selected';
            ph.disabled = 'disabled';
        } else {
            s = document.createElement("span");
            s.innerHTML = txt;
        }
        s.className = "select";            
        return s;
    }

    // Must be called after the root has been set up.
    Node.prototype.decorate = function() {
        var root = this.root;
        root.spanMap[this.path] = this.div;
        if (Array.isArray(this.exp)) {
            var text = root.fact.Skin.TermNames[this.exp[0]];
            this.div.className += " name" + cssEscape(text);
            this.span = this.div.appendChild(this.makeTerm(text));
        } else {
            var varNum = this.exp;
            var text = root.fact.Skin.VarNames[varNum];
            this.div.className += " name" + varNum;
            this.span = this.div.appendChild(this.makeVar(text, root.getSpecifyOptions));
            if (root.getSpecifyOptions) {
                // Editable: wire up select element
                if (!root.varMap.hasOwnProperty(varNum)) {
                    root.varMap[varNum] = [];
                }
                root.varMap[varNum].push(this);
                this.span.addEventListener("focus", this.populateSelect.bind(this));
                this.span.addEventListener("change", this.onchange.bind(this));
            }
        }
        if (root.onclick) {
            this.div.addEventListener("click", root.onclick.bind(this, this.path));
            this.span.addEventListener("click", root.onclick.bind(this, this.path));
        }
        return this;
    };

    Node.prototype.populateSelect = function() {
        var specifyOptions = this.root.getSpecifyOptions();
        var select = this.span;
        var oldValue = select.value;
        var optionValues = this.optionValues = [];
        while (select.lastChild != select.firstChild) {
            select.removeChild(select.lastChild);
        }
        for (var k in specifyOptions) if (specifyOptions.hasOwnProperty(k)) {
            var og = select.appendChild(document.createElement("optGroup"));
            og.label = optGroupLabels.hasOwnProperty(k) ?
                optGroupLabels[k] : k;
            og.className = k;
            specifyOptions[k].forEach(function(val) {
                var opt = og.appendChild(
                    document.createElement("option"));
                var optIndex = optionValues.push({
                    group: k,
                    value: val,
                });
                opt.value = optIndex - 1;
                if (opt.value == oldValue) {
                    opt.selected = "selected";
                }
                // Var values are simple strings; Term values have a text property.
                opt.innerHTML = val.text ? val.text : val;
            });
        }
    };

    Node.prototype.onchange = function(ev) {
        var that = this;
        var promise;
        if (this.children !== undefined && this.children.length > 0) {
            this.root.varMap[this.exp].forEach(function(node) {
                node.x = node.parent.x;
                node.y = node.parent.y;
            });
            promise = this.redrawP();
        } else {
            promise = Promise.resolve();
        }
        var specifyOption = this.optionValues[this.span.value];

        var newChildren = [];
        if (specifyOption.group == 'Terms') {
            for (var i = 0; i < specifyOption.value.arity; i++) {
                // TODO: reuse old vars?
                this.root.maxVar++;
                newChildren.push(this.root.maxVar);
                this.root.fact.nameVar("&#" + (0x2460 + this.root.maxVar) + ";"); // XXX
            }
        }

        this.root.varMap[this.exp].forEach(function(other) {
            if (other !== that) {
                other.populateSelect();
                other.span.value = that.span.value;
            }
            other.setSpecifyOption(specifyOption, newChildren);
        });
        promise.then(this.redrawP.bind(this));
    };
    
    // Trigger a redraw right now; fulfill the promise when all anims are done.
    Node.prototype.redrawP = function() {
        this.layout();
        return Promise.resolve(); // XXX TODO
    };
    
    Node.prototype.setSpecifyOption = function(specifyOption, newChildren) {
        var that = this;
        if (this.children) {
            this.children.forEach(function(node) {
                that.div.removeChild(node.div);
            });
            delete this.children;
        }
        if (newChildren) {
            this.children = [];
            newChildren.reduce(makeGraph, this);
        }

    };

    // ==== Reduce methods ====
    function makeGraph(parent, exp, i) {
        var n = new Node(parent, exp, i);
        if (Array.isArray(exp)) {
            exp.slice(1).reduce(makeGraph, n);
        } else {
            n.root.maxVar = Math.max(n.root.maxVar, exp);
        }
        if (parent instanceof Node) {
            parent.height = Math.max(parent.height, n.height + 1);
            return parent;
        } else {
            return n;
        }
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
        if (node.children) {
            // term nodes sized and positioned here.
            node.span.style.left = scale * (node.x - RADIUS - node.divRect.left) + UNIT;
            node.span.style.top = scale * (node.y - RADIUS - node.divRect.top) + UNIT;
            node.span.style.width =
                node.span.style.height =
                scale * RADIUS * 2 + UNIT;
            if (node.children) {
                node.children.map(positionDivs.bind(null, node.divRect, scale));
            }
        } else {
            // var nodes (leaves) positiend and sized through CSS.
            var ns = node.span;
            ns.style.left = ns.style.top = ns.style.width = ns.style.height = '';
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

    // TODO: this should really be attached to the Root object, not the graph node?
    Node.prototype.layout = function() {
        var nodes = d3tree.nodes(this.root.node);
        var rect = measureDivs(null, this.root.node);
        rect.width = (rect.right - rect.left);
        rect.height = (rect.bottom - rect.top);
        // make fit within bounds. TODO: this is not exactly right
        largerDim = (rect.width > rect.height) ? "width" : "height";
        scale = this.root.size / rect[largerDim];
        this.root.div.style["font-size"] = 0.5 * NODE_SIZE * scale + UNIT;
        positionDivs(rect, scale, this.root.node);
        return rect;
    };
    
    /**
     * Make a tree, i.e. a two-dimensional hierarchical display of an expression. 
     *
     * @param opts.fact the Fact object for looking up operator names, etc.
     * @param opts.exp the expression to draw
     * @param opts.onclick
     * @param opts.size
     * @param opts.getSpecifyOptions
     * @return a DOM element containing the tree
     */
    var tm = function(opts) {
        var rootDiv = document.createElement("div")
        rootDiv.setAttribute("class", "root");

        // Turning a term into a graph structure for d3. Also constructing
        // nested divs to mirror the graph structure.
        var root = {
            div: rootDiv,
            spanMap: {},
            varMap: {},
            onclick: opts.onclick,
            fact: opts.fact,
            getSpecifyOptions: opts.getSpecifyOptions,
            size: opts.size,
            maxVar: -1,
        };
        var graph = makeGraph(root, opts.exp);
        rootDiv.appendChild(graph.div);
        graph.layout();
        rootDiv.spanMap = root.spanMap;
        return rootDiv;
    };
    
    if (typeof define === "function" && define.amd) define(tm); else if (typeof module === "object" && module.exports) module.exports = tm;
    this.tm = tm;
}(d3);
