!function(d3) {
    var nodeSize = 3 // XXX Sync with stairs.less
    ,radius = nodeSize * (3/8) //XXX
    ,UNIT = "vw"
    function makeSpan(txt) {
        if (txt === undefined) throw new Error("undef");
        var s = document.createElement("span");
        s.innerHTML = txt;
        return s;
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
        ,symbols = ['!','@','#','$','%','&','*','?'];

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
        var graph = (function makeGraph() {
            var ancestors = [{div: nodeGroup, path:[]}];
            var numArgs = null;
            var tool = null;
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
                root.spanMap[n.path] = n.div;
                if (opts.onclick) {
                    n.div.addEventListener("click", function(ev) {
                        opts.onclick(ev, n.path);
                    });
                }
                    
                n.div.className = "depth" + (n.path.length) +
                    " input" + (i+1) + "of" + numArgs +
                    " tool" + tool
                if (Array.isArray(exp)) {
                    var termName = fact.Skin.TermNames[exp[0]];
                    tool = cssEscape(termName);
                    n.span = makeSpan(termName);
                    n.div.appendChild(n.span);
                    n.div.className += " treeKids" + (exp.length - 1);
                    numArgs = exp.length - 1;
                    ancestors.push(n);
                    n.children = exp.slice(1).map(recurse);
                    n.children.map(function(c) {
                        n.height = Math.max(n.height, c.height + 1);
                    });
                    ancestors.pop();
                } else {
                    n.span = makeSpan(symbols[exp]);
                    n.div.appendChild(n.span);
                    n.div.className += " treeLeaf treeText" + exp;
                }
                return n;
            }
            return recurse(exp);
        })();

        
        links = d3tree.links(d3tree.nodes(graph));

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
        var scale = opts[largerDim] / rect[largerDim];
        nodeGroup.style["font-size"] = 0.5 * nodeSize * scale + UNIT;
        nodeGroup.style.width = scale * rect.width + UNIT;
        nodeGroup.style.height = scale * rect.height + UNIT;
        nodeGroup.style.left=0;
        nodeGroup.style.top=0;
        var origins = [rect]
        function positionDivs(node) {
            node.div.style.width = scale * (node.divRect.right - node.divRect.left) + UNIT;
            node.div.style.height = scale * (node.divRect.bottom - node.divRect.top) + UNIT;
            node.div.style["z-index"] = graph.height - node.height; // TODO:imperfect
            var origin = origins[origins.length-1];
            node.div.style.left = scale * (node.divRect.left - origin.left) + UNIT;
            node.div.style.top = scale * (node.divRect.top - origin.top) + UNIT;
            node.span.style.left = scale * (node.x - radius - node.divRect.left) + UNIT;
            node.span.style.top = scale * (node.y - radius - node.divRect.top) + UNIT;
            node.span.style.width =
                node.span.style.height =
                node.span.style['border-radius'] =
                scale * radius * 2 + UNIT;

            if (node.children) {
                origins.push(node.divRect);
                node.children.map(positionDivs);
                origins.pop();
            }
        }
        positionDivs(graph);
        return root;
    };
    

    if (typeof define === "function" && define.amd) define(tm); else if (typeof module === "object" && module.exports) module.exports = tm;
    this.tm = tm;
}(d3);
