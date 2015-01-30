!function(d3) {
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
        ,nodeSize = 20 // XXX Sync with stairs.less
        ,radius = nodeSize * (3/8) //XXX
        ,d3tree = d3.layout.tree()
        ,nodes = null
        ,links = null
        ,svg = document.createElementNS("http://www.w3.org/2000/svg", "svg")
        ,linkGroup = document.createElementNS("http://www.w3.org/2000/svg", "g")
        ,nodeGroup = document.createElementNS("http://www.w3.org/2000/svg", "g")
        ,symbols = ['!','@','#','$','%','&','*','?'];

        svg.appendChild(linkGroup);
        svg.appendChild(nodeGroup);
        linkGroup.setAttribute("class", "linkGroup");
        nodeGroup.setAttribute("class", "nodeGroup");
        svg.spanMap = {};

        d3tree.nodeSize([nodeSize, nodeSize]);
        // Turning a term into a graph structure for d3. Also contsructing
        // nested svg groups to mirror the graph structure.
        var graph = (function makeGraph() {
            var path = [];
            var groups = [nodeGroup];
            function recurse(e, i) {
                var g = document.createElementNS("http://www.w3.org/2000/svg", "g");
                groups[groups.length-1].appendChild(g);
                path.push(i + 1);
                groups.push(g);
                var n = {
                    path: path.slice(1),
                    argNum: i,
                    className: "argNum" + i
                };
                if ("number" == typeof e) {
                    n.d = e;
                    n.text = symbols[e];
                    n.className += " treeLeaf treeText" + e;
                } else {
                    n.d = e[0];
                    n.children = e.slice(1).map(recurse);
                    //n.path.push(0);
                    n.text = fact.Skin.TermNames[e[0]];
                    n.className += " treeKids" + (e.length - 1);
                }
                svg.spanMap[n.path] = g;
                g.node = n;
                groups.pop();
                path.pop();
                return n;
            }
            return recurse(exp);
        })();

        nodes = d3tree.nodes(graph);
        links = d3tree.links(nodes);

        // Calculate and set viewbox
        (function() {
            var minX = 0, minY = 0, maxX = 0, maxY = 0;
            nodes.forEach(function(n) {
                minX = Math.min(minX, n.x);
                minY = Math.min(minY, n.y);
                maxX = Math.max(maxX, n.x);
                maxY = Math.max(maxY, n.y);
            });
            minX -= radius + 1;
            minY -= radius + 1;
            maxX += radius + 1;
            maxY += radius + 1;
            var w  = (maxX - minX);
            var h = (maxY - minY);
            svg.setAttribute("viewBox", [minX, minY, w, h].join(' '));
        })();

        function getter(prop) { return function(d) { return d[prop]; };}

        d3.select(linkGroup)
            .selectAll("paths")
            .data(links)
            .enter().append("svg:path")
            .attr("d", d3.svg.diagonal())

        var leafGroups = d3.select(nodeGroup).selectAll("g")
            .datum(function(g) { return this.node; })
            .attr("class", getter("className"))
            .on("click", function(d) {
                if (opts.callback) {
                    // TODO: fix this
                    var f = opts.callback(d.path);
                    if (f) f(d3.event);
                }
            })
        leafGroups.append("svg:circle")
            .attr("cx", getter("x"))
            .attr("cy", getter("y"))
            .attr("r", radius + "px")
        leafGroups.append("svg:text")
            .attr("x", getter("x"))
            .attr("y", getter("y"))
            .text(getter("text"))
            .attr("text-anchor", "middle")
            .attr("transform", "translate(0 " + radius/3.1 + ")")

        return svg;
    };
    

    if (typeof define === "function" && define.amd) define(tm); else if (typeof module === "object" && module.exports) module.exports = tm;
  this.tm = tm;
}(d3);
