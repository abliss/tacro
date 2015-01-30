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
        ,svg = null
        
        d3tree.nodeSize([nodeSize, nodeSize]);
        // Turning a term into a graph structure for d3: since our leaves are
        // numbers and numbers cannot have properties, we must objectify them.
        var graph = (function makeGraph() {
            var path = [];
            function recurse(e, i) {
                path.push(i);
                var n = ("number" == typeof e) ? new Number(e) : e.map(recurse);
                n.path = path.slice(1);
                path.pop();
                return n;
            }
            return recurse(exp);
        })();
        
        
        d3tree.children(function children(x) {
            // Must return null, not an empty array, for leaves.
            return (!Array.isArray(x) || x.length == 1) ? null : x.slice(1);
        });
        nodes = d3tree.nodes(graph);
        links = d3tree.links(nodes);
        svg = d3.select(document.createElementNS("http://www.w3.org/2000/svg", "svg"));

        !function() {
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
            var svgWidth  = (maxX - minX);
            var svgHeight = (maxY - minY);
            svg.attr("viewBox", [minX, minY, svgWidth, svgHeight].join(' '));
        }();

        function getText(d) {
            var symbols = ['!','@','#','$','%','&','*','?'];
            return d.length ? fact.Skin.TermNames[d[0]] : symbols[d];
        }
        function getter(prop) { return function(d) {return d[prop]; };}


        var spanMap = {};

        svg.selectAll("paths")
            .data(links)
            .enter().append("svg:path")
            .attr("d", d3.svg.diagonal())
            .attr("class", "treeLink");
        var gEnter = svg.selectAll("nodes")
            .data(nodes)
            .enter()
            .append("svg:g")
            .attr("class", function(d) {
                return "treeNode "+ 
                    ((d.length >= 0) ?
                     ("treeKids" + d.length) :
                     ("treeLeaf treeText" + d));})
            .on("click", function(d) {
                if (opts.callback) {
                    console.log("Clicked: " + JSON.stringify(d));
                    console.log("At: " + JSON.stringify(d.path));
                    var f = opts.callback(d.path);
                    if (f) f(d3.event);
                }
            })
            .each(function(d) {
                spanMap[d.path] = this;
            })
        gEnter.append("svg:circle")
            .attr("cx", getter("x"))
            .attr("cy", getter("y"))
            .attr("r", radius + "px")
        gEnter.append("svg:text")
            .attr("x", getter("x"))
            .attr("y", getter("y"))
            //.text(function(d) {return d.children?getText(d):""})
        .text(getText)
            .attr("text-anchor", "middle")
            .attr("transform", "translate(0 " + radius/3.1 + ")")
        var tree = svg[0][0];
        tree.spanMap = spanMap;
        
        return tree;
    };
    

    if (typeof define === "function" && define.amd) define(tm); else if (typeof module === "object" && module.exports) module.exports = tm;
  this.tm = tm;
}(d3);
