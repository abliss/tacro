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
    var tm = function(fact, exp, nodeSize, treeSize) {
        var d3tree = d3.layout.tree();
        var radius;
        if (nodeSize) {
            d3tree.nodeSize([nodeSize, nodeSize]);
            radius = nodeSize * (3/8); //XXX
        } else {
            d3tree.size(treeSize);
        }
        // Turning a term into a graph structure for d3: since our leaves are
        // numbers and numbers cannot have properties, we must objectify them.
        function objectify(n) {
            return ("number" == typeof n) ? new Number(n) : n;
        }
        d3tree.children(function children(x) {
            // Must return null, not an empty array, for leaves.
            return (!Array.isArray(x) || x.length == 1) ? null : x.slice(1).map(objectify);
        });
        var nodes = d3tree.nodes(exp);
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
        var links = d3tree.links(nodes);
        var el = document.createElementNS("http://www.w3.org/2000/svg", "svg");
        var svg = d3.select(el);
        svg.attr("viewBox", [minX, minY, svgWidth, svgHeight].join(' '));

        if (treeSize) {
            svg.attr("width", treeSize[0])
                .attr("height", treeSize[1]);
        }
        function getText(d) {
            return d.children ? fact.Skin.TermNames[d[0]] : d;
        }
        function getter(prop) { return function(d) {return d[prop]; };}

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
                return "treeNode " +
                    (d.children?("treeKids"+d.children.length):"treeLeaf") +
                    " treeText" + getText(d);});

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
            .attr("font-size", radius / 0.707)
        return svg[0][0];
    };
    

    if (typeof define === "function" && define.amd) define(tm); else if (typeof module === "object" && module.exports) module.exports = tm;
  this.tm = tm;
}(d3);
