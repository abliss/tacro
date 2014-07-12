// Hackish for now.

var Fact = require('./fact.js');
function removeClass(node, className) {
    while (node.className.match(className)) {
        node.className = node.className.replace(className,'');
    }
}

function newVarNamer() {
    var names = ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L'];
    var map = {};
    return function(obj) {
        if (!map[obj]) {
            map[obj] = names.shift();
        }
        return map[obj];
    };
}

function makeTree(doc, fact, exp, path, inputTot, varNamer, spanMap) {
    var termSpan = doc.createElement("span");
    spanMap[path] = termSpan;
    var width = 0;
    var height = 0;
    termSpan.className += " term";
    termSpan.className += " depth" + path.length;
    if (path.length > 0) {
        var inputNum = path[path.length - 1];
        termSpan.className += " input" + inputNum + "of" + inputTot;
    }
    if (Array.isArray(exp)) {
        var termName = fact.Skin.TermNames[exp[0]];
        var arity = exp.length - 1;
        var children = [];
        for (var i = 1; i <= arity; i++) {
            path.push(i);
            children.push(makeTree(doc, fact, exp[i], path, arity, varNamer, spanMap));
            path.pop();
        }
        switch (arity) {
        case 2:
            var rowSpan = doc.createElement("span");
            path.push("r");
            spanMap[path] = rowSpan;
            path.pop();
            termSpan.appendChild(rowSpan);
            rowSpan.className += " hyprow";
            var opSpan = doc.createElement("span");
            path.push("o");
            spanMap[path] = opSpan;
            path.pop();
            rowSpan.appendChild(children[0].span);
            rowSpan.appendChild(opSpan);
            opSpan.className += " operator";
            var txtSpan = doc.createElement("span");
            opSpan.appendChild(txtSpan);
            opSpan.className += " txtBox";
            txtSpan.innerHTML = termName;
            txtSpan.className = " txt";
            width = children[0].width + children[1].width;
            height = children[0].height + children[1].height;
            var opWidth = children[1].width;
            var opHeight = children[0].height;
            opSpan.style.height = "100%";
            children[0].span.style.height = "100%";
            rowSpan.style.height = "" + (100 * children[0].height / height) + "%";
            children[1].span.style.height = "" + (100 * children[1].height / height) + "%";

            rowSpan.style.width = "100%";
            children[0].span.style.width = "" + (100 * children[0].width / width) + "%";
            opSpan.style.width =  "" + (100 * children[1].width / width) + "%";
            children[1].span.style.width = opSpan.style.width;
            termSpan.appendChild(children[1].span);
            break;
        default:
            console.log("TODO: XXX Only arity 2 supported");
            throw new Error("TODO: XXX Only arity 2 supported");
        }
    } else {
        termSpan.className += " variable";
        termSpan.className += " var" + varNamer(exp);
        width = 1;
        height = 1;
        var txtSpan = doc.createElement("span");
        txtSpan.className = " txt";
        txtSpan.style.width="100%";
        txtSpan.style.height="100%";
        termSpan.appendChild(txtSpan);
        termSpan.className += " txtBox";
        var innerHTML = varNamer(exp);
        var whichChild = path[path.length - 1];
        for (var i = path.length  - 1; (i >= 0) && path[i] == whichChild; i--) {
            if (whichChild == 1) {
                innerHTML = innerHTML + ")";
            } else if (whichChild == 0) {
                innerHTML = "(" + innerHTML;
            }
        }
        txtSpan.innerHTML = innerHTML;
    }
    return ({span:termSpan, width:width, height:height});
}

function makeThmBox(fact) {
	var stmt = fact.Core[Fact.CORE_STMT];
    var termBox = document.createElement("span");
    termBox.className += " termbox";
    var spanMap = {};
    var tree = makeTree(document, fact, stmt, [], -1, newVarNamer(), spanMap);
    termBox.appendChild(tree.span);
    tree.span.style.width = "100%";
    tree.span.style.height = "100%";
    termBox.style.width = "" + (2 * tree.width) + "em";
    termBox.style.height ="" + (2 * tree.height) + "em";
    termBox.spanMap = spanMap;
    termBox.tree = tree;
    return termBox;
}


function size(thmBox, ems) {
    thmBox.style.width = ems + "em";
    thmBox.style.height = ems + "em";
    thmBox.tree.span.style["font-size"] = "" + (50 * ems / thmBox.tree.width) + "%";
}

function addToShooter(fact) {
    var box;
	if (fact.Core[Fact.CORE_HYPS].length == 0) {
		box = makeThmBox(fact);
		size(box, 4);
		document.getElementById("shooterTape").appendChild(box);
	} // TODO: handle axioms with hyps
}

/*
var thmsToAdd = exports.theory.theorems();
function doWork() {
    if (thmsToAdd.length > 0) {
        addToShooter(thmsToAdd.shift());
        window.setTimeout(doWork, 10);
    }
}
doWork();

var box = makeThmBox("rarr_rarr_A_rarr_B_C_rarr_rarr_A_B_rarr_A_C");
size(box, box.tree.width * 2);
document.getElementById("well").appendChild(box);

function nextStep() {
}
document.body.onclick = nextStep;
document.body.onkeyup = nextStep;
document.body.focus();
*/

var allLands = require('./all_lands.js');
var landMap = {};
var landDepMap = {}; // XXX
allLands.forEach(function(land) {
	landMap[land.name] = land;
	landDepMap[land.depends[0]] = land;
});

var land = landDepMap[undefined];
land.axioms.forEach(addToShooter);

var goal = land.goals[0];
var box = makeThmBox(goal);
size(box, box.tree.width * 2);
document.getElementById("well").appendChild(box);
