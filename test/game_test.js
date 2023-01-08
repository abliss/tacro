//TODO: allow storage.js to init with empty LocalStorage
require('fs').rmdirSync("./scratch", {recursive: true});
const {Ui, Game} = require('../script/stairs.js');
Ui.startup({
    redrawDelay:1,
});

if (false) {
    const { whyIsNodeStillRunning } = require('why-is-node-still-running');
    setTimeout(function(){
        whyIsNodeStillRunning();
    },1000);
}
function sleep(ms) { return new Promise(resolve => setTimeout(resolve, ms)); }

async function specify(box, path, selectedIndex, ignoredValTODO) {
    var node = path.reduce((node, index) => node.children[index],box.tree.node);
    node.populateSelect();
    node.span.value = selectedIndex;
    node.onchange();
    await sleep(2);
}


const ax1Mark = '[[],[0,0,[0,1,0]],[]];["→"]';

async function test1() {
    await sleep(2);
    var ax1Box = Ui.factToShooterBox[ax1Mark].box;
    await specify(ax1Box, [0], 1, "→");
    await specify(ax1Box, [0,0], 0, 0);
    await specify(ax1Box, [0,1], 0, 0);
    await specify(ax1Box, [1,0], 0, 0);
    // TODO: assert removeAttribute disabled
    ax1Box.deployButtons[2].onclick();    
}

test1();

