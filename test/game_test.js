
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
    //TODO: allow storage.js to init with empty LocalStorage
    const scratchDir = "./scratch1"
    require('fs').rmdirSync(scratchDir, {recursive: true});
    const {Ui, Game} = require('../script/stairs.js');
    const ui = new Ui({});
    ui.startup({
        redrawDelay:1,
        scratchDir,
    });
    await sleep(2);
    var ax1Box = ui.factToShooterBox[ax1Mark].box;
    await specify(ax1Box, [0], 1, "→");
    await specify(ax1Box, [0,0], 0, 0);
    await specify(ax1Box, [0,1], 0, 0);
    await specify(ax1Box, [1,0], 0, 0);
    // TODO: assert removeAttribute disabled
    ax1Box.deployButtons[2].onclick();
    await sleep(2);
    // TODO: assert enabled
    ui.groundButton.onclick();
}

async function test2() {
    //TODO: allow storage.js to init with empty LocalStorage
    const scratchDir = "./scratch2"
    require('fs').rmdirSync(scratchDir, {recursive: true});
    const {Ui, Game} = require('../script/stairs.js');
    var ui = new Ui({});
    ui.startup({
        redrawDelay:1,
        scratchDir,
    });
    await sleep(2);
    var ax1Box = ui.factToShooterBox[ax1Mark].box;
    await specify(ax1Box, [0], 1, "→");
    await specify(ax1Box, [0,0], 0, 0);
    await specify(ax1Box, [0,1], 0, 0);
    await specify(ax1Box, [1,0], 0, 0);
    // TODO: assert removeAttribute disabled
    ax1Box.deployButtons[2].onclick();
    await sleep(2);
    ui = new Ui({});
    ui.startup({
        redrawDelay:1,
        scratchDir,
    });
    await sleep(200);
    // TODO: register promise for observing, then await
    ui.groundButton.onclick();
    //TODO: need a promise to resolve at end of test
    //require('fs').rmdirSync(scratchDir, {recursive: true});
}

async function testAll() {
    await test1();
    await sleep(20);
    await test2();
}

testAll();
