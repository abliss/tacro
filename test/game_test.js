
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

const ev = {stopPropagation:function(){}};

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
    await sleep(20);
    var ax2Box = ui.factToShooterBox['[[],[0,[0,0,1],[0,[0,1,2],[0,0,2]]],[]];["→"]'].box;
    await specify(ax2Box, [0,0], 1, 1);
    await specify(ax2Box, [1,1,1], 2, 2);
    await specify(ax2Box, [1,0,0], 3, "→");
    await specify(ax2Box, [1,0,0,0], 0, 0);
    await specify(ax2Box, [1,0,0,1], 1, 1);
    ax2Box.deployButtons[2].onclick();
    await sleep(2);
    ui.workOnclick([1],ev);
    await specify(ax1Box, [0], 1, 1);
    await specify(ax1Box, [1,0], 0, 0);
    ax1Box.deployButtons[1].onclick();
    await sleep(2);
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

async function test3() {
    //TODO: allow storage.js to init with empty LocalStorage
    const scratchDir = "./scratch3"
    require('fs').rmdirSync(scratchDir, {recursive: true});
    const {Ui, Game} = require('../script/stairs.js');
    var ui = new Ui({});
    ui.startup({
        redrawDelay:1,
        scratchDir,
    });
    await sleep(2);
    ui.Game.cheat(8);
    await sleep(16);
    var ax1Box = ui.factToShooterBox[ax1Mark].box;
    var ax3Box = ui.factToShooterBox['[[],[0,[0,[1,0],[1,1]],[0,1,0]],[]];["→","¬"]'].box;
    await specify(ax3Box, [1,0], 0, 0);
    await specify(ax3Box, [1,1], 1, 1);
    ui.workOnclick([2],ev);
    ax3Box.deployButtons[2].onclick();
    await sleep(2);
    ui = new Ui({});
    ui.startup({
        redrawDelay:1,
        scratchDir,
    });
    await sleep(20);
    ui.workOnclick([2],ev);
    await sleep(2);

    var ax1Box = ui.factToShooterBox[ax1Mark].box;
    await specify(ax1Box, [1,0], 3, "¬");
    await specify(ax1Box, [1,1], 3, "¬");
    await specify(ax1Box, [1,1,0], 0, 0);
    await specify(ax1Box, [1,0,0], 1, 1);
    await sleep(200);
    ax1Box.deployButtons[2].onclick();
    await sleep(2);

}

async function test4() {
    //TODO: allow storage.js to init with empty LocalStorage
    const scratchDir = "./scratch4"
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
    if (typeof ui.groundButton.onclick !== "function") {
        throw new Error("expected groundable");
    }
    ui.rewind();
    await sleep(200);
    if (typeof ui.groundButton.onclick === "function") {
        throw new Error("expected ungroundable");
    }
    ui.forward();
    await sleep(200);
    if (typeof ui.groundButton.onclick !== "function") {
        throw new Error("expected groundable");
    }
}
async function test5() { // test double rewind
    //TODO: allow storage.js to init with empty LocalStorage
    const scratchDir = "./scratch5"
    require('fs').rmdirSync(scratchDir, {recursive: true});
    const {Ui, Game} = require('../script/stairs.js');
    const ui = new Ui({});
    ui.startup({
        redrawDelay:1,
        scratchDir,
    });
    ui.Game.auto=true;
    await sleep(2);
    var ax1Box = ui.factToShooterBox[ax1Mark].box;
    ax1Box.deployButtons[2].onclick();
    await sleep(2);
    ax1Box.deployButtons[2].onclick();
    await sleep(2);
    // TODO: assert enabled
    if (typeof ui.groundButton.onclick === "function") {
        throw new Error("expected ungroundable");
    }
    ui.rewind();
    await sleep(200);
    if (typeof ui.groundButton.onclick !== "function") {
        throw new Error("expected groundable");
    }
    ui.rewind();
    await sleep(200);
    if (typeof ui.groundButton.onclick === "function") {
        throw new Error("expected ungroundable");
    }
    ui.forward();
    await sleep(200);
    if (typeof ui.groundButton.onclick !== "function") {
        throw new Error("expected groundable");
    }
}

async function testAll() {
    await test1();
    await sleep(20);
    await test2();
    await sleep(20);
    await test3();
    await sleep(20);
    await test4();
    await test5();
    await sleep(20);
}

testAll();
