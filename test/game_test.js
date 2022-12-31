
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

const ax1Mark = '[[],[0,0,[0,1,0]],[]];["→"]';
setTimeout(function(){
    var ax1Box = Ui.factToShooterBox[ax1Mark].box;
    var a = ax1Box.tree.node.children[0];
    a.populateSelect();
    a.span.value = 1;
    a.onchange();
    console.log( JSON.stringify(ax1Box.tree.getTermArr()) );
},10);

// TODO: figure out why the script doesn't end naturally. Need to deregister
// event callbacks?
//process.exit(0);
