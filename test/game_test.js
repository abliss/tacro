
var Stairs = require('../script/stairs.js');
Stairs.Ui.startup({
    redrawDelay:1,
});

if (false) {
    const { whyIsNodeStillRunning } = require('why-is-node-still-running');
    setTimeout(function(){
        whyIsNodeStillRunning();
    },1000);
}
// TODO: figure out why the script doesn't end naturally. Need to deregister
// event callbacks?
//process.exit(0);
