var Storage = require('../script/storage.js');
var Engine = require('../script/engine.js');
var storage = new Storage(Engine.fingerprint);
var work = 0;
var finished = false;
function done() {
    work--;
    if (work == 0 && finished) {
        process.exit(0);
    }
}

var fp = storage.fpSave('kind', {foo:1});

work++;
storage.fpLoad('kind', fp, function(x) {
    if (x.foo == 1) {
        done();
    } else {
        throw new Error("storage fp fail");
    }
});
finished = true;

