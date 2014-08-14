var Storage = require('../script/storage.js');

var work = 0;
var finished = false;
function done() {
    work--;
    if (work == 0 && finished) {
        process.exit(0);
    }
}

var fp = Storage.saveFp('kind', {foo:1});

work++;
Control.storage.loadFp('kind', fp, function(x) {
    if (x.foo == 1) {
        done();
    } else {
        throw new Error("storage fp fail");
    }
});
finished = true;

