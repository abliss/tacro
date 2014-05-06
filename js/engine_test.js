var Fs = require('fs');
var Bencode = require('bencode');
var Crypto = require('crypto');

function getWorld(filename) {
    // Uses eval instead of json to allow comments and naked keys.
    // This is almost certainly a terrible idea.
    return eval("("+Fs.readFileSync(filename,'utf8')+")");
}

function fingerprint(obj) {
    var hash = Crypto.createHash('sha1');
    hash.update(Bencode.encode(obj));
    return "bencode-sha1-" + hash.digest('hex');
}

console.log(fingerprint(getWorld("world_rarr.js")));