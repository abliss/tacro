var Fs = require('fs');
var Bencode = require('bencode');
var Crypto = require('crypto');

var lands = [];
var state = {};
function getLand(filename) {
    // Uses eval instead of json to allow comments and naked keys.
    // This is almost certainly a terrible idea.
    return eval("("+Fs.readFileSync(filename,'utf8')+")");
}

function fingerprint(obj) {
    var hash = Crypto.createHash('sha1');
    hash.update(Bencode.encode(obj));
    return "bencode-sha1-" + hash.digest('hex');
}

function clone(obj) {
    return JSON.parse(JSON.stringify(obj));
}

function startWork(fact) {
    var work = clone(fact);
    work.Bone.Hyps = [clone(work.Bone.Stmt)];
    work.Bone.Tree = {};
}
lands.push(getLand("land_rarr.js"));
state.land = lands[0];
state.goal = 0;
state.work = clone(words.goals[state.goal]);



