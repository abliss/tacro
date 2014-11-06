// does stuff
var Firebase = require('firebase');
var Facts = require('../data/factlog.js').facts;
var Fact = require('../script/fact.js');
var Storage = require('../script/storage.js');
var Engine = require('../script/engine.js');
var Fs = require('fs');

var storage = new Storage();
var rootRef = storage.remote;
var token = Fs.readFileSync("firebase_token.txt", "utf8").replace(/\s*$/,'');

rootRef.auth(token, function(err) {
    if (err) {
        console.log("Auth failed: " + err);
    } else {
        console.log("Auth succeeeded!");
    }
});
rootRef.child("incoming").child("fact").on('child_added', function(snap) {
    var value = snap.val();
    console.log("New fact: " + JSON.stringify(value));
    console.log("  at " + new Date(value.when) + ", " + (new Date() - value.when) + "ms ago");
    try {
        var fact = new Fact(JSON.parse(value.what));
        fact.verify();
        console.log("Verified!");
    } catch (e) {
        console.log("Didn't verify: " + e);
    }
    console.log("");
})
