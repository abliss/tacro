// does stuff
var Firebase = require('firebase');
var Facts = require('../data/factlog.js').facts;
var Fact = require('../script/fact.js');
var Storage = require('../script/storage.js');
var Engine = require('../script/engine.js');
var Fs = require('fs');

var storage = new Storage(Engine.fingerprint);
var rootRef = storage.remote;
var token = Fs.readFileSync("firebase_token.txt", "utf8").replace(/\s*$/,'');

function fbEscape(str) {
    return encodeURIComponent(str).replace(/\./g,"%2E");
}

function getFbKey(fact) {
    var core = JSON.stringify(fact.Core).
        replace(/\[/g,'(').
        replace(/\]/g,')');
    var terms = fact.getCoreTermNames().map(fbEscape).join(",");
    return core + ";" + terms + ";" + fbEscape(Engine.fingerprint(fact));
}

rootRef.authWithCustomToken(token, function(err, authData) {
    if (err) {
        console.log("Auth failed: " + err);
    } else {
        console.log("Auth succeeeded!" + authData);
    }
});

rootRef.child("incoming").child("fact").on('child_added', function(snap) {
    var value = snap.val();
    if (!value) {
        return;
    }
    console.log("New fact: " + JSON.stringify(value));
    console.log("  at " + new Date(value.when) + ", " + (new Date() - value.when) + "ms ago");
    try {
        var fact = new Fact(JSON.parse(value.what));
        var key = getFbKey(fact);

        if (fact.Tree.Cmd != 'stmt') {
            fact.verify();
            rootRef.child("checked").child("fact").child("byMark").child(key).set(value.what);
        }
        rootRef.child("checked").child("fact").child("pushed").child(snap.key()).set(value);
        snap.ref().remove();
        console.log("Verified! " + key);
    } catch (e) {
        try {
            var fact = new Fact(JSON.parse(value.what));
            if (!fact.Tree.Cmd) {
                snap.ref().remove();
            }
        } catch (e2) {
            console.log("Didn't verify: " + e);
        }
    }
    console.log("");
})
