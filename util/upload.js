// Uploads lands and facts to firebase; also prepares lands as a locally
// fetchable json.
var Firebase = require('firebase');
var Facts = require('../data/factlog.js').facts;
var Fact = require('../script/fact.js');
var Storage = require('../script/storage.js');
var Fs = require('fs');

var rootRef = new Storage().remote;
var checkedRef = rootRef.child('checked');
var factsRef = checkedRef.child('facts');

var token = Fs.readFileSync("firebase_token.txt", "utf8").replace(/\s*$/,'');

rootRef.auth(token, function(err) {
    if (err) {
        console.log("Auth failed: " + err);
    } else {
        console.log("Auth succeeeded!");
    }
});

function getFbKey(fact) {
    var core = JSON.stringify(fact.Core).
        replace(/\[/g,'(').
        replace(/\]/g,')');
    var terms = encodeURIComponent(JSON.stringify(fact.getCoreTermNames())).
        replace(/\./g,"%2E");
    return core + ";" + terms;
}


// ==== Work counter so node knows when to exit ====
var work = 0;
var finished = false;
function done(err) {
    if (err) {
        console.log("Error: " + err);
    }
    work--;
    if (finished && work == 0) {
        process.exit(0);
    }
}
function set(ref, val) {
    work++;
    ref.set(val, done);
} 
// ====

/*
Facts.forEach(function(factData) {
    var fact = new Fact(factData);
    var key = getFbKey(fact);
    work++;
    set(factsRef.child(key),JSON.stringify(factData));
    if (key.length > 700) {
        console.log("key:" + key);
    }
});
*/
// Combine all lands into one object. JSONify the axioms and goals for fast
// parsing and efficient firebase storage.
var lands = {};
Fs.readdirSync("../data").forEach(function(fn) {
    if (fn.match(/^land_/)) {
        var landData = Fs.readFileSync("../data/" + fn,"utf8");
        var land = eval(landData);
        var path = encodeURIComponent(land.name).replace(/\./g,"%2E");
        if (!path) {
            throw new Error("Bad land " + fn + ": " + landData + "\n=>\n" +
                            JSON.stringify(land));
        }
        lands[path] = {depends: land.depends,
                       land: JSON.stringify(land)};
    }
})
set(rootRef.child('checked').child('lands'), lands);
Fs.mkdir('../rest', function(err) {
    //if (err) throw err;
    Fs.mkdir('../rest/checked', function(err) {
        //if (err) throw err;
        work++;
        Fs.writeFile(
            "../rest/checked/lands.json",
            JSON.stringify(lands), function(err) {
                work--;
                if (err) throw err;
                console.log("Local write complete");
            });
    });
});
finished = true;
