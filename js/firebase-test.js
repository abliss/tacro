var Firebase = require('firebase');
var Facts = require('./factlog.js').facts;
var Fact = require('./fact.js');
var Fs = require('fs');

var rootRef = new Firebase("https://tacro.firebaseio.com/tacro");
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


factsRef.set({});
var work = 0;
var finished = false;
function done() {
    work--;
    if (finished && work == 0) {
        process.exit(0);
    }
}
Facts.forEach(function(factData) {
    var fact = new Fact(factData);
    var key = getFbKey(fact);
    work++;
    factsRef.child(key).set(JSON.stringify(factData), function(err) {
        if(err) {
            console.log(err);
        }
        done();
    });
    if (key.length > 700) {
        console.log("key:" + key);
    }
});

var allLands = require('./all_lands.js');
var landsRef = rootRef.child('checked').child('lands');
landsRef.set({});
allLands.forEach(function(land) {
    if (land.axioms) {
        land.axioms = land.axioms.map(JSON.stringify);
    }
    land.goals = land.goals.map(JSON.stringify);
    landsRef.child(land.name).set(land, function(err) {
        if(err) {
            console.log(err);
        }
        done();
    });
});

finished = true;
