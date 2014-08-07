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
Facts.forEach(function(factData) {
    var fact = new Fact(factData);
    var key = getFbKey(fact);
    work++;
    factsRef.child(key).set(factData, function(err) {
        if(err) {
            console.log(err);
        }
        work--;
        if (finished && work == 0) {
            process.exit(0);
        }
    });
    if (key.length > 700) {
        console.log("key:" + key);
    }
});
finished = true;