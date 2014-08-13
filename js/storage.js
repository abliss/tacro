(function(module) {
    // Storage abstraction. Currently involves localStorage and Firebase,
    // and automatically adapts to browser or node.
    var FB_URL = "https://tacro.firebaseio.com/tacro";
    var nextTick;

    if (typeof process !== 'undefined' && process.nextTick) {
        nextTick = process.nextTick;
    } else if (typeof window !== 'undefined' && window.setTimeout) {
        nextTick = function(cb) {window.setTimeout(cb, 0);}
    } else {
        throw new Error("No nextTick");
    }

    function Storage() {
    };

    if (typeof localStorage === "undefined" || localStorage === null) {
        var LocalStorage = require('node-localstorage').LocalStorage;
        Storage.local = new LocalStorage('./scratch');
    } else {
        Storage.local = localStorage;
    }

    var Firebase;
    var offlineEnabled = false;
    if (typeof OfflineFirebase !== 'undefined') {
        Firebase = OfflineFirebase;
        offlineEnabled = true;
    } else {
        Firebase = require('firebase');
    }
    Storage.remote = new Firebase("https://tacro.firebaseio.com/tacro");

    // Takes a /-delimited firebase path and calls back with the snapshot.
    Storage.remoteGet = function(path, callback) {
        var ref = this.remote;
        path.split("/").forEach(function(step) {ref = ref.child(step);});
        if (offlineEnabled) {
            ref.once('value', callback, null, null, true);
        } else {
            ref.once('value', callback, null, null);
        }
    };

    Storage.authInit = function(FirebaseSimpleLogin, callback) {
        var thatStorage = this;
        this.auth = new FirebaseSimpleLogin(
            this.remote, function(err, user) {
                if (err) {
                    // an error occurred while attempting login
                    console.log(err);
                } else {
                    if (user) {
                        console.log("User: " + user.id + " = " +
                                    user.displayName);
                    } else {
                        console.log("No User.");
                    }
                    thatStorage.user = user;
                    callback(user);
                }
            });
        new Firebase("https://tacro.firebaseio.com/.info/authenticated").
            on("value", function(snap) {
                if (snap.val() == true) {
                    console.log("Now logged in.");
                } else {
                    console.log("Now logged out.");
                }
            });
    }
    ;
    Storage.authLogout = function() {
        this.auth.logout();
    }
    Storage.authLogin = function() {
        this.auth.login("google", { rememberMe: true });
    }
    module.exports = Storage;
})(module);
