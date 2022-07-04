(function(module) {
    // Storage abstraction. Currently involves localStorage and Firebase,
    // and automatically adapts to browser or node.
    var OFFLINE = false;
    if ((typeof document == 'undefined') && require && require('fs') && require('fs').existsSync &&
        require('fs').existsSync('use-local-storage')) {
        OFFLINE = true;
    }
    var FB_URL = "https://tacro.firebaseio.com/tacroV001";
    var nextTick;
    var offlineEnabled = false;
    var firebase;

    if (typeof process !== 'undefined' && process.nextTick) {
        nextTick = process.nextTick;
    } else if (typeof window !== 'undefined' && window.FAST_TICK) {
        nextTick = function nextTick(cb) {cb();};
    } else if (typeof window !== 'undefined' && window.setTimeout) {
        nextTick = function nextTick(cb) {window.setTimeout(cb, 0);}
    } else {
        throw new Error("No nextTick");
    }

    function FirebaseStub() {
    }
    FirebaseStub.prototype.child =
        FirebaseStub.prototype.push =
        FirebaseStub.prototype.set =
        FirebaseStub.prototype.once =
        FirebaseStub.prototype.on =
        FirebaseStub.prototype.off =
        FirebaseStub.prototype.name =
        FirebaseStub.prototype.authWithCustomToken =
        function() {
            return new FirebaseStub();
        };
    

    function Storage(fingerprinter) {
        var thatStorage = this;

        if (typeof localStorage === "undefined" || localStorage === null) {
            var LocalStorage = require('node-localstorage').LocalStorage;
            this.local = new LocalStorage('./scratch');
        } else {
            this.local = localStorage;
        }
        this.fpRm = function(kind, fp) {
            var key = "fp/" + kind + "/" + fp;
            this.local.removeItem(key);
        }
        // Save the given obj in a content-addressable location. also upload to
        // firebase. Returns the local key (content-based) and the remote key
        // (uniquely generated).
        this.fpSave = function(kind, obj) {
            var that = this;
            var str = JSON.stringify(obj);
            var fp = fingerprinter(str);
            var key = "fp/" + kind + "/" + fp;
            try {
                this.local.setItem(key, str);
            } catch (e) {
                console.warn("failed to setItem key=" + key.length + " val=" + str.length);
                throw(e);
            }
            var pushRef = this.remote.child("incoming").child(kind).push(
                {
                    "when":Firebase.ServerValue.TIMESTAMP,
                    "what":str
                }, function(err) {
                    if (err) {
                        console.log("Err on push: " + err);
                    } else {
                        that.local.setItem("fb-" + key, pushRef.name());
                    }
                });
            return {local: fp, remote: pushRef.name()};
            return fp;
        },

        // Load an object by its content-addressable key as returned by
        // storage.fpSave
        this.fpLoad = function(kind, fp, cb) {
            var key = "fp/" + kind + "/" + fp;
            var str = this.local.getItem(key);
            if (!str) {
                console.log("Key not found: " + key);
                return;
            }
            var obj = JSON.parse(str);
            nextTick(cb.bind(null, obj));
        };


        if (OFFLINE) {
            firebase = FirebaseStub;
        } else if (typeof OfflineFirebase !== 'undefined') {
            firebase = OfflineFirebase;
            offlineEnabled = true;
        } else {
            firebase = require('firebase');
            Firebase = firebase;
        }
        try {
            this.remote = new firebase(FB_URL);
        } catch (e) {
            console.log("no remote: " + e);
        }
        // Takes a /-delimited firebase path and calls back with the snapshot.
        var fbGet = function(path, callback) {
            var ref = thatStorage.remote;
            path.split("/").forEach(function(step) {ref = ref.child(step);});
            var cbWrap = function(snap){callback(snap.val());};
            if (offlineEnabled) {
                ref.once('value', cbWrap, null, null, true);
            } else {
                ref.once('value', cbWrap, null, null);
            }
        };
        var restGet;
        if (typeof XMLHttpRequest !== 'undefined') {
            // XXXX Override remoteGet to use XHR
            restGet = function(path, callback) {
                var xhr = new XMLHttpRequest();
                xhr.onreadystatechange = function () {
                    if (xhr.readyState === 4) {
                        var obj;
                        try {
                            var obj = eval("(" + xhr.responseText + ")");
                            callback(obj);
                        } catch (e) {
                            console.log("Error evaluating xhr.responsetext:");
                            console.log(e);
                            console.log(e.stack);
                            console.log("text was:");
                            console.log("================");
                            var dump = xhr.responseText;
                            var maxDumpLength = 500;
                            if (dump.length > 500) {
                                dump = "..." + dump.substring(dump.length - 500);
                            }
                            console.log(dump);
                        }
                    } else if (xhr.readyState > 4) {
                        console.log("Bad xhr: " + xhr.readyState);
                    }
                };
                xhr.open("GET", "rest/" + path + ".json?t=" + Date.now(), true);
                xhr.send(null);
            };
        }

        this.remoteGet = function(path, callback) {
            var success = false;
            if (restGet) {
                restGet(path, function(arg) {
                    if (!success) {
                        success = true;
                        callback(arg);
                    }
                });
            }
            fbGet(path, function(arg) {
                if (!success) {
                    success = true;
                    callback(arg);
                }
            });
        };
        this.authInit = function(FirebaseSimpleLogin, callback) {
            this.auth = new FirebaseSimpleLogin(
                this.remote, function(err, user) {
                    if (err) {
                        // an error occurred while attempting login
                        console.log(err);
                    } else {
                        if (user) {
                            console.log("User: " + user.id + " = " +
                                        user.displayName);
                            thatStorage.remote.child("users").child(user.uid).
                                child("displayName").set(user.displayName);
                        } else {
                            console.log("No User.");
                        }
                        thatStorage.user = user;
                        callback(user);
                    }
                });
            new firebase("https://tacro.firebaseio.com/.info/authenticated").
                on("value", function(snap) {
                    if (snap.val() == true) {
                        console.log("Now logged in.");
                    } else {
                        console.log("Now logged out.");
                    }
                });
        }
        ;
        this.authLogout = function() {
            this.auth.logout();
        };
        this.authLogin = function() {
            this.auth.login("google", { rememberMe: true });
        };
        this.escape = function(str) {
            return encodeURIComponent(str).replace(/\./g,"%2E").replace(/%/g,'@');
        };

    }
    module.exports = Storage;
})(module);
