(function(module) {
    // Storage abstraction. Currently involves localStorage and Firebase,
    // and automatically adapts to browser or node.
    var OFFLINE = false;
    if (typeof process !== 'undefined' && process.env &&
        process.env["TACRO_USE_LOCAL_STORAGE"]) {
        OFFLINE = true;
    }
    var FB_URL = "https://tacro.firebaseio.com/tacroV001";
    var nextTick;
    var offlineEnabled = false;
    var firebase;


    function FirebaseStub() {
    }
    FirebaseStub.prototype.child =
        FirebaseStub.prototype.push =
        FirebaseStub.prototype.set =
        FirebaseStub.prototype.once =
        FirebaseStub.prototype.on =
        FirebaseStub.prototype.off =
        FirebaseStub.prototype.name =
        FirebaseStub.prototype.key =
        FirebaseStub.prototype.authWithCustomToken =
        function() {
            return new FirebaseStub();
        };
    FirebaseStub.ServerValue = {TIMESTAMP:null};
    
    function Storage(fingerprinter, optFastTick, optScratchDir) {
        if (typeof process !== 'undefined' && process.nextTick && !optFastTick) {
            nextTick = process.nextTick;
        } else if (typeof window !== 'undefined' && optFastTick) {
            nextTick = function nextTick(cb) {cb();};
        } else if (typeof window !== 'undefined' && window.setTimeout) {
            nextTick = function nextTick(cb) {window.setTimeout(cb, 0);}
        } else {
            throw new Error("No nextTick");
        }

        var thatStorage = this;
        if (typeof localStorage === "undefined" || localStorage === null) {
            var LocalStorage = require('node-localstorage').LocalStorage;
            var localStorage = new LocalStorage(optScratchDir||'./scratch');
            this.local = {
                getItem: function(k,c) {c(localStorage.getItem(k));},
                removeItem: function(k,c) {localStorage.removeItem(k);
                                           if (c) c()},
                clear: localStorage.clear,
                setItem:  function(k,v,c) {localStorage.setItem(k,v);
                                           if (c) c()},
            };
        } else {
            // https://raw.githubusercontent.com/mozilla-b2g/gaia/master/shared/js/async_storage.js
            this.local = (function() {
                'use strict';

                var DBNAME = 'asyncStorage';
                var DBVERSION = 1;
                var STORENAME = 'keyvaluepairs';
                var db = null;

                function withDatabase(f) {
                    if (db) {
                        f();
                    } else {
                        var openreq = indexedDB.open(DBNAME, DBVERSION);
                        openreq.onerror = function withStoreOnError() {
                            console.error('asyncStorage: can\'t open database:',
                                          openreq.error.name);
                        };
                        openreq.onupgradeneeded = function withStoreOnUpgradeNeeded() {
                            // First time setup: create an empty object store
                            openreq.result.createObjectStore(STORENAME);
                        };
                        openreq.onsuccess = function withStoreOnSuccess() {
                            db = openreq.result;
                            f();
                        };
                    }
                }

                function withStore(type, callback, oncomplete) {
                    withDatabase(function() {
                        var transaction = db.transaction(STORENAME, type);
                        if (oncomplete) {
                            transaction.oncomplete = oncomplete;
                        }
                        callback(transaction.objectStore(STORENAME));
                    });
                }

                function getItem(key, callback) {
                    var req;
                    withStore('readonly', function getItemBody(store) {
                        req = store.get(key);
                        req.onerror = function getItemOnError() {
                            console.error('Error in asyncStorage.getItem(): ', req.error.name);
                        };
                    }, function onComplete() {
                        var value = req.result;
                        if (value === undefined) {
                            value = null;
                        }
                        callback(value);
                    });
                }

                function setItem(key, value, callback) {
                    withStore('readwrite', function setItemBody(store) {
                        var req = store.put(value, key);
                        req.onerror = function setItemOnError() {
                            console.error('Error in asyncStorage.setItem(): ', req.error.name);
                        };
                    }, callback);
                }

                function removeItem(key, callback) {
                    withStore('readwrite', function removeItemBody(store) {
                        var req = store.delete(key);
                        req.onerror = function removeItemOnError() {
                            console.error('Error in asyncStorage.removeItem(): ', req.error.name);
                        };
                    }, callback);
                }

                function clear(callback) {
                    withStore('readwrite', function clearBody(store) {
                        var req = store.clear();
                        req.onerror = function clearOnError() {
                            console.error('Error in asyncStorage.clear(): ', req.error.name);
                        };
                    }, callback);
                }

                var writeQueue = [];
                function onWriteComplete() {
                    var args = writeQueue.shift();
                    var callback = args[2];
                    if (callback) {callback();}
                    if (writeQueue.length > 0) {
                        var args = writeQueue[0];
                        setItem(args[0], args[1], onWriteComplete);
                    }
                }
                return {
                    getItem: getItem,
                    removeItem: removeItem,
                    clear: clear,
                    setItem: function(k,v,c) {
                        writeQueue.push([k,v,c]);
                        if (writeQueue.length == 1) {
                            setItem(k, v, onWriteComplete);
                        }
                    }
                };
            }());
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
                    "when":firebase.ServerValue.TIMESTAMP,
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
            this.local.getItem(
                key, function(str) {
                    if (!str) {
                        console.log("Key not found: " + key);
                        return;
                    }
                var obj = JSON.parse(str);
                nextTick(cb.bind(null, obj));
                });
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
        } else if (OFFLINE) {
            restGet = function(path, callback) {
                callback(eval("("+require('fs').readFileSync(
                    "../rest/" + path + '.json','utf8')+")"));
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
