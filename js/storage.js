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



    module.exports = Storage;
})(module);
