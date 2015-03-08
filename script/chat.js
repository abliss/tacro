(function(module) {
    function Chat(storage, fingerprinter, pane, input) {
        var that = this;
        var workChannel = null;
        input.onkeypress = function(e) {
            e = e || window.event;
            var key = (e.keyCode || e.which);
            if (key == 13 || key == 3) {
                var msg = input.value;
                input.value = '';
                sendMsg(msg);
            }
        };
        
        function sendMsg(msg) {
            var value = {
                v: 1,
                msg: msg
            }
            if (workChannel) {
                workChannel.push(value);
            }
        }
        
        function receiveMsg(snap) {
            var box = addMsg(snap.val().msg);
            box.className += " incoming";
        }

        function addMsg(msg, className) {
            var box = document.createElement("div");
            box.className = "chatMsg";
            box.innerText = msg; // TODO: injection
            pane.appendChild(box);
            return box;
        }

        this.setWork = function(workObj) {
            if (workChannel) {
                workChannel.off("child_added",receiveMsg);
            }
            // XXX ??? storage.escape(JSON.stringify(workObj));
            var chanName = storage.escape(fingerprinter(workObj));
            workChannel = storage.remote.child("chat").child(chanName);
            workChannel.on("child_added", receiveMsg);
        };
    }
    

    module.exports = Chat;
})(module);
