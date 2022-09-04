(function(module) {
    function Chat(storage, fingerprinter, pane, input, filter, Fact) {
        var that = this;
        var workChannel = null;
        var history = [];
        var boxMap = {};
        input.onkeypress = function(e) {
            e = e || window.event;
            var key = (e.keyCode || e.which);
            if (key == 13 || key == 3) {
                var msg = input.value;
                input.value = '';
                sendMsg(msg);
            } else if (key == 38) { // up
                input.value = history.pop();
            }
        };
        
        function sendMsg(msg) {
            history.push(msg);
            if (filter && !filter(msg)) {
                return;
            }
            var value = {
                v: 1,
                msg: msg
            }
            if (workChannel) {
                workChannel.push(value);
            }
        }
        
        function removeMsg(snap) {
            var box = boxMap[snap.name()];
            if (box) {
                pane.removeChild(box);
            }
        }
        
        function receiveMsg(snap) {
            var box = pane.appendChild(document.createElement("div"));
            box.className = "chatMsg";
            box.innerText = snap.val().msg; // TODO: injection
            boxMap[snap.name()] = box;
            var close = box.appendChild(document.createElement("button"));
            close.innerText = "X";
            close.className = "close";
            close.onclick = function(){
                snap.ref().remove();
            };
            return box;
        }

        this.setWork = function(workObj) {
            while (pane.lastChild) {
                pane.removeChild(pane.lastChild);
            }
            boxMap = {};
            if (workChannel) {
                workChannel.off("child_added",receiveMsg);
                workChannel.off("child_removed",removeMsg);
            }
            // XXX ??? storage.escape(JSON.stringify(workObj));
            var chanName = storage.escape(fingerprinter(workObj.Core[Fact.CORE_HYPS][0]));
            workChannel = storage.remote.child("chat").child(chanName);
            workChannel.on("child_added", receiveMsg);
            workChannel.on("child_removed",removeMsg);
        };
    }
    

    module.exports = Chat;
})(module);
