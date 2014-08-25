### What is it?

Tacro is a browser game wherein you solve puzzles to advance, and your solutions
provide computer-verifiable formal proofs for mathematical theorems.

Tacro comprises a few different parts:

   * An _engine_ which determines the possible moves and their results;
   * Some _data_ which defines a progression of levels, each containing
     axioms and some goal theorems which must be be proved from them to advance
     to the next level;
   * An _interface_ for manipulating the engine into proving the goal theorems;
     and
   * A _schema_ for data interchange (currently hosted on a Firebase backend),
     allowing each player to publish solutions and new levels.
   
### Is it functional?

Yes, at least in Chrome.

### Is it usable?

Not yet. There are no instructions or tutorial, and the UI controls are highly
non-self-evident.

### Is it fun?

Not yet. If you can somehow figure out the UI controls, and if you enjoy formal
theorem proving for its own sake, then you might have fun. The levels have not
yet been optimized for Flow.

### Is it sound?

I think so. Modulo any bugs I'm not aware of, it should not be possible to
create unsound proofs with the Tacro engine. Currently this is only guaranteed
by the engine's JS, which is probably buggy. In the future, all generated proofs
will be double-checked offline by the Ghilbert verifier.

### Is it powerful?

Yes! The current set of levels progresses through propositional calculus,
predicate calculus, and Peano arithmetic. I have used the engine to prove
induction theorems like the associativity of addition. I believe that anything
provable from the Peano axioms could be added as a goal theorem and proved from
these levels.

### Is it general?

Yes! The engine, interface, and schema are totally separate from the particular
data set currently available. It should be possible to use Tacro to work in any
axiom system, as long as it has a two-hypothesis inference that "looks like
modus ponens", and all of its other axioms have one or zero hypotheses. (I also
believe, but am not certain, that any axiom system with more two-hypothesis
inferences besides modus ponens can be easily converted to an equipotent axiom
system compatible with these requirements.)

### Does it work offline/mobile?

Yes. Your work will be published to the server when you come back online.

### Is it social?

Not yet. But I'm planning to add a scoreboard, a P2P hint/chat system, a level
creator, and systems to publish, browse, rate, and reward new levels and new
solutions.

### Why's it called "Tacro"?

The previous version was called "Orcat" which was short for "Order Categorical".
In Orcat, you work forwards from your axioms until your theorem matches a given
goal. In Tacro, you work "backwards" from a given goal until your hypothesis
matches one of your axioms.