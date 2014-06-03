{
    name:"&rarr;",
    depends:[],
    axioms:[// 0-hyp theorems only.
        // NB: instead of the usual Simp+Frege basis for positive propositional
        // calculus, we use one of Hilbert's because it provides the necessary
        // "binding theorems" for rarr over itself.
        // ax1
        {Bone:{Stmt:[0,"T0.0",[0,"T0.1","T0.0"]]},
         Meat:{Terms:["&rarr;"],Kinds:["wff"]}},
        // imim1
        {Bone:{Stmt:[0,[0,"T0.0","T0.1"],[0,[0,"T0.1","T0.2"],[0,"T0.0","T0.2"]]]},
         Meat:{Terms:["&rarr;"],Kinds:["wff"]}},
        // imim2
        {Bone:{Stmt:[0,[0,"T0.0","T0.1"],[0,[0,"T0.2","T0.0"],[0,"T0.2","T0.1"]]]},
         Meat:{Terms:["&rarr;"],Kinds:["wff"]}},
        // pm2.43
        {Bone:{Stmt:[0,[0,"T0.0",[0, "T0.0", "T0.1"]],[0,"T0.0","T0.1"]]},
         Meat:{Terms:["&rarr;"],Kinds:["wff"]}},
    ],
    inferences:[  // Not displayed in the user's toolbox.
        // ax-mp
        {Bone:{Stmt:"T0.0",Hyps:["T0.1",[0,"T0.1","T0.0"]],Free:[]},
         Meat:{Terms:["&rarr;"],Kinds:["wff"]}},
    ],
    goals:[
        // ax2
        {Bone:{Stmt:[0,[0,"T0.0",[0,"T0.1","T0.2"]],[0,[0,"T0.0","T0.1"],[0,"T0.0","T0.2"]]]},
         Meat:{Terms:["&rarr;"],Kinds:["wff"]}},
        {Bone:{Stmt:[0,[0,[0,"T0.0","T0.1"],"T0.2"],[0,"T0.1","T0.2"]]},
         Meat:{Terms:["&rarr;"],Kinds:["wff"]}},
        {Bone:{Stmt:[0,[0,"T0.0",[0,"T0.1","T0.2"]],[0,"T0.1",[0,"T0.0","T0.2"]]]},
         Meat:{Terms:["&rarr;"],Kinds:["wff"]}},
        {Bone:{Stmt:[0,[0,"T0.0","T0.1"],[0,"T0.0","T0.0"]]},
         Meat:{Terms:["&rarr;"],Kinds:["wff"]}},
        {Bone:{Stmt:[0,"T0.0",[0,"T0.1","T0.1"]]},
         Meat:{Terms:["&rarr;"],Kinds:["wff"]}},
        {Bone:{Stmt:[0,"T0.0","T0.0"]},
         Meat:{Terms:["&rarr;"],Kinds:["wff"]}},
        {Bone:{Stmt:[0,"T0.0",[0,"T0.1",[0,[0,"T0.1","T0.2"],"T0.2"]]]},
         Meat:{Terms:["&rarr;"],Kinds:["wff"]}},
        {Bone:{Stmt:[0,"T0.0",[0,[0,"T0.0","T0.1"],"T0.1"]]},
         Meat:{Terms:["&rarr;"],Kinds:["wff"]}},
        {Bone:{Stmt:[0,[0,[0,"T0.0","T0.0"],"T0.1"],"T0.1"]},
         Meat:{Terms:["&rarr;"],Kinds:["wff"]}},
    ],
}
