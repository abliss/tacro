{
    name:"&not;",
    depends:["&rarr;"],  // TODO: figure out a content-addressable scheme
    axioms:[
        // ax3
        {Bone:{Stmt:[0,[0,[1,"T0.0"],[1,"T0.1"]],[0,"T0.1","T0.0"]]},
         Meat:{Terms:["&rarr;","&not;"],Kinds:["wff"]}},
    ],
    goals:[
        {Bone:{Stmt:[0,[1,"T0.0"],[0,"T0.0","T0.1"]]},
         Meat:{Terms:["&rarr;","&not;"],Kinds:["wff"]}},
        {Bone:{Stmt:[0,[1,[1,"T0.0"]],"T0.0"]},
         Meat:{Terms:["&rarr;","&not;"],Kinds:["wff"]}},
        {Bone:{Stmt:[0,"T0.0",[1,[1,"T0.0"]]]},
         Meat:{Terms:["&rarr;","&not;"],Kinds:["wff"]}},
        {Bone:{Stmt:[0,[0,"T0.0", "T0.1"],[0,[1,"T0.1"],[1,"T0.0"]]]},
         Meat:{Terms:["&rarr;","&not;"],Kinds:["wff"]}},
        {Bone:{Stmt:[0,[1,[0,"T0.0", "T0.1"],[1,"T0.1"]]]},
         Meat:{Terms:["&rarr;","&not;"],Kinds:["wff"]}},
        {Bone:{Stmt:[0,[1,[0,"T0.0", "T0.1"],"T0.0"]]},
         Meat:{Terms:["&rarr;","&not;"],Kinds:["wff"]}},
        {Bone:{Stmt:[0,"T0.0",[0,[1,"T0.1"],[1,[0,"T0.0", "T0.1"]]]]},
         Meat:{Terms:["&rarr;","&not;"],Kinds:["wff"]}},
        {Bone:{Stmt:[0,[0,[1,"T0.0"],"T0.0"],"T0.0"]},
         Meat:{Terms:["&rarr;","&not;"],Kinds:["wff"]}},
        {Bone:{Stmt:[0,[1,[1,"T0.0","T0.0"],[0,[1,"T0.1", "T0.1"]]]]},
         Meat:{Terms:["&not;","&rarr;"],Kinds:["wff"]}},
    ],
}
