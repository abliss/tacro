(function(w) {
    if (!exports.worlds) exports.worlds = {};
    exports.worlds[w.name] = w;
}({
    name:"&rarr;"
    depends:[],
    axioms:[  // Deductions only.
        // ax1
        {Bone:{Stmt:[0,"T0.0",[0,"T0.1","T0.0"]],Hyps:[],Free:[]},
         Meat:{Terms:["&rarr;"],Kinds:["wff"]}},
        // ax2
        {Bone:{Stmt:[0,[0,"T0.0",[0,"T0.1","T0.2"]],[0,[0,"T0.0","T0.1"],[0,"T0.0","T0.2"]]],Hyps:[],Free:[]},
         Meat:{Terms:["&rarr;"],Kinds:["wff"]}}        
    ],
    secrets:[  // May contain inferences. Not displayed to user.
        // ax-mp
        {Bone:{Stmt:T0.0,Hyps:["T0.1",[0,"T0.1","T0.0"]],Free:[]},
         Meat:{Terms:["&rarr;"],Kinds:["wff"]}},
        // To establish bindings on &rarr;
        // imim1
        {Bone:{Stmt:[0,[0,"T0.0","T0.1"],[0,[0,"T0.1","T0.2"],[0,"T0.0","T0.2"]]],Hyps:[],Free:[]},
         Meat:{Terms:["&rarr;"],Kinds:["wff"]}},
        // imim2
        {Bone:{Stmt:[0,[0,"T0.0","T0.1"],[0,[0,"T0.2","T0.0"],[0,"T0.2","T0.1"]]],Hyps:[],Free:[]},
         Meat:{Terms:["&rarr;"],Kinds:["wff"]}},
    ],
    buttons:[ // One-hypothesis inferences only.
    ],
    goals:[
        "() () (rarr (rarr A B) (rarr (rarr C A) (rarr C B)))" ,
        "() () (rarr (rarr A B) (rarr (rarr B C) (rarr A C)))" ,
        "() () (rarr (rarr (rarr A B) C) (rarr B C))" ,
        "() () (rarr (rarr A (rarr B C)) (rarr B (rarr A C)))" ,
        "() () (rarr (rarr A B) (rarr A A))",
        "() () (rarr A (rarr B B))",
        "() () (rarr A A)",
        "() () (rarr A (rarr (rarr A B) B))" ,
        "() () (rarr (rarr (rarr A A) B) B)" ,
        "() () (rarr (rarr A (rarr A B)) (rarr A B))",
    ]
]
});
