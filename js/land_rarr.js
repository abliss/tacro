{
    name:"&rarr;",
    depends:[],
    axioms:[// 0-hyp theorems only.
        // NB: instead of the usual Simp+Frege basis for positive propositional
        // calculus,we use one of Hilbert's because it provides the necessary
        // "binding theorems" for rarr over itself.
        // ax1
        {Core:[[],[0,0,[0,1,0]],[]],
         Skin:{TermNames:["&rarr;"]}},
        // imim1
        {Core:[[],[0,[0,0,1],[0,[0,1,2],[0,0,2]]],[]],
         Skin:{TermNames:["&rarr;"]}},
        // imim2
        {Core:[[],[0,[0,0,1],[0,[0,2,0],[0,2,1]]],[]],
         Skin:{TermNames:["&rarr;"]}},
        // pm2.43
        {Core:[[],[0,[0,0,[0,0,1]],[0,0,1]],[]],
         Skin:{TermNames:["&rarr;"]}},
    ],
    inferences:[  // Not displayed in the user's toolbox.
        // ax-mp
        {Core:[[1,[0,1,0]],0,[]],
         Skin:{TermNames:["&rarr;"]}},
    ],
    goals:[
        // ax2
        {Core:[[],[0,[0,0,[0,1,2]],[0,[0,0,1],[0,0,2]]],[]],
         Skin:{TermNames:["&rarr;"]}},
        {Core:[[],[0,[0,[0,0,1],2],[0,1,2]],[]],
         Skin:{TermNames:["&rarr;"]}},
        {Core:[[],[0,[0,0,[0,1,2]],[0,1,[0,0,2]]],[]],
         Skin:{TermNames:["&rarr;"]}},
        {Core:[[],[0,[0,0,1],[0,0,0]],[]],
         Skin:{TermNames:["&rarr;"]}},
        {Core:[[],[0,0,[0,1,1]],[]],
         Skin:{TermNames:["&rarr;"]}},
        {Core:[[],[0,0,0],[]],
         Skin:{TermNames:["&rarr;"]}},
        {Core:[[],[0,0,[0,1,[0,[0,1,2],2]]],[]],
         Skin:{TermNames:["&rarr;"]}},
        {Core:[[],[0,0,[0,[0,0,1],1]],[]],
         Skin:{TermNames:["&rarr;"]}},
        {Core:[[],[0,[0,[0,0,0],1],1],[]],
         Skin:{TermNames:["&rarr;"]}},
    ],
}
