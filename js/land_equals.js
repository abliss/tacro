({
    name:"&equals;",
    depends:["&exist;"],  
    axioms:[
        {Core:[[],[0,[1,0,1],[0,[1,0,2],[1,1,2]]],[]],
         Skin:{TermNames:["&rarr;","&equals;"]}},
        {Core:[[],[0,[1,0,[0,[2,0,1]]]],[[1,0]]],
         Skin:{TermNames:["&not;","&forall;","&equals;"]}},
    ],
    goals:[
        {Core:[[],[0,0,[1,0,1]],[[1,0]]],
         Skin:{TermNames:["&exist;","&equals;"]}},

        {Core:[[],[0,0,0],[]],
         Skin:{TermNames:["&equals;"]}},
        {Core:[[],[0,[1,0,1],[0,[1,0,2],[1,2,1]]],[]],Skin:{TermNames:["&rarr;","&equals;"]}},
        {Core:[[],[0,[1,0,1],[1,1,0]],[]],Skin:{TermNames:["&rarr;","&equals;"]}},
        {Core:[[],[0,[1,0,1],[1,1,0]],[]],Skin:{TermNames:["&harr;","&equals;","&rarr;"]}},
        {Core:[[],[0,[0,[1,0,[2,0,1]],2],2],[[1,0]]],
               Skin:{TermNames:["&rarr;","&exist;","&equals;"]}},
        {Core:[[],[0,[0,[1,0,0,],1],1],[]],
               Skin:{TermNames:["&rarr;","&equals;"]}},

    ],
})
