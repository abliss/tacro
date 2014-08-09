({
    name:"&forall;",
    depends:["&or;"],  
    axioms:[
        {Core:[[0],[0,1,0],[]], // generify
         Skin:{TermNames:["&forall;"]}},
        {Core:[[],[0,[1,0,1],1],[]],
         Skin:{TermNames:["&rarr;","&forall;"]}},
        {Core:[[],[0,[1,0,[0,1,2]],[0,[1,0,1],[1,0,2]]],[]],
         Skin:{TermNames:["&rarr;","&forall;"]}},
        {Core:[[],[0,[1,0,[1,1,2]],[1,1,[1,0,2]]],[]],
         Skin:{TermNames:["&rarr;","&forall;"]}},
        {Core:[[],[0,[1,[2,0,1]],[2,0,[1,[2,0,1]]]],[]],
         Skin:{TermNames:["&rarr;","&not;","&forall;"]}},
        {Core:[[],[0,0,[1,1,0]],[[0,1]]],
         Skin:{TermNames:["&rarr;","&forall;"]}},
    ],
    goals:[
        {Core:[[],[0,[1,0,[2,1,2]],[0,[1,0,1],[1,0,2]]],[]],
         Skin:{TermNames:["&rarr;","&forall;","&harr;"]}},
        {Core:[[],[0,[1,0,[2,1,2]],[2,[1,0,1],[1,0,2]]],[]],
         Skin:{TermNames:["&rarr;","&forall;","&harr;","&and;"]}},
        {Core:[[],[0,[1,0,[2,1,2]],[1,0,1]],[]],
         Skin:{TermNames:["&rarr;","&forall;","&and;"]}},
        {Core:[[],[0,[1,0,[2,1,2]],[2,[1,0,1],[1,0,2]]],[]],
         Skin:{TermNames:["&rarr;","&forall;","&and;"]}},
        {Core:[[],[0,[1,0,[2,1,2]],[2,[1,0,1],[1,0,2]]],[]],
         Skin:{TermNames:["&harr;","&forall;","&and;","&rarr;"]}},
        {Core:[[],[0,[1,0,[1,1,2]],[1,1,[1,0,2]]],[]],
         Skin:{TermNames:["&harr;","&forall;","&rarr;","&and;"]}},
        {Core:[[],[0,[0,0,1],[0,[1,1],[1,0]]],[]],
         Skin:{TermNames:["&harr;","&not;","&rarr;","&and;"]}},
        {Core:[[],[0,[1,0,[2,1,2]],[2,[1,0,[3,2]],[1,0,[3,1]]]],[]],
         Skin:{TermNames:["&rarr;","&forall;","&harr;","&not;"]}},
        {Core:[[],[0,[0,[1,0,[0,1,1]],2],2],[]],
         Skin:{TermNames:["&rarr;","&forall;"]}},
    ],
})
