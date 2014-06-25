{
    name:"&exist;",
    depends:["&forall;"],  // TODO: figure out a content-addressable scheme
    goals:[
        {Core:[[],[0,[1,[2,0,[1,1]]],[3,0,1]],[]],
         Skin:{TermNames:["&harr;","&not;","&forall;","&exist;"]},
         Tree:{Cmd:"defthm",Definiendum: 3}},

        {Core:[[],[0,[1,0,1],[2,[3,0,[2,1]]]],[]],
         Skin:{TermNames:["&harr;","&exist;","&not;","&forall;","&rarr;"]}},
        {Core:[[],[0,[1,[2,0,1],[3,0,2]],[3,0,[1,1,2]]],[]],
         Skin:{TermNames:["&rarr;","&and;","&forall;","&exist;","&not;","&harr;"]}},
        {Core:[[],[0,0,[1,1,0]],[]],
         Skin:{TermNames:["&rarr;","&exist;","&not;","&forall;","&and;","&harr;"]}},
        {Core:[[],[0,[1,0,1],[2,0,1]],[]],
         Skin:{TermNames:["&rarr;","&forall;","&exist;"]}},
        {Core:[[],[0,[1,0,[0,1,2]],[0,[2,0,1],[2,0,2]]],[]],
         Skin:{TermNames:["&rarr;","&forall;","&exist;","&not;","&harr;"]}},
        {Core:[[],[0,[1,0,[2,1,2]],[2,[3,0,1],[3,0,2]]],[]],
         Skin:{TermNames:["&rarr;","&forall;","&harr;","&exist;","&not;"]}},
        {Core:[[],[0,[1,0,1],[0,[2,0,[0,1,2]],[1,0,2]]],[]],
         Skin:{TermNames:["&rarr;","&exist;","&forall;","&harr;"]}},
        {Core:[[],[0,[1,0,1],1],[[1,0]]],
         Skin:{TermNames:["&rarr;","&exist;","&not;","&forall;","&harr;"]}},
    ],
}