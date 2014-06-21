{
    name:"&not;",
    depends:["&rarr;"],  // TODO: figure out a content-addressable scheme
    axioms:[
        // ax3
        {Core:[[],[0,[0,[1,0],[1,1]],[0,1,0]],[]],
         Skin:{TermNames:["&rarr;","&not;"]}},
    ],
    goals:[
        {Core:[[],[0,[1,0],[0,0,1]],[]],
         Skin:{TermNames:["&rarr;","&not;"]}},
        {Core:[[],[0,[1,[1,0]],0],[]],
         Skin:{TermNames:["&rarr;","&not;"]}},
        {Core:[[],[0,0,[1,[1,0]]],[]],
         Skin:{TermNames:["&rarr;","&not;"]}},
        {Core:[[],[0,[0,0,1],[0,[1,1],[1,0]]],[]],
         Skin:{TermNames:["&rarr;","&not;"]}},
        {Core:[[],[0,[1,[0,0,1]],[1,1]],[]],
         Skin:{TermNames:["&rarr;","&not;"]}},
        {Core:[[],[0,[1,[0,0,1]],0],[]],
         Skin:{TermNames:["&rarr;","&not;"]}},
        {Core:[[],[0,0,[0,[1,1],[1,[0,0,1]]]],[]],
         Skin:{TermNames:["&rarr;","&not;"]}},
        {Core:[[],[0,[0,[1,0],0],0],[]],
         Skin:{TermNames:["&rarr;","&not;"]}},
        {Core:[[],[0,[1,[1,0,0],[0,[1,1,1]]]],[]],
         Skin:{TermNames:["&not;","&rarr;"]}},
        // Future definitions using the biconditional can be automatic, but
        // this definition *of* the biconditional must be manual.
        {Core:[[],[0,[1,
                      [1,
                       [2,0,1],[0,[1,[1,0,1],[0,[1,1,0]]]]],
                      [0,[1,   [0,[1,[1,0,1],[0,[1,1,0]]]],
                       [2,0,1]]
                      ]]],[]],
         Skin:{TermNames:["&not;","&rarr;","&harr;"]},
         Tree:{Cmd:"defthm",Definiendum: 2}
        },
    ],
}
