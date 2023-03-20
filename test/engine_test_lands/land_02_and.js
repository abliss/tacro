({
    name:"&and;",
    depends:["&not;"],  
    goals:[
        // Future definitions using the biconditional can be automatic, but this
        // definition must be manual. In addition, to keep id as the "universal
        // first step", we add a layer of indirection so that the root of the
        // expression is ->.
        {Core:[[[0,
                   [0,
                    [1,[0,
                      [0,
                       [1,[0,0,[1,1]]],[1,[0,0,[1,1]]]],
                      [1,[0,   [1,[0,0,[1,1]]],
                       [1,[0,0,[1,1]]]]]]],
                    2],
                   2]],
               [0,
                [0,
                 [1,[0,
                     [0,
                      [2,0,1],[1,[0,0,[1,1]]]],
                     [1,[0,   [1,[0,0,[1,1]]],
                         [2,0,1]]]]],
                 2],
                2],[]],
         Skin:{TermNames:["&rarr;","&not;","&and;"]},
         FreeMaps:[[],[],[]],
         Tree:{Cmd:"defthm",Definiendum: 2,
               Proof: ["Hyps.0"]}
        },
        {Core:[[],[0,[1,0,1],[2,[0,0,[2,1]]]],[]],
         Skin:{TermNames:["&rarr;","&and;","&not;"]},
         FreeMaps:[[],[],[]]},
        {Core:[[],[0,[1,[0,0,[1,1]]],[2,0,1]],[]],
         Skin:{TermNames:["&rarr;","&not;","&and;"]},
         FreeMaps:[[],[],[]]},
        {Core:[[],[0,[0,0,1],[0,[1,0,2],[1,1,2]]],[]],
         Skin:{TermNames:["&rarr;","&and;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,[0,0,1],[0,[1,2,0],[1,2,1]]],[]],
         Skin:{TermNames:["&rarr;","&and;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,[1,0,1],0],[]],
         Skin:{TermNames:["&rarr;","&and;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,[1,0,1],1],[]],
         Skin:{TermNames:["&rarr;","&and;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,0,[0,1,[1,0,1]]],[]],
         Skin:{TermNames:["&rarr;","&and;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,0,[1,0,0]],[]],
         Skin:{TermNames:["&rarr;","&and;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,0,[1,[0,1,1],0]],[]],
         Skin:{TermNames:["&rarr;","&and;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,[1,0,1],[1,1,0]],[]],
         Skin:{TermNames:["&rarr;","&and;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,[0,0,1],[0,0,[1,0,1]]],[]],
         Skin:{TermNames:["&rarr;","&and;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,[0,0,[0,1,2]],[0,[1,0,1],2]],[]],
         Skin:{TermNames:["&rarr;","&and;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,[1,0,[0,0,1]],1],[]],
         Skin:{TermNames:["&rarr;","&and;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,[1,0,[0,1,2]],[0,1,[1,0,2]]],[]],
         Skin:{TermNames:["&rarr;","&and;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,[1,[0,0,1],[0,2,3]],[0,[1,0,2],[1,1,3]]],[]],
         Skin:{TermNames:["&rarr;","&and;"]},
         FreeMaps:[[],[]]},
],
})