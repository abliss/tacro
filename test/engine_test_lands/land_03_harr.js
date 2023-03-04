({
    name:"&harr;",
    depends:["&and;"],  
    goals:[
        // More indirection to keep -> at the root
        {Core:[[[0,[0,
                   [1,[0,[1,[0,0,1],[0,1,0]],
                       [1,[0,0,1],[0,1,0]]],
                    [0,[1,[0,0,1],[0,1,0]],
                     [1,[0,0,1],[0,1,0]]]],
                   2],2]],
               [0,[0,
                   [1,[0,[2,0,1],[1,[0,0,1],[0,1,0]]],
                    [0,[1,[0,0,1],[0,1,0]],[2,0,1]]],
                   2],2],[]],
         Skin:{TermNames:["&rarr;","&and;","&harr;"]},
         FreeMaps:[[],[],[]],
         Tree:{Cmd:"defthm",Definiendum: 2,
               Proof: ["Hyps.0"]}},
        {Core:[[],[0,[1,0,1],[2,[0,0,1],[0,1,0]]],[]],
         Skin:{TermNames:["&rarr;","&harr;","&and;"]},
         FreeMaps:[[],[],[]],
        },
        {Core:[[],[0,[1,[0,0,1],[0,1,0]],[2,0,1]],[]],
         Skin:{TermNames:["&rarr;","&and;","&harr;"]},
         FreeMaps:[[],[],[]]},
        {Core:[[],[0,[1,0,1],[0,0,1]],[]],
         Skin:{TermNames:["&rarr;","&harr;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,[1,0,1],[0,1,0]],[]],
         Skin:{TermNames:["&rarr;","&harr;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,[1,0,1],[1,[0,1,2],[0,0,2]]],[]],
         Skin:{TermNames:["&rarr;","&harr;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,[1,0,1],[1,[0,2,0],[0,2,1]]],[]],
         Skin:{TermNames:["&rarr;","&harr;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,[1,0,1],[1,[1,0,2],[1,1,2]]],[]],
         Skin:{TermNames:["&rarr;","&harr;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,[1,0,1],[1,[1,2,0],[1,2,1]]],[]],
         Skin:{TermNames:["&rarr;","&harr;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,0,[0,[1,0,1],1]],[]],
         Skin:{TermNames:["&rarr;","&harr;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,0,[0,[1,1,0],1]],[]],
         Skin:{TermNames:["&rarr;","&harr;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,0,0],[]],
         Skin:{TermNames:["&harr;"]},
         FreeMaps:[[]]},
        {Core:[[],[0,0,[1,[0,1,1],0]],[]],
         Skin:{TermNames:["&harr;","&and;"]},
         FreeMaps:[[],[]]},

        {Core:[[],[0,[0,0,[1,1,2]],[1,[0,0,1],[0,0,2]]],[]],
         Skin:{TermNames:["&rarr;","&harr;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,[1,0,1],[1,[2,1],[2,0]]],[]],
         Skin:{TermNames:["&rarr;","&harr;","&not;"]},
         FreeMaps:[[],[],[]]}, 

        {Core:[[],[0,[1,0,1],[1,[2,0,2],[2,1,2]]],[]],
         Skin:{TermNames:["&rarr;","&harr;","&and;"]},
         FreeMaps:[[],[],[]]},
        {Core:[[],[0,[1,0,1],[1,[2,2,0],[2,2,1]]],[]],
         Skin:{TermNames:["&rarr;","&harr;","&and;"]},
         FreeMaps:[[],[],[]]},
       {Core:[[],[0,[0,0,1],[0,1,0]],[]],
         Skin:{TermNames:["&harr;"]},
         FreeMaps:[[]]},
        {Core:[[],[0,0,[1,[1,0]]],[]],
         Skin:{TermNames:["&harr;","&not;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,[1,0,1],[1,[2,1],[2,0]]],[]],
         Skin:{TermNames:["&harr;","&rarr;","&not;"]},
         FreeMaps:[[],[],[]]},
        {Core:[[],[0,[1,0,1],[2,[3,0,[2,1]]]],[]],
         Skin:{TermNames:["&harr;","&and;","&not;","&rarr;"]},
         FreeMaps:[[],[],[],[]]},
        {Core:[[],[0,[1,0,1],[1,1,0]],[]],
         Skin:{TermNames:["&harr;","&and;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,0,[1,0,0]],[]],
         Skin:{TermNames:["&harr;","&and;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,[1,0,[1,1,2]],[1,1,[1,0,2]]],[]],
         Skin:{TermNames:["&harr;","&rarr;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,[1,[1,0,1],2],[1,0,[1,1,2]]],[]],
         Skin:{TermNames:["&harr;","&and;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,[1,0,[1,1,2]],[1,[2,0,1],2]],[]],
         Skin:{TermNames:["&harr;","&rarr;","&and;"]},
         FreeMaps:[[],[],[]]},
        {Core:[[],[0,[0,0,1],[1,[2,0,1],[2,1,0]]],[]],
         Skin:{TermNames:["&harr;","&and;","&rarr;"]},
         FreeMaps:[[],[],[]]},
        {Core:[[],[0,[1,0,1],[1,[1,2,0],[1,1,2]]],[]],
         Skin:{TermNames:["&rarr;","&harr;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,[0,0,1],[0,[0,1,0],[1,0,1]]],[]],
         Skin:{TermNames:["&rarr;","&harr;","&and;"]},
         FreeMaps:[[],[],[]]},
        {Core:[[],[0,[1,[2,0,1],[2,0,2]],[2,0,[1,1,2]]],[]],
         Skin:{TermNames:["&harr;","&and;","&rarr;"]},
         FreeMaps:[[],[],[]]},
        {Core:[[],[0,[1,[2,0,1],[2,0,2]],[2,1,2]],[]],
         Skin:{"TermNames":["&rarr;","&and;","&harr;"]},
         FreeMaps:[[],[],[],[]]},
        {Core:[[],[0,[0,0,1],[0,[1,1],[1,0]]],[]],
         Skin:{TermNames:["&harr;","&not;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,0,[1,1,[2,0,1]]],[]],
         Skin:{"TermNames":["&rarr;","&harr;","&and;"]},
         FreeMaps:[[],[],[]]},
        {Core:[[],[0,[1,0,[2,1,2]],[2,[1,0,1],[1,0,2]]],[]],
         Skin:{"TermNames":["&rarr;","&and;","&harr;"]},
         FreeMaps:[[],[],[]]},
        {Core:[[],[0,[1,[2,0,1],2],[2,[1,0,2],[1,1,2]]],[]],
         Skin:{"TermNames":["&rarr;","&and;","&harr;"]},
         FreeMaps:[[],[],[]]},
        {Core:[[],[0,[0,0,[1,1,2]],[1,[2,0,1],[2,0,2]]],[]],
         Skin:{"TermNames":["&rarr;","&harr;","&and;"]},
         FreeMaps:[[],[],[]]},
    ],
})
