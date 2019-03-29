({
    name:"&int;",
    depends:["&equals;"],  
    axioms:[
        {Core:[[],[0,[1,0,1],[0,[2,1,2],[2,0,[0,[1,0,1],2]]]],[]],
         Skin:{TermNames:["&rarr;","&equals;","&forall;"]},
         FreeMaps:[[],[],[[]]]},
    ],
    goals:[
        {Core:[[[0,[1,0,[2,[3,0,1],[1,2,[2,[3,2,0],3]]]],
                   [1,0,[2,[3,4,1],[1,2,[2,[3,2,4],3]]]]]],
                [0,[1,0,[2,[3,0,1],[1,2,[2,[3,2,0],3]]]],[4,2,1,3]],[[1,0],[3,0]]],
         Skin:{TermNames:["&harr;","&exist;","&and;","&equals;","&int;"]},
         FreeMaps:[[],[[]],[],[],[[1]]],
         Tree:{Cmd:"defthm",Definiendum: 4}},
        {Core:[[],[0,[1,0,1,[2,3]],[2,[1,0,1,3]]],[]],
         Skin:{TermNames:["&harr;", "&int;", "&not;"]},
         FreeMaps:[[],[[1]],[]]},
        {Core:[[],[0,[1,0,1,[2,3,4]],[2,[1,0,1,3],[1,0,1,4]]],[]],
         Skin:{TermNames:["&harr;", "&int;", "&rarr;"]},
         FreeMaps:[[],[[1]],[]]},
        {Core:[[],[0,[1,0,1,[2,3,4]],[2,[1,0,1,3],[1,0,1,4]]],[]],
         Skin:{TermNames:["&harr;", "&int;", "&rarr;"]},
         FreeMaps:[[],[[1]],[]]},
        {Core:[[],[0,[1,0,1,[2,3,4]],[2,[1,0,1,3],[1,0,1,4]]],[]],
         Skin:{TermNames:["&harr;", "&int;", "&and;"]},
         FreeMaps:[[],[[1]],[]]},
        {Core:[[],[0,[1,0,1,[0,3,4]],[0,[1,0,1,3],[1,0,1,4]]],[]],
         Skin:{TermNames:["&harr;", "&int;"]},
         FreeMaps:[[],[[1]]]},
        {Core:[[],[0,[1,0,0,1],1],[]],
         Skin:{TermNames:["&harr;", "&int;"]},
         FreeMaps:[[],[[1]]]},
        {Core:[[],[0,[1,0,1],[1,2,[2,0,2,1]]],[[1,2]]],
         Skin:{TermNames:["&harr;", "&forall;", "&int;"]},
         FreeMaps:[[],[[]],[[1]]]},
    ],
})
