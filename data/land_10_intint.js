({
    name:"&int;&int;",
    depends:["&iota;"],  
    axioms:[],
    goals:[
        {Core:[[[0,[1,0,[2,1,2,[3,0,3]]],
                   [1,4,[2,1,2,[3,4,3]]]]],
                [0,[1,0,[2,1,2,[3,0,3]]],[4,1,2,3]],
               [[2,0],[3,0]]],
         Skin:{TermNames:["&harr;","&iota;","&int;","&equals;","&int;&int;"]},
         FreeMaps:[[],[[]],[[1]],[],[[1]]],
         Tree:{Cmd:"defthm",Definiendum: 4}},
        {Core:[[],[0,[1,0,0,1],1],[]],
         Skin:{Name: "sbbid1", TermNames:["&equals;", "&int;&int;"]},
         FreeMaps:[[],[[1]]]},
        {Core:[[],[0,[1,0,1,0],1],[]],
         Skin:{Name: "sbbid2", TermNames:["&equals;", "&int;&int;"]},
         FreeMaps:[[],[[1]]]},
        {Core:[[],[0,[1,0,1,2],2],[[2,0]]],
         Skin:{Name: "sbbnf", TermNames:["&equals;", "&int;&int;"]},
         FreeMaps:[[],[[1]]]},
        {Core:[[],[0,[1,0,1,[2,2,3]],[2,[3,0,1,2],[3,0,1,3]]],[]],
         Skin:{Name: "sbeqsbb", 
               TermNames:["&harr;","&int;","&equals;", "&int;&int;"]},
         FreeMaps:[[],[[1]],[],[[1]]]},
    ],
})