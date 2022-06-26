({
    name:"&int;",
    depends:["&equals;"],  
    axioms:[
        // A literal translation of ax-12, but problematic because both vars are binding.
        // {Core:[[],[0,[1,0,1],[0,[2,1,2],[2,0,[0,[1,0,1],2]]]],[]],
        //  Skin:{TermNames:["&rarr;","&equals;","&forall;"]},
        //  FreeMaps:[[],[],[[]]]},
        // A hopefully weaker version, experimental!
        {Core:[[],[0,[1,0,1],[0,2,[2,0,[0,[1,0,1],2]]]],[[1,0]]],
         Skin:{TermNames:["&rarr;","&equals;","&forall;"]},
         FreeMaps:[[],[],[[]]]},

    ],
    goals:[
        {Core:[[[0,[1,0,[2,[3,0,1],[1,2,[2,[3,2,0],3]]]],
                   [1,4,[2,[3,4,1],[1,2,[2,[3,2,4],3]]]]]],
                [0,[1,0,[2,[3,0,1],[1,2,[2,[3,2,0],3]]]],[4,2,1,3]],[[1,0],[3,0]]],
         Skin:{TermNames:["&harr;","&exist;","&and;","&equals;","&int;"]},
         FreeMaps:[[],[[]],[],[],[[1]]],
         Tree:{Cmd:"defthm",Definiendum: 4}},
        {Core:[[],[0,[1,0,[2,[3,0,1],2]],[4,0,[5,[3,0,1],2]]],[[1,0]]],
         Skin:{Name: "df-subst", TermNames:["&harr;","&exist;", "&and;", "&equals;", "&forall;","&rarr;"]},
         FreeMaps:[             [],     [[]],      [],         [],       [[]],      []]},

        {Core:[[],[0,[1,0,1],[2,0,2,1]],[]],
         Skin:{Name: "asb",TermNames:["&rarr;", "&forall;", "&int;"]},
         FreeMaps:[[],[[]],[[1]]]},

        {Core:[[],[0,[1,0,1,[2,2,3]],[2,[1,0,1,2],[1,0,1,3]]],[]],
         Skin:{Name: "sbim", TermNames:["&harr;", "&int;", "&rarr;"]},
         FreeMaps:[[],[[1]],[]]},
        {Core:[[],[0,[1,0,[0,1,2]],[0,[2,0,3,1],[2,0,3,2]]],[]],
         Skin:{Name: "imsb3", TermNames:["&rarr;", "&forall;", "&int;"]},
         FreeMaps:[[],[[]],[[1]]]},
      
        {Core:[[],[0,[1,0,1,[2,2]],[2,[1,0,1,2]]],[]],
         Skin:{Name: "sbn",TermNames:["&harr;", "&int;", "&not;"]},
         FreeMaps:[[],[[1]],[]]},
        {Core:[[],[0,[1,0,1,[2,2,3]],[2,[1,0,1,2],[1,0,1,3]]],[]],
         Skin:{Name:"sban", TermNames:["&harr;", "&int;", "&and;"]},
         FreeMaps:[[],[[1]],[]]},
        {Core:[[],[0,[1,0,1,[0,2,3]],[0,[1,0,1,2],[1,0,1,3]]],[]],
         Skin:{Name:"sbbi", TermNames:["&harr;", "&int;"]},
         FreeMaps:[[],[[1]]]},
        {Core:[[],[0,[1,0,[2,1,2]],[2,[3,0,3,1],[3,0,3,2]]],[]],
         Skin:{Name: "bisb3", TermNames:["&rarr;", "&forall;","&harr;", "&int;"]},
         FreeMaps:[[],[[]],[],[[1]]]},
        
        {Core:[[],[0,[1,0,1,[2,2,3]],[2,[1,0,1,2],[1,0,1,3]]],[]],
         Skin:{Name:"sbor", TermNames:["&harr;", "&int;", "&or;"]},
         FreeMaps:[[],[[1]],[]]},
        {Core:[[],[0,[1,0,1,[2,2,3]],[2,2,[1,0,1,3]]],[
            [1,2] // TODO doesn't seem like this freelist should be needed!
        ]],
         Skin:{Name:"sbal", TermNames:["&harr;", "&int;", "&forall;"]},
         FreeMaps:[[],[[1]],[[]]]},
        {Core:[[],[0,[1,0,1,[2,2,3]],[2,2,[1,0,1,3]]],[
                        [1,2] // TODO doesn't seem like this freelist should be needed!
        ]],
         Skin:{Name:"sbex", TermNames:["&harr;", "&int;", "&exist;"]},
         FreeMaps:[[],[[1]],[[]]]},
        
        {Core:[[],[0,[1,0,0,1],1],[]],
         Skin:{Name: "sbid", TermNames:["&harr;", "&int;"]},
         FreeMaps:[[],[[1]]]},
        {Core:[[],[0,[1,0,1],[1,2,[2,0,2,1]]],[[1,2]]],
         Skin:{Name: "sbalpha", TermNames:["&harr;", "&forall;", "&int;"]},
         FreeMaps:[[],[[]],[[1]]]},
        {Core:[[],[0,[1,0,1],[2,0,2,1]],[]],
         Skin:{Name: "axsb", TermNames:["&rarr;", "&forall;", "&int;"]},
         FreeMaps:[[],[[]],[[1]]]},
    ],
})
