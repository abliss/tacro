{
    name:"&plus;",
    depends:["&Osect;"],  // TODO: figure out a content-addressable scheme
    axioms:[
        {Core:[[],[0,[1,0,1],[0,[1,2,3],[1,[2,0,2],[2,1,3]]]],[]],
         Skin:{TermNames:["&rarr;","&equals;","&plus;"]}},
        {Core:[[],[0,[1,0,[2]],0],[]],
         Skin:{TermNames:["&equals;","&plus;","&Oslash;"]}},
        {Core:[[],[0,[1,0,[2,1]],[2,[1,0,1]]],[]],
         Skin:{TermNames:["&equals;","&plus;","&sect;"]}},
    ],
    goals:[
    ],
}
