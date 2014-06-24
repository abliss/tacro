1);//  TODO: XXX HACK
var terms = ["&rarr;","&not;","&and;","&harr;","&or;","&forall;"];
var rarr=0, not=1, and=2, harr=3, or=4, forall=5;
var z=0, y=1, x=2, A=3, B=4, C=5, D=6, E=7;
({
    name:"&forall;",
    depends:["&or;"],  // TODO: figure out a content-addressable scheme
    axioms:[
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
        {Core:[[0],[0,1,0],[]], // generify
         Skin:{TermNames:["&forall;"]}},
    ],
    goals:[
        {Core:[[],[rarr,[forall,z,[harr,A,B]],[rarr,[forall,z,A],[forall,z,B]]],[]
              ], Skin:{TermNames:terms}},
        {Core:[[],[rarr,[forall,z,[harr,A,B]],[harr,[forall,z,A],[forall,z,B]]],[]
              ], Skin:{TermNames:terms}},
    ],
}
