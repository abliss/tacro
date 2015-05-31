({
    name:"&equals;",
    depends:["&exist;"],  
    axioms:[
        {Core:[[],[0,[1,0,1],[0,[1,0,2],[1,1,2]]],[]],
         Skin:{TermNames:["&rarr;","&equals;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,[0,[1,[2,0,[1,[3,0,1]]]],2],2],[[1,0]]],
         Skin:{TermNames:["&rarr;","&not;","&forall;","&equals;"]},
         FreeMaps:[[],[],[[]],[]]},
    ],
    goals:[
        {Core:[[],[0,0,0],[]],
         Skin:{TermNames:["&equals;"]},
         FreeMaps:[[]]},
        {Core:[[],[0,[1,0,1],[0,[1,0,2],[1,2,1]]],[]],
         Skin:{TermNames:["&rarr;","&equals;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,[1,0,1],[1,1,0]],[]],
         Skin:{TermNames:["&rarr;","&equals;"]},
         FreeMaps:[[],[]]},
        {Core:[[],[0,[1,0,1],[1,1,0]],[]],
         Skin:{TermNames:["&harr;","&equals;","&rarr;"]},
         FreeMaps:[[],[],[]]},
        {Core:[[],[0,[1,0,1],[2,[1,2,0],[1,2,1]]],[]],
         Skin:{TermNames:["&rarr;","&equals;","&harr;"]},
         FreeMaps:[[],[],[]]},
        {Core:[[],[0,[1,0,1],[2,[1,0,2],[1,1,2]]],[]],
         Skin:{TermNames:["&rarr;","&equals;","&harr;"]},
         FreeMaps:[[],[],[]]},
        {Core:[[],[0,[0,[1,0,[2,0,1]],2],2],[[1,0]]],
               Skin:{TermNames:["&rarr;","&exist;","&equals;"]},
         FreeMaps:[[],[[]],[]]},
        {Core:[[],[0,[0,[1,0,0,],1],1],[]],
               Skin:{TermNames:["&rarr;","&equals;"]},
         FreeMaps:[[],[]]},

        {"Core":[[],[0,[1,0,[1,1,[0,[2,0,1],[0,2,3]]]],[0,[1,0,2],[1,1,3]]],[[2,1],[3,0]]],"Skin":{"TermNames":["&rarr;","&forall;","&equals;","&exist;","&and;","&harr;"]},"FreeMaps":[[],[[]],[],[[]],[],[]]}
        ,
        {"Core":[[],[0,[1,0,[1,1,[0,[2,0,1],[3,2,3]]]],[3,[1,0,2],[1,1,3]]],[[2,1],[3,0]]],"Skin":{"TermNames":["&rarr;","&forall;","&equals;","&harr;","&and;"]},"FreeMaps":[[],[[]],[],[],[]]}
        ,
        {"Core":[[],[0,[1,0,[1,1,[0,[2,0,1],[3,2,3]]]],[3,[4,1,2],[4,0,3]]],[[2,0],[3,1]]],"Skin":{"TermNames":["&rarr;","&forall;","&equals;","&harr;","&exist;","&not;"]},"FreeMaps":[[],[[]],[],[],[[]],[]]}
        ,
        {"Core":[[],[0,[1,0,[1,1,[0,[2,0,1],[3,2,3]]]],[3,[4,0,2],[4,1,3]]],[[2,1],[3,0]]],"Skin":{"TermNames":["&rarr;","&forall;","&equals;","&harr;","&exist;","&not;"]},"FreeMaps":[[],[[]],[],[],[[]],[]]}

    ],
})
