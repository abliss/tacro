({
    name:"&le;",
    depends:["&plus;"],  
    axioms:[
    ],
    goals:[
        {"Core":[[[0,
                   [1,0,[2,[3,1,0],2]],
                   [1,3,[2,[3,1,3],2]]]],
                 [0,[1,0,[2,[3,1,0],2]],[4,1,2]],
                 [[1, 0],[2, 0] ]],
         "Skin":{"Name":"df-le2","TermNames":["&harr;","&exist;","&equals;","&plus;","&le;"]},
         "FreeMaps":[[],[[]],[],[],[]],
         Tree:{Cmd:"defthm",Definiendum: 4}
        },
        /*
        {"Core":[[[0,[2,3,[3,[4,0,3],1]],
                     [2,2,[3,[4,0,2],1]]]],
                 [0,[1,0,1],
                     [2,2,[3,[4,0,2],1]]],
                 []],
         "Skin":{"TermNames":["&harr;","&le;","&exist;","&equals;","&plus;"]},
         "FreeMaps":[[],[],[[]],[],[]],
         Tree:{Cmd:"defthm",Definiendum: 1}},
        */
        {"Core":[[],[0,0,[1,0,1]],[]],"Skin":{"TermNames":["&le;","&plus;"]},"FreeMaps":[[],[]]},
        {"Core":[[],[0,[1],0],[]],"Skin":{"TermNames":["&le;","&Oslash;"]},"FreeMaps":[[],[]]},
        {"Core":[[],[0,0,0],[]],"Skin":{"TermNames":["&le;"]},"FreeMaps":[[]]},
        {"Core":[[],[0,0,[1,1,1]],[]],"Skin":{"TermNames":["&rarr;","&le;"]},"FreeMaps":[[],[]]},
        {"Core":[[],[0,[1,0,1],[2,[3,0,2],[3,1,2]]],[]],"Skin":{"TermNames":["&rarr;","&equals;","&harr;","&le;"]},"FreeMaps":[[],[],[],[]]},
        {"Core":[[],[0,[1,0,1],[2,[3,2,0],[3,2,1]]],[]],"Skin":{"TermNames":["&rarr;","&equals;","&harr;","&le;"]},"FreeMaps":[[],[],[],[]]},
        {"Core":[[],[0,[1,0,1],[0,[1,1,2],[1,0,2]]],[]],"Skin":{"TermNames":["&rarr;","&le;"]},"FreeMaps":[[],[]]},
        {"Core":[[],[0,[1,0,1],[0,[1,2,0],[1,2,1]]],[]],"Skin":{"TermNames":["&rarr;","&le;"]},"FreeMaps":[[],[]]},
        {"Core":[[],[0,[1,0,1],[1,[2,0,2],[2,1,2]]],[]],"Skin":{"TermNames":["&harr;","&le;","&plus;"]},"FreeMaps":[[],[],[]]},
        {"Core":[[],[0,[1,0,1],[1,[2,2,0],[2,2,1]]],[]],"Skin":{"TermNames":["&harr;","&le;","&plus;"]},"FreeMaps":[[],[],[]]},
        {"Core":[[],[0,[1,0,1],[1,[2,0],[2,1]]],[]],"Skin":{"TermNames":["&harr;","&le;","&sect;"]},"FreeMaps":[[],[],[]]},
        {"Core":[[],[0,[1,[2,0,1]],[2,[3,1],0]],[]],"Skin":{"TermNames":["&rarr;","&not;","&le;","&sect;"]},"FreeMaps":[[],[],[],[]]},
        {"Core":[[],[0,[1,[2,0,1]],[2,[3,1],0]],[]],"Skin":{"TermNames":["&harr;","&not;","&le;","&sect;"]},"FreeMaps":[[],[],[],[]]},
        {"Core":[[],[0,[1,0,1],[2,[3,0,1],[3,1,0]]],[]],"Skin":{"TermNames":["&harr;","&equals;","&and;","&le;"]},"FreeMaps":[[],[],[],[]]},
        {"Core":[[],[0,[1,0,[2]],[3,0,[2]]],[]],"Skin":{"TermNames":["&harr;","&le;","&Oslash;","&equals;"]},"FreeMaps":[[],[],[],[]]},
        {"Core":[[],[0,[1,0,1],[0,[1,2,3],[1,[2,0,2],[2,1,3]]]],[]],"Skin":{"TermNames":["&rarr;","&le;","&plus;"]},"FreeMaps":[[],[],[]]},
        {"Core":[[],[0,[1,[2,0,1]],[0,[1,[2,2,3]],[1,[2,[3,0,2],[3,1,3]]]]],[]],"Skin":{"TermNames":["&rarr;","&not","&le;","&plus;"]},"FreeMaps":[[],[],[],[]]},
        {Core:[[],[0,[1,
                              [2,0,[0,[3,0,[4]],1]],
                      [2,2,[0,[2,0,[0,[5,0,2],1]],
                              [2,0,[0,[3,0,[6,2]],1]]]]],
                   [2,0,1]],[[1,2]]],
         Skin:{TermNames:["&rarr;","&and;","&forall;","&equals;","&Oslash;","&le;","&sect;"]},
         FreeMaps:[[],[],[[]],[],[],[],[]]},

{"Core":[[],[0,[1,[2,0,1]],[3,[2,0,[0,[4,[5,0],[6,2,[2,0,[0,[4,[5,0],2],1]]]],1]],[7,0,[3,[8,0,[6,2,[2,0,[0,[4,[5,0],2],1]]]],[1,1]]]]],[[1,2]]],"Skin":{"Name":"L6Mtw.","HypNames":[],"DepNames":[],"VarNames":["V0","V1","V2"],"TermNames":["&rarr;","&not;","&forall;","&and;","&le;","&sect;","&upsilon;","&exist;","&equals;"],"Delimiters":[]},"Tree":{"Cmd":"stmt","Deps":[],"Proof":[]},"FreeMaps":[[],[],[[]],[],[],[],[[]],[[]],[]]}

        ,
        {"Core":[[],[0,[1,[2,0,1]],[3,[4,2,[2,0,[0,[3,[5,0],2],1]]],[4,3,[2,0,[0,[3,[5,0],3],1]]]]],[[1,2,3]]],"Skin":{"Name":"ohS5HB","HypNames":[],"DepNames":[],"VarNames":["V0","V1","V2","V3"],"TermNames":["&rarr;","&not;","&forall;","&le;","&upsilon;","&sect;"],"Delimiters":[]},"Tree":{"Cmd":"stmt","Deps":[],"Proof":[]},"FreeMaps":[[],[],[[]],[],[[]],[]]}

        ,
        {"Core":[[],[0,0,[1,1,[2,[3,2,1],[3,3,1]]]],[[2,1],[3,1]]],"Skin":{"TermNames":["&rarr;","&exist;","&and;","&le;"]},"FreeMaps":[[],[[]],[],[]]}
        
    ],

})
