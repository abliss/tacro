({
    name:"&vert;",
    depends:["&times;"],  
    axioms:[
    ],
    goals:[
        {"Core":[[[0,
                   [1,0,[2,[3,1,0],2]],[1,3,[2,[3,1,3],2]]]],
                 [0,[1,0,[2,[3,1,0],2]],[4,1,2]],
                 [[1, 0],[2, 0] ]],
         "Skin":{"Name":"df-divides","TermNames":["&harr;","&exist;","&equals;","&times;","&vert;"]},
         "FreeMaps":[[],[[]],[],[],[]],
         Tree:{Cmd:"defthm",Definiendum: 4}
        },
        {"Core":[[],[0,0,[1,0,1]],[]],"Skin":{"TermNames":["&vert;","&times;"]},"FreeMaps":[[],[]]},
        // only needed in euclidlem?
        // {"Core":[[],[0,0,[1]],[]],"Skin":{"TermNames":["&vert;","&Oslash;"]},"FreeMaps":[[],[]]},
        {"Core":[[],[0,0,0],[]],"Skin":{"TermNames":["&vert;"]},"FreeMaps":[[]]},
        {"Core":[[],[0,[0,[1,0,0],1],1],[]],"Skin":{"TermNames":["&rarr;","&vert;"]},"FreeMaps":[[],[]]},
        {"Core":[[],[0,[1,0,1],[2,[3,0,2],[3,1,2]]],[]],"Skin":{"TermNames":["&rarr;","&equals;","&harr;","&vert;"]},"FreeMaps":[[],[],[],[]]},
        {"Core":[[],[0,[1,0,1],[2,[3,2,0],[3,2,1]]],[]],"Skin":{"TermNames":["&rarr;","&equals;","&harr;","&vert;"]},"FreeMaps":[[],[],[],[]]},
        {"Core":[[],[0,[1,0,1],[0,[1,1,2],[1,0,2]]],[]],"Skin":{"TermNames":["&rarr;","&vert;"]},"FreeMaps":[[],[]]},
        {"Core":[[],[0,[1,0,1],[0,[1,2,0],[1,2,1]]],[]],"Skin":{"TermNames":["&rarr;","&vert;"]},"FreeMaps":[[],[]]},
        {"Core":[[],[0,[1,0,1],[1,[2,0,[3,2]],[2,1,[3,2]]]],[]],"Skin":{"TermNames":["&harr;","&vert;","&times;","&sect;"]},"FreeMaps":[[],[],[],[]]},
        //? {"Core":[[],[0,[1,0,1],[1,[2,2,0],[2,2,1]]],[]],"Skin":{"TermNames":["&harr;","&vert;","&times;"]},"FreeMaps":[[],[],[]]},
        //{"Core":[[],[0,[1,0,1],[2,[3,0,1],[3,1,0]]],[]],"Skin":{"TermNames":["&harr;","&equals;","&and;","&vert;"]},"FreeMaps":[[],[],[],[]]},
        {"Core":[[],[0,[1,[2],0],[3,[2],0]],[]],"Skin":{"TermNames":["&harr;","&vert;","&Oslash;","&equals;"]},"FreeMaps":[[],[],[],[]]},
        {"Core":[[],[0,[1,0,1],[0,[1,2,3],[1,[2,0,2],[2,1,3]]]],[]],"Skin":{"TermNames":["&rarr;","&vert;","&times;"]},"FreeMaps":[[],[],[]]},
        {"Core":[[],[0,[1,0,1],[0,[1,0,[2,1,2]],[1,0,2]]],[]],"Skin":{"TermNames":["&rarr;","&vert;","&plus;"]},"FreeMaps":[[],[],[]]},
        {"Core":[[],[0,[1,[2,[2,0]],[2,[3]]],1],[]],"Skin":{"TermNames":["&rarr;","&vert;","&sect;","&Oslash;"]},"FreeMaps":[[],[],[],[]]},
        {"Core":[[],[0,0,[1,1,[2,2,[0,[3,[4,2],3],[5,[4,2],[4,[4,1]]]]]]],[[3,1,2]]],
         "Skin":{"TermNames":["&rarr;","&exist;","&forall;","&le;","&sect;","&vert;"]},"FreeMaps":[[],[[]],[[]],[],[],[]]}, 
    ],
})
