({
    name:"&perp;",
    depends:["&vert;"],  
    axioms:[    ],
    goals:[
        {"Core":[[[0,
                   [1,0,[2,[3,1,[4,2,0]],[3,1,0]]],
                   [1,3,[2,[3,1,[4,2,3]],[3,1,3]]]]],
                 [0,[1,0,[2,[3,1,[4,2,0]],[3,1,0]]],[5,1,2]],
                 [[1, 0],[2, 0] ]],
         "Skin":{"Name":"df-relprim","TermNames":["&harr;","&forall;","&rarr;","&vert;","&times;","&perp;"]},
         "FreeMaps":[[],[[]],[],[],[],[]],
         Tree:{Cmd:"defthm",Definiendum: 5}
        },
        {"Core":[[],[0,[1,0,1],[0,[2,0,[3,1,2]],[2,0,2]]],[]],"Skin":{"TermNames":["&rarr;","&perp;","&vert;","&times"]},"FreeMaps":[[],[],[],[]]},
        {"Core":[[],[0,[1,0,1],[2,[3,0,2],[3,1,2]]],[]],"Skin":{"TermNames":["&rarr;","&equals;","&harr;","&perp;"]},"FreeMaps":[[],[],[],[]]},
        {"Core":[[],[0,[1,0,1],[2,[3,2,0],[3,2,1]]],[]],"Skin":{"TermNames":["&rarr;","&equals;","&harr;","&perp;"]},"FreeMaps":[[],[],[],[]]},
        {"Core":[[],[0,[1,[2,0],1],[1,1,[2,0]]],[]],"Skin":{"TermNames":["&rarr;","&perp;","&sect;"]},"FreeMaps":[[],[],[]]},
        {"Core":[[],[0,[1,[2,0],[2,1]],[1,[2,1],[2,0]]],[]],"Skin":{"TermNames":["&harr;","&perp;","&sect;"]},"FreeMaps":[[],[],[]]},
        {"Core":[[],[0,[1,0,[2,[3,1],[3,2]]],[4,[1,0,[3,1]],[1,0,[3,2]]]],[]],"Skin":{"TermNames":["&harr;","&perp;","&times;","&sect;","&and;"]},"FreeMaps":[[],[],[],[],[]]},
        {"Core":[[],[0,0,[1,[2,1],[2,[3,[2,1],2]]]],[]],"Skin":{"TermNames":["&rarr;","&perp;","&sect;","&times;"]},"FreeMaps":[[],[],[],[]]},
        
        {"Core":[[],[0,[1,0,[1,1,[0,[2,2,[3,[4,2,0],3]],[0,4,[5,[6,[6,0]],[6,[6,1]]]]]]],[2,5,[3,[1,0,[0,[7,[6,0],6],[0,[1,2,[0,[4,2,0],3]],[8,[6,[6,0]],5]]]],[1,1,[0,4,[9,[8,[6,[6,1]],5]]]]]]],[[3,0,1,5],[4,0,2,5],[6,0,1,2,5]]],"Skin":{"Name":"vyfmV","HypNames":[],"DepNames":[],"VarNames":["V0","V1","V2","V3","V4","V5","V6"],"TermNames":["&rarr;","&forall;","&exist;","&and;","&equals;","&perp;","&sect;","&le;","&vert;","&not;"],"Delimiters":[]},"Tree":{"Cmd":"stmt","Deps":[],"Proof":[]},"FreeMaps":[[],[[]],[[]],[],[],[],[],[],[],[]]},


        {"Core":[[],
                 [0,[1,0,[0,[2,[3,0],1],[4,[3,0],[3,[3,2]]]]],
                  [0,
                   [5,[2,[3,3],1],
                    [5,[2,[3,4],1],
                     [2,[3,3],4]]],
                   [6,[3,[7,[3,3],[3,[3,2]]]],
                    [3,[7,[3,4],[3,[3,2]]]]]]]
                 ,[[1,0],[2,0],[3,0],[4,0]]],
         "Skin":{"TermNames":[
             "&rarr;","&forall;","&le;","&sect;","&vert;","&and;","&perp;","&times;"]},"FreeMaps":[[],[[]],[],[],[],[],[],[]]}, 
    ],
})