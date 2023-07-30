({
    name:"pow" ,
    depends:["&gamma;"],
    axioms:[    ],
    goals:[
        // [gamma,0,1,2,3,4] means applying 1(0) from 2, 3 times gets 4
        {"Core":[[[0,[1,0,[2,1,[3,1,2],[4,[5]],3,0]],
                   [1,20,[2,21,[3,21,2],[4,[5]],3,20]]]],
                 [0,[1,0,[2,1,[3,1,2],[4,[5]],3,0]],
                  [6,2,3]],
                 [[2,0,1],[3,0,1]]],
         "Skin":{"Name":"df-pow","TermNames":[
             "&equals;","min","&gamma;","&times;","&sect;",
             "&Oslash;","pow"]},
         "FreeMaps":[[],[[]],[[2,3,4]],[],[],[],[]],
         Tree:{Cmd:"defthm",Definiendum: 6}
        },
        {"Core":[[],[0,[1,0,1],[1,[2,2,0],[2,2,1]]],[]],
         "Skin":{"TermNames":["&rarr;","&equals;","pow"]},
         "FreeMaps":[[],[],[]]},
        {"Core":[[],[0,[1,0,1],[1,[2,0,2],[2,1,2]]],[]],
         "Skin":{"TermNames":["&rarr;","&equals;","pow"]},
         "FreeMaps":[[],[],[]]},
        {"Core":[[],[0,[1,0,[2]],[3,[2]]],[]],                 
         "Skin":{"TermNames":["&equals;","pow","&Oslash;","&sect;"]},
         "FreeMaps":[[],[],[],[]]},
        {Core:[[],[0,[1,0,[2,1]],[3,[1,0,1],0]],[]],
         Skin:{TermNames:["&equals;","pow","&sect;","&times;"]},
         FreeMaps:[[],[],[],[]]},
        
    ]
})
