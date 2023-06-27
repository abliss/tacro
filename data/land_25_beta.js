({
    name:"&beta;",
    depends:["&sbquo;"],
    axioms:[    ],
    goals:[
        {"Core":[
            [
                [0,
                 [1,[2,[3,[2,0],1]],2],
                 [1,[2,[3,[2,0],1]],2]
                 ]
            ],
            [0,
             [1,[2,[3,[2,0],1]],2],
             [4,1,2,0]
             ],
            []
        ],
         // don't forget: to verify, the terms should be numbered as if
       // the conclusion needed no hypotheses
       "Skin":{"Name":"df-min","TermNames":
               ["&harr;","&vert;","&sect;","&times;","&beta;"]},
       "FreeMaps":[[],[],[],[],[],[]],
           Tree:{Cmd:"defthm",Definiendum: 4}}
,
           {"Core":[[],
                    [0,0,[0,1,[1,2,[2,[3,2,3],
                                    [4,[5,[6,0],1,2],
                                     [1,4,[2,[7,4,2],5]]]]]]],
                    [[3,0,1,2,4],[5,0,1,2]]],
            "Skin":{"TermNames":["&exist;","&forall;","&rarr;","&le;","&harr;","&beta;","&sect;","&equals;"]},
            "FreeMaps":[[[]],[[]],[],[],[],[],[],[]]},
    ]
})
