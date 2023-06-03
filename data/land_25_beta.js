({
    name:"&beta;",
    depends:["&sbquo;"],
    axioms:[    ],
    goals:[{"Core":[[],
               [0,
                [1,0,[2,[3,[4,[3,[5,1,0]],2]],3]],
                [6,2,3,1]
               ],
               [[1,0],[2,0],[3,0]]
              ],
       // don't forget: to verify, the terms should be numbered as if
       // the conclusion needed no hypotheses
       "Skin":{"Name":"df-min","TermNames":
               ["&equals;","min","&vert;","&sect;","&times;","&sbquo;","&beta;"]},
       "FreeMaps":[[],[[]],[],[],[],[],[]],
           Tree:{Cmd:"defthm",Definiendum: 6}}
,
           {"Core":[[],
                    [0,0,[0,1,[1,2,[2,[3,2,3],[4,[5,0,1,2],4]]]]],
                    [[3,0,1,2],[4,0,1]]],
            "Skin":{"TermNames":["&exist;","&forall;","&rarr;","&le;","&equals;","&beta;"]},
            "FreeMaps":[[[]],[[]],[],[],[],[]]},
    ]
})
