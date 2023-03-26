({
    name:"min",
    depends:["&le;"],  
    axioms:[
    ],
    goals:[
      {"Core":[[[0,[1,0,1],[2,
                            [1,0,[2,[3,0,
                                     [7,2,[5,0,[0,[6,[8,0],2],[9,1]]]]
                                    ],1]],
                            [5,0,[0,1,[6,
                                     [7,2,[5,0,[0,[6,[8,0],2],[9,1]]]],
                                       0]]]
                           ]]],
               [0,[1,0,1],[2,
                           [1,0,[2,[3,0,[4,0,1]],1]],
                           [5,0,[0,1,[6,[4,0,1],0]]]
                           ]],
               []],
       // don't forget: to verify, the terms should be numbered as if
       // the conclusion needed no hypotheses
       "Skin":{"Name":"df-min","TermNames":
               ["&rarr;","&exist;","&and;","&equals;","min","&forall;","&le;","&upsilon;","&sect;","&not;"]},
       "FreeMaps":[[],[[]],[],[[]],[],[[]],[],[[]],[],[]],
       Tree:{Cmd:"defthm",Definiendum: 5}}
       
    ],
})

