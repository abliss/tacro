({
    name:"min",
    depends:["&le;"],  
    axioms:[
    ],
    goals:[
        /* can't prove anything without E. x A
        {"Core":[[[0,
                   [1,0,[2,1,[3,[4,[5,1],0],[6,2]]]],
                   [1,3,[2,1,[3,[4,[5,1],3],[6,2]]]]]],
                 [0,[1,0,[2,1,[3,[4,[5,1],0],[6,2]]]],
                  [7,1,2]],
                 [[2,0]]],
         "Skin":{"Name":"df-min","TermNames":["&equals;","&upsilon;","&forall;","&rarr;","&le;","&sect;","&not;","min"]},
         "FreeMaps":[[],[[]],[[]],[],[],[],[],[[]]],
         
         Tree:{Cmd:"defthm",Definiendum: 6}
        },
*/
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
       "Skin":{"Name":"df-min","TermNames":
               ["&rarr;","&exist;","&and;","&equals;","min","&forall;","&le;","&upsilon;","&sect;","&not;"]},
       "FreeMaps":[[],[[]],[],[[]],[],[[]],[],[[]],[],[]],
       Tree:{Cmd:"defthm",Definiendum: 5}}
       
/*         
        {"Core":[[],[0,[1,0,1],[2,0,[0,[3,0,[4,0,1]],1]]],[]], 
         "Skin":{"TermNames":["&rarr;","&exist;","&forall;","&equals;","min"]},
         "FreeMaps":[[],[[]],[[]],[],[[]]]},
        {"Core":[[],[2,0,[0,1,[3,[4,0,1],0]]],[]], 
         "Skin":{"TermNames":["&forall;","&rarr;","&le;","min"]},
         "FreeMaps":[[[]],[],[],[[]]]},
*/
    ],
})

