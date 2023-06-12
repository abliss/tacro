({
    name:"&upsilon;",
    depends:["&sect;"],  
    axioms:[
        // Induction axiom with upsilon operator
        {Core:[[],[0,   [1,0,[0,[2,0,   [3]     ],1]],
                   [0,[4,[1,0,1]],
                    [4,[0,
                        [1,0,[0,[2,0,   [5,0,1] ],1]],
                        [1,0,[0,[2,0,[6,[5,0,1]]],1]]]]
                   ]],[]],
         Skin:{TermNames:["&rarr;","&forall;","&equals;","&Oslash;","&not;","&upsilon;","&sect;"]},
         FreeMaps:[[],[[]],[],[],[],[[]],[]]},
    ],
    goals:[
                {Core:[[],[0,[1,
                              [2,0,[0,[3,0,[4]],1]],
                      [2,2,[0,[2,0,[0,[3,0,2],1]],
                              [2,0,[0,[3,0,[5,2]],1]]]]],
                   [2,0,1]],[[1,2]]],
        Skin:{TermNames:["&rarr;","&and;","&forall;","&equals;","&Oslash;","&sect;"]},
        FreeMaps:[[],[],[[]],[],[],[]]},

        //lefoo
         {Core:[[],[0,[1,[2,0,[3]]],[4,1,[2,0,[5,1]]]],[[0,1]]],
         Skin:{TermNames:["&rarr;","&not;","&equals;","&Oslash;","&exist;","&sect;"]},
          FreeMaps:[[],[],[],[],[[]],[]]},
        
    ],
})
