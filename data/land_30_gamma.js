({
    name:"&gamma;" ,
    depends:["&beta;"],
    axioms:[    ],
    goals:[

        {"Core":[
            [
            ],
            [0,
             [1,0, // bound
              [1,1,[1,2, // beta args
                    [5, //both
                     [5, // both
                      [2,7,[3,[5,[4,[10,[11],7],0],[6,[7,1],2,[10,[11],7]]],[8,6,7]]], // 0,7 <bound & beta 0,7 => 7=6, and
                              [5,[4,[10,  9,10],0],[6,[7,1],2,[10,  9,10]]]], // 9,10<bound & beta 9,10; , and
                     [2,3,[2,4,[3,[5,[5,[4,[7,3],9],[4,[10,[7,3],4],0]],[6,[7,1],2,[10,[7,3],4]]], // if S(3)<=9 & S(3),4 <=bound & beta S3,4 ,then
                                [1,5, // there is a 5 s.t.
                              [5,[5,[4,[10,3,5],0],[6,[7,1],2,[10,3,5]]], // 3,5<bound & beta 3,5; , and
                                  [8,12,4] // 12(5) = 4
                                 ]]]]]]]]],
             [9,5,12,6,9,10]],
            []
        ],
         // don't forget: to verify, the terms should be numbered as if
       // the conclusion needed no hypotheses
       "Skin":{"Name":"df-min","TermNames":
               ["&harr;","&exist;","&forall;","&rarr;","&le;",
                "&and;","&beta;","&sect;","&equals;","&gamma;",
                "&sbquo;","&Oslash;","&not;"
               ]},
         "FreeMaps":[[],[[]],[[]],[],[],
                     [],[],[],[],[[2,3,4]],
                     [],[],[]],
         Tree:{Cmd:"defthm",Definiendum: 9}},
        


        {"Core":[[],[0,[1,0,1],[2,[3,2,3,4,5,0],[3,2,3,4,5,1]]],[]],"Skin":{"TermNames":["&rarr;","&equals;","&harr;","&gamma;"]},"FreeMaps":[[],[],[],[[2,3,4]]]},
        {"Core":[[],[0,[1,0,1],[2,[3,2,3,4,0,5],[3,2,3,4,1,5]]],[]],"Skin":{"TermNames":["&rarr;","&equals;","&harr;","&gamma;"]},"FreeMaps":[[],[],[],[[2,3,4]]]},
        {"Core":[[],[0,[1,0,1],[2,[3,2,3,0,4,5],[3,2,3,1,4,5]]],[]],"Skin":{"TermNames":["&rarr;","&equals;","&harr;","&gamma;"]},"FreeMaps":[[],[],[],[[2,3,4]]]},
        {"Core":[[],[0,[1,0,[1,1,[0,[2,0,1],[2,2,3]]]],[3,[4,0,2,4,5,6],[4,1,3,4,5,6]]],[[2,1],[3,0]]],"Skin":{"Name":"CiVNq.","HypNames":[],"DepNames":[],"VarNames":["V0","V1","V2","V3","V4","V5","V6"],"TermNames":["&rarr;","&forall;","&equals;","&harr;","&gamma;"],"Delimiters":[]},"Tree":{"Cmd":"stmt","Deps":[],"Proof":[]},"FreeMaps":[[],[[]],[],[],[[2,3,4]]]}
,
        {"Core":[[],[0,[1,0,[2,1,2]],[3,[4,0,1,3,4,5],[4,0,2,3,4,5]]],[]],"Skin":{"TermNames":["&rarr;","&forall;","&equals;","&harr;","&gamma;"]},"FreeMaps":[[],[[]],[],[],[[2,3,4]]]},
// [gamma,0,1,2,3,4] means applying 1(0) from 2, 3 times, gets to 4
        {"Core":[[],[0,[1,1,2,3,[2],4],[3,4,3]],[]],
         "Skin":{"TermNames":["&rarr;","&gamma;","&Oslash;","&equals;"]},"FreeMaps":[[],[[2,3,4]],[],[]]},
        {"Core":[[],[0,0,[1,1,[2,2,3,4,5,1]]],[[3,1],[4,1],[5,1]]],
        "Skin":{"TermNames":["&rarr;","&exist;","&gamma;"]},"FreeMaps":[[],[],[[2,3,4]]]},

{"Core":[[],[0,[1,0,1,2,[2,3],4],[3,5,[4,[1,0,1,2,3,5],[5,0,[6,[7,0,5],[7,1,4]]]]]],[[1,5],[2,0,5],[3,0,5],[4,0,5]]],"Skin":{"Name":"mxVki.","HypNames":[],"DepNames":[],"VarNames":["V0","V1","V2","V3","V4","V5"],"TermNames":["&harr;","&gamma;","&sect;","&exist;","&and;","&forall;","&rarr;","&equals;"],"Delimiters":[]},"Tree":{"Cmd":"stmt","Deps":[],"Proof":[]},"FreeMaps":[[],[[2,3,4]],[],[[]],[],[[]],[],[]]}

,
        {"Core":[[],[0,[1,0,1,2,3,4],[0,[1,0,1,2,3,5],[2,4,5]]],[[2,0]]],"Skin":{"Name":"T6zknB","HypNames":[],"DepNames":[],"VarNames":["V0","V1","V2","V3","V4","V5"],"TermNames":["&rarr;","&gamma;","&equals;"],"Delimiters":[]},"Tree":{"Cmd":"stmt","Deps":[],"Proof":[]},"FreeMaps":[[],[[2,3,4]],[]]}
,
        {"Core":[[],[0,0,[1,1,[2,2,[3,[4,3,4,5,6,2],[5,2,1]]]]],[[4,1,2],[5,1,2,3],[6,1,2,3]]],"Skin":{"TermNames":["&rarr;","&exist;","&forall;","&harr;","&gamma;","&equals;"]},"FreeMaps":[[],[[]],[[]],[],[[2,3,4]],[]]}
    ]
})
