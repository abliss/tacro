({
    name:"&gamma;" ,
    depends:["&beta;"],
    axioms:[    ],
    goals:[

        {"Core":[
            [ // TODO
            ],
            [0,
             [1,0, // bound
              [1,1,[1,2, // beta args
                    [5, //both
                     [5, // both
                      [2,7,[3,[6,0,1,2,[10,[11],7]],[8,6,7]]], // forall 7: 0,7 <bound & beta 0,7 => 7=6, and
                      [6,0,1,2,[10,  9,10]]], // 9,10<bound & beta 9,10; , and
                     [2,3,[2,4,[3,[5,[4,[7,3],9],[6,0,1,2,[10,[7,3],4]]], // forall 3,4: if S(3)<=9 & S(3),4 <=bound & beta S3,4 ,then
                                [1,11, // exists 11 s.t.  
                                 [5,[6,0,1,2,[10,3,11]], //  3,11<bound & beta 3,11; and
                                  [2,5, // forall 5 ,
                                   [3,[8,5,11],[8,12,4]]] // 11=5 -> 12(5) = 4
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

{"Core":[[],[0,[1,0,1,2,[2,3],4],[3,5,[4,[1,0,1,2,3,5],[5,0,[0,[6,0,5],[6,1,4]]]]]],[[1,5],[2,0,5],[3,0,5],[4,0,5]]],"Skin":{"Name":"gHAazB","HypNames":[],"DepNames":[],"VarNames":["V0","V1","V2","V3","V4","V5"],"TermNames":["&rarr;","&gamma;","&sect;","&exist;","&and;","&forall;","&equals;"],"Delimiters":[]},"Tree":{"Cmd":"stmt","Deps":[],"Proof":[]},"FreeMaps":[[],[[2,3,4]],[],[[]],[],[[]],[]]}
        ,
        {"Core":[[],[0,[1,0,1,2,[2,3],4],[3,5,[4,[1,0,1,2,3,5],[5,0,[6,[7,0,5],[7,1,4]]]]]],[[1,5],[2,0,5],[3,0,5],[4,0,5]]],"Skin":{"Name":"mxVki.","HypNames":[],"DepNames":[],"VarNames":["V0","V1","V2","V3","V4","V5"],"TermNames":["&harr;","&gamma;","&sect;","&exist;","&and;","&forall;","&rarr;","&equals;"],"Delimiters":[]},"Tree":{"Cmd":"stmt","Deps":[],"Proof":[]},"FreeMaps":[[],[[2,3,4]],[],[[]],[],[[]],[],[]]}

        ,
        {"Core":[[],[0,[1,0,1,2,3,4],[0,[1,0,1,2,3,5],[2,4,5]]],[[2,0]]],"Skin":{"Name":"T6zknB","HypNames":[],"DepNames":[],"VarNames":["V0","V1","V2","V3","V4","V5"],"TermNames":["&rarr;","&gamma;","&equals;"],"Delimiters":[]},"Tree":{"Cmd":"stmt","Deps":[],"Proof":[]},"FreeMaps":[[],[[2,3,4]],[]]}
,
        {"Core":[[],[0,[1,0,[2,1,[1,2,[0,[3,2,0],[3,3,1]]]]],[2,4,[4,2,3,5,6,4]]],[[3,0,1,4],[5,1,4],[6,4]]],"Skin":{"Name":"hUxM2B","HypNames":[],"DepNames":[],"VarNames":["V0","V1","V2","V3","V4","V5","V6"],"TermNames":["&rarr;","&forall;","&exist;","&equals;","&gamma;"],"Delimiters":[]},"Tree":{"Cmd":"stmt","Deps":[],"Proof":[]},"FreeMaps":[[],[[]],[[]],[],[[2,3,4]]]}

,
        {"Core":[[],[0,[1,0,[2,1,[1,2,[0,[3,2,0],[3,3,1]]]]],[2,4,[1,5,[4,[5,2,3,6,7,5],[3,5,4]]]]],[[3,4,5],[6,1,2,4,5],[7,2,4,5]]],"Skin":{"Name":"mv0dk.","HypNames":[],"DepNames":[],"VarNames":["V0","V1","V2","V3","V4","V5","V6","V7"],"TermNames":["&rarr;","&forall;","&exist;","&equals;","&harr;","&gamma;"],"Delimiters":[]},"Tree":{"Cmd":"stmt","Deps":[],"Proof":[]},"FreeMaps":[[],[[]],[[]],[],[],[[2,3,4]]]}

    ]
})
