({
    name:"&beta;",
    depends:["&sbquo;"],
    axioms:[    ],
    goals:[
        {"Core":[[
            [0,[1,[2,0,1],[3,[4,[5,[4,0],2]],3]]
             ,[1,[2,0,1],[3,[4,[5,[4,0],2]],3]]
            ]],
                 [0,[1,[2,0,1],[3,[4,[5,[4,0],2]],3]],
                  [6,1,2,3,0]],[]],
         // don't forget: to verify, the terms should be numbered as if
       // the conclusion needed no hypotheses
         "Skin":{"Name":"df-min","TermNames":
                 ["&harr;","&and;","&le;","&vert;","&sect;","&times;","&beta;"]},
            "FreeMaps":[[],[],[],[],[],[],[],[]],
           Tree:{Cmd:"defthm",Definiendum: 6}}
        ,
        {"Core":[[],[0,[1,0,1],[2,[3,2,3,4,0],[3,2,3,4,1]]],[]],"Skin":{
            "TermNames":["&rarr;","&equals;","&harr;","&beta;"]},"FreeMaps":[[],[],[],[]]},
        {"Core":[[],[0,[1,0,1],[2,[3,0,2,3,4],[3,1,2,3,4]]],[]],"Skin":{
            "TermNames":["&rarr;","&equals;","&harr;","&beta;"]},"FreeMaps":[[],[],[],[]]},
        {"Core":[[],[0,0,
                     [1,1,[1,2,[2,3,[3,[4,4,1,2,3],[5,[6,3,4],[2,5,[0,[7,5,3],6]]]]]]]
                    ],[[4,1,2,3,5],[6,1,2,3]]],"Skin":
         {"Name":"5CoMgB","HypNames":[],"DepNames":[],"VarNames":["V0","V1","V2","V3","V4","V5","V6"],"TermNames":
          [ "&rarr;","&exist;","&forall;","&harr;","&beta;","&and;","&le;","&equals;"]
          ,"Delimiters":[]},"Tree":{"Cmd":"stmt","Deps":[],"Proof":[]},
         "FreeMaps":[[],[[]],[[]],[],[],[],[],[]]}

,
    ]
})
