({
    name:"&plus;",
    depends:["&sect;"],  
    axioms:[
        {Core:[[],[0,[1,0,1],[0,[1,2,3],[1,[2,0,2],[2,1,3]]]],[]],
         Skin:{TermNames:["&rarr;","&equals;","&plus;"]},
         FreeMaps:[[],[],[]]},
        {Core:[[],[0,[1,0,[2]],0],[]],
         Skin:{TermNames:["&equals;","&plus;","&Oslash;"]},
         FreeMaps:[[],[],[]]},
        {Core:[[],[0,[1,0,[2,1]],[2,[1,0,1]]],[]],
         Skin:{TermNames:["&equals;","&plus;","&sect;"]},
         FreeMaps:[[],[],[]]},
    ],
    goals:[
        {"Core":[[],[0,[1,0,1],[1,[2,2,0],[2,2,1]]],[]],
         "Skin":{"TermNames":["&rarr;","&equals;","&plus;"]},
         "FreeMaps":[[],[],[]]},
        {"Core":[[],[0,[1,0,1],[1,[2,0,2],[2,1,2]]],[]],
         "Skin":{"TermNames":["&rarr;","&equals;","&plus;"]},
         "FreeMaps":[[],[],[]]},
        
        {Core:[[],[0,[1,0,1,[2,2,3]],[2,[1,0,1,2],[1,0,1,3]]],[]],
         Skin:{Name: "sbbplus", 
               TermNames:["&equals;", "&int;&int;", "&plus;"]},
         FreeMaps:[[],[[1]],[]]},
/*
        {"Core":[[],[0,0,[1,
                          [2,1,[2,2,[0,[3,3,4],[4,
                                                [3,[5,[6],3],3],
                                                [3,[5,[6],4],4]]]]],
                          0]],[]],
         "Skin":{"TermNames":["&rarr;","&and;","&forall;","&equals;","&harr;","&plus;","&Oslash;"]},         
         "FreeMaps":[[],[],[[]],[],[],[],[]]},
*/
        {Core:[[],[0,[1,[2],0],0],[]],
         Skin:{TermNames:["&equals;","&plus;","&Oslash;"]},
         FreeMaps:[[],[],[]]},
        {Core:[[],[0,[1,0,1],[1,1,0]],[]],
         Skin:{TermNames:["&equals;","&plus;"]},
         FreeMaps:[[],[]]},
        {"Core":[[],[0,[1,[1,0,1],2],[1,0,[1,1,2]]],[]],
         "Skin":{"TermNames":["&equals;","&plus;"]},
         "FreeMaps":[[],[]]},

        {"Core":[[],[0,[1,[2,0,1],[2,2,1]],[1,0,2]],[]],"Skin":{"TermNames":["&harr;","&equals;","&plus;","&Oslash;","&rarr;","&sect;"]},"FreeMaps":[[],[],[],[],[],[]]},
        {"Core":[[],[0,[1,0],[2,0,[1,[3]]]],[]],"Skin":{"Name":"a1suc","TermNames":["&equals;","&sect;","&plus;","&Oslash;"]},"FreeMaps":[[],[],[],[]]},
        {"Core":[[],[0,[1,[2,0,1],[3]],[1,1,[3]]],[]],"Skin":{"TermNames":["&rarr;","&equals;","&plus;","&Oslash;"]},"FreeMaps":[[],[],[],[]]}

    ],
})
