{
    name:"&harr;",
    depends:["&not;"],  // TODO: figure out a content-addressable scheme
    goals:[
        // Future definitions using the biconditional can be automatic, but
        // this definition *of* the biconditional must be manual.
        {Core:[[],[0,[1,0,1],[0,0,1]],[]],
         Skin:{TermNames:["&rarr;","&harr;"]}},
        {Core:[[],[0,[1,0,1],[0,1,0]],[]],
         Skin:{TermNames:["&rarr;","&harr;"]}},
    ],
}
