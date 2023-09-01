({
    name:"&rarr;",
    depends:["tut6"],
    // 0 hyp theorems are displayed in the user's toolbox.
    // 1 hyp theorems get buttons.
    // 2+hyp theorems are not displayed, but ax-mp is special.
    axioms:[
        // NB: instead of the usual Simp+Frege basis for positive propositional
        // calculus,we use one of Hilbert's because it provides the necessary
        // "binding theorems" for rarr over itself.
        // pm2.43
        {Core:[[],[0,[0,0,[0,0,1]],[0,0,1]],[]],
         Skin:{TermNames:["&rarr;"]},
         FreeMaps:[[]]},
    ],
    goals:[
        // mp
        {Core:[[],[0,0,[0,[0,0,1],1]],[]],
         Skin:{TermNames:["&rarr;"]},
         FreeMaps:[[]]},
        // idie
        {Core:[[],[0,[0,[0,0,0],1],1],[]],
         Skin:{TermNames:["&rarr;"]},
         FreeMaps:[[]]},
        // con12
        {Core:[[],[0,[0,0,[0,1,2]],[0,1,[0,0,2]]],[]],
         Skin:{TermNames:["&rarr;"]},
         FreeMaps:[[]]},
        // ax2
        {Core:[[],[0,[0,0,[0,1,2]],[0,[0,0,1],[0,0,2]]],[]],
         Skin:{TermNames:["&rarr;"]},
         FreeMaps:[[]]},
        {Core:[[],[0,[0,0,[0,1,2]],[0,[0,2,0],[0,1,0]]],[]],
         Skin:{TermNames:["&rarr;"]},
         FreeMaps:[[]]},
    ],
})
