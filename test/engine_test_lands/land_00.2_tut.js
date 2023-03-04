({
    name:"tut2",
    depends:[],
    // 0 hyp theorems are displayed in the user's toolbox.
    // 1 hyp theorems get buttons.
    // 2+hyp theorems are not displayed, but ax-mp is special.
    axioms:[
        // NB: instead of the usual Simp+Frege basis for positive propositional
        // calculus,we use one of Hilbert's because it provides the necessary
        // "binding theorems" for rarr over itself.
        // ax-mp
        {Core:[[0,[0,0,1]],1,[]],
         Skin:{TermNames:["&rarr;"]},
         FreeMaps:[[]]},
        // id: can be proved from the 4 below, but makes a nice "universal first step".
        {Core:[[],[0,0,0],[]],
         Skin:{TermNames:["&rarr;"]},
         FreeMaps:[[]]},
        // ax1
        {Core:[[],[0,0,[0,1,0]],[]],
         Skin:{TermNames:["&rarr;"]},
         FreeMaps:[[]]},
    ],
    goals:[
        // Tutorial 1
        {Core:[[],[0,0,[0,0,0]],[]],
         Skin:{TermNames:["&rarr;"]},
         FreeMaps:[[]]},
    ],
})
