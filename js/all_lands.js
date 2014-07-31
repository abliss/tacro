// TODO: hack
(function(module) {
	module.exports = [
{
    name:"&and;",
    depends:["&not;"],  // TODO: figure out a content-addressable scheme
    goals:[
        // Future definitions using the biconditional can be automatic, but
        // this definition *of* the biconditional must be manual.
        {Core:[[],[0,[1,
                      [1,
                       [2,0,1],[0,[1,0,[0,1]]]],
                      [0,[1,   [0,[1,0,[0,1]]],
                       [2,0,1]]]]],[]],
         Skin:{TermNames:["&not;","&rarr;","&and;"]},
         Tree:{Cmd:"defthm",Definiendum: 2}
        },
        {Core:[[],[0,[1,0,1],[2,[0,0,[2,1]]]],[]],
         Skin:{TermNames:["&rarr;","&and;","&not;"]}},
        {Core:[[],[0,[1,[0,0,[1,1]]],[2,0,1]],[]],
         Skin:{TermNames:["&rarr;","&not;","&and;"]}},
        {Core:[[],[0,[0,0,1],[0,[1,0,2],[1,1,2]]],[]],
         Skin:{TermNames:["&rarr;","&and;"]}},
        {Core:[[],[0,[0,0,1],[0,[1,2,0],[1,2,1]]],[]],
         Skin:{TermNames:["&rarr;","&and;"]}},
        {Core:[[],[0,[1,0,1],0],[]],
         Skin:{TermNames:["&rarr;","&and;"]}},
        {Core:[[],[0,[1,0,1],1],[]],
         Skin:{TermNames:["&rarr;","&and;"]}},
        {Core:[[],[0,0,[0,1,[1,0,1]]],[]],
         Skin:{TermNames:["&rarr;","&and;"]}},
        {Core:[[],[0,0,[1,0,0]],[]],
         Skin:{TermNames:["&rarr;","&and;"]}},
        {Core:[[],[0,[1,0,1],[1,1,0]],[]],
         Skin:{TermNames:["&rarr;","&and;"]}},
        {Core:[[],[0,[0,0,1],[0,0,[1,0,1]]],[]],
         Skin:{TermNames:["&rarr;","&and;"]}},
        {Core:[[],[0,[0,0,[0,1,2]],[0,[1,0,1],2]],[]],
         Skin:{TermNames:["&rarr;","&and;"]}},
        {Core:[[],[0,[1,0,[0,0,1]],1],[]],
         Skin:{TermNames:["&rarr;","&and;"]}},
        {Core:[[],[0,[1,0,[0,1,2]],[0,1,[1,0,2]]],[]],
         Skin:{TermNames:["&rarr;","&and;"]}},
        {Core:[[],[0,[1,[0,0,1],[0,2,3]],[0,[1,0,2],[1,1,3]]],[]],
         Skin:{TermNames:["&rarr;","&and;"]}},
],
},
{
    name:"&equals;",
    depends:["&exist;"],  // TODO: figure out a content-addressable scheme
    axioms:[
        {Core:[[],[0,[1,0,1],[0,[1,0,2],[1,1,2]]],[]],
         Skin:{TermNames:["&rarr;","&equals;"]}},
        {Core:[[],[0,[1,0,[0,[2,0,1]]]],[[1,0]]],
         Skin:{TermNames:["&not;","&forall;","&equals;"]}},
    ],
    goals:[
        {Core:[[],[0,0,[1,0,1]],[[1,0]]],
         Skin:{TermNames:["&exist;","&equals;"]}},

        {Core:[[],[0,0,0],[]],
         Skin:{TermNames:["&equals;"]}},
        {Core:[[],[0,[1,0,1],[0,[1,0,2],[1,2,1]]],[]],Skin:{TermNames:["&rarr;","&equals;"]}},
        {Core:[[],[0,[1,0,1],[1,1,0]],[]],Skin:{TermNames:["&rarr;","&equals;"]}},
        {Core:[[],[0,[1,0,1],[1,1,0]],[]],Skin:{TermNames:["&harr;","&equals;","&rarr;"]}},
        //XXX
        {Core:[[],[0,[0,[1,0,[2,0,1]],2],2],[[1,0]]],
               Skin:{TermNames:["&rarr;","&exist;","&equals;"]}},

    ],
},
{
    name:"&exist;",
    depends:["&forall;"],  // TODO: figure out a content-addressable scheme
    goals:[
        {Core:[[],[0,[1,[2,0,[1,1]]],[3,0,1]],[]],
         Skin:{TermNames:["&harr;","&not;","&forall;","&exist;"]},
         Tree:{Cmd:"defthm",Definiendum: 3}},

        {Core:[[],[0,[1,0,1],[2,[3,0,[2,1]]]],[]],
         Skin:{TermNames:["&harr;","&exist;","&not;","&forall;"]}},
        {Core:[[],[0,[1,[2,0,1],[3,0,2]],[3,0,[1,1,2]]],[]],
         Skin:{TermNames:["&rarr;","&and;","&forall;","&exist;"]}},
        {Core:[[],[0,0,[1,1,0]],[]],
         Skin:{TermNames:["&rarr;","&exist;"]}},
        {Core:[[],[0,[1,0,1],[2,0,1]],[]],
         Skin:{TermNames:["&rarr;","&forall;","&exist;"]}},
        {Core:[[],[0,[1,0,[0,1,2]],[0,[2,0,1],[2,0,2]]],[]],
         Skin:{TermNames:["&rarr;","&forall;","&exist;"]}},
        {Core:[[],[0,[1,0,[2,1,2]],[2,[3,0,1],[3,0,2]]],[]],
         Skin:{TermNames:["&rarr;","&forall;","&harr;","&exist;"]}},
        {Core:[[],[0,[1,0,1],[0,[2,0,[0,1,2]],[1,0,2]]],[]],
         Skin:{TermNames:["&rarr;","&exist;","&forall;"]}},
        {Core:[[],[0,[1,0,1],1],[[1,0]]],
         Skin:{TermNames:["&rarr;","&exist;"]}},
    ],
},
{
    name:"&forall;",
    depends:["&or;"],  // TODO: figure out a content-addressable scheme
    axioms:[
        {Core:[[0],[0,1,0],[]], // generify
         Skin:{TermNames:["&forall;"]}},
        {Core:[[],[0,[1,0,1],1],[]],
         Skin:{TermNames:["&rarr;","&forall;"]}},
        {Core:[[],[0,[1,0,[0,1,2]],[0,[1,0,1],[1,0,2]]],[]],
         Skin:{TermNames:["&rarr;","&forall;"]}},
        {Core:[[],[0,[1,0,[1,1,2]],[1,1,[1,0,2]]],[]],
         Skin:{TermNames:["&rarr;","&forall;"]}},
        {Core:[[],[0,[1,[2,0,1]],[2,0,[1,[2,0,1]]]],[]],
         Skin:{TermNames:["&rarr;","&not;","&forall;"]}},
        {Core:[[],[0,0,[1,1,0]],[[0,1]]],
         Skin:{TermNames:["&rarr;","&forall;"]}},
    ],
    goals:[
        {Core:[[],[0,[1,0,[2,1,2]],[0,[1,0,1],[1,0,2]]],[]],
         Skin:{TermNames:["&rarr;","&forall;","&harr;"]}},
        {Core:[[],[0,[1,0,[2,1,2]],[2,[1,0,1],[1,0,2]]],[]],
         Skin:{TermNames:["&rarr;","&forall;","&harr;","&and;"]}},
        {Core:[[],[0,[1,0,[2,1,2]],[1,0,1]],[]],
         Skin:{TermNames:["&rarr;","&forall;","&and;"]}},
        {Core:[[],[0,[1,0,[2,1,2]],[2,[1,0,1],[1,0,2]]],[]],
         Skin:{TermNames:["&rarr;","&forall;","&and;"]}},
        {Core:[[],[0,[1,0,[2,1,2]],[2,[1,0,1],[1,0,2]]],[]],
         Skin:{TermNames:["&harr;","&forall;","&and;","&rarr;"]}},
        {Core:[[],[0,[1,0,[1,1,2]],[1,1,[1,0,2]]],[]],
         Skin:{TermNames:["&harr;","&forall;","&rarr;","&and;"]}},
        {Core:[[],[0,[0,0,1],[0,[1,1],[1,0]]],[]],
         Skin:{TermNames:["&harr;","&not;","&rarr;","&and;"]}},
        {Core:[[],[0,[1,0,[2,1,2]],[2,[1,0,[3,2]],[1,0,[3,1]]]],[]],
         Skin:{TermNames:["&rarr;","&forall;","&harr;","&not;"]}},
        {Core:[[],[0,[0,[1,0,[0,1,1]],2],2],[]],
         Skin:{TermNames:["&rarr;","&forall;"]}},
    ],
},
{
    name:"&harr;",
    depends:["&and;"],  // TODO: figure out a content-addressable scheme
    goals:[
        {Core:[[],[0,[1,0,0],[1,1,1]],[]],
         Skin:{TermNames:["&and;","&rarr;"]}},

        {Core:[[],[0,[1,[2,1,2],[0,[1,1,2],[1,2,1]]],
                   [1,[0,[1,1,2],[1,2,1]],[2,1,2]]],[]],
         Skin:{TermNames:["&and;","&rarr;","&harr;"]},
         Tree:{Cmd:"defthm",Definiendum: 2}},

        {Core:[[],[0,[1,0,1],[2,[0,0,1],[0,1,0]]],[]],
         Skin:{TermNames:["&rarr;","&harr;","&and;"]},
        },
        {Core:[[],[0,[1,[0,0,1],[0,1,0]],[2,0,1]],[]],
         Skin:{TermNames:["&rarr;","&and;","&harr;"]}},
        {Core:[[],[0,[1,0,1],[0,0,1]],[]],
         Skin:{TermNames:["&rarr;","&harr;"]}},
        {Core:[[],[0,[1,0,1],[0,1,0]],[]],
         Skin:{TermNames:["&rarr;","&harr;"]}},
        {Core:[[],[0,[1,0,1],[1,[0,1,2],[0,0,2]]],[]],
         Skin:{TermNames:["&rarr;","&harr;"]}},
        {Core:[[],[0,[1,0,1],[1,[0,2,0],[0,2,1]]],[]],
         Skin:{TermNames:["&rarr;","&harr;"]}},
        {Core:[[],[0,[1,0,1],[1,[1,0,2],[1,1,2]]],[]],
         Skin:{TermNames:["&rarr;","&harr;"]}},
        {Core:[[],[0,[1,0,1],[1,[1,2,0],[1,2,1]]],[]],
         Skin:{TermNames:["&rarr;","&harr;"]}},
        {Core:[[],[0,0,[0,[1,0,1],1]],[]],
         Skin:{TermNames:["&rarr;","&harr;"]}},
        {Core:[[],[0,0,[0,[1,1,0],1]],[]],
         Skin:{TermNames:["&rarr;","&harr;"]}},
        {Core:[[],[0,[1,0,1],[1,[2,0,2],[2,1,2]]],[]],
         Skin:{TermNames:["&rarr;","&harr;","&and;"]}},
        {Core:[[],[0,[1,0,1],[1,[2,2,0],[2,2,1]]],[]],
         Skin:{TermNames:["&rarr;","&harr;","&and;"]}},
        {Core:[[],[0,[1,0,1],[1,[2,1],[2,0]]],[]],
         Skin:{TermNames:["&rarr;","&harr;","&not;"]}},
        {Core:[[],[0,[0,0,1],[0,1,0]],[]],
         Skin:{TermNames:["&harr;"]}},
        {Core:[[],[0,0,0],[]],
         Skin:{TermNames:["&harr;"]}},
        {Core:[[],[0,0,[1,[1,0]]],[]],
         Skin:{TermNames:["&harr;","&not;"]}},
        {Core:[[],[0,[1,0,1],[1,[2,1],[2,0]]],[]],
         Skin:{TermNames:["&harr;","&rarr;","&not;"]}},
        {Core:[[],[0,[1,0,1],[2,[3,0,[2,1]]]],[]],
         Skin:{TermNames:["&harr;","&and;","&not;","&rarr;"]}},
        {Core:[[],[0,[1,0,1],[1,1,0]],[]],
         Skin:{TermNames:["&harr;","&and;"]}},
        {Core:[[],[0,0,[1,0,0]],[]],
         Skin:{TermNames:["&harr;","&and;"]}},
        {Core:[[],[0,[1,0,[1,1,2]],[1,1,[1,0,2]]],[]],
         Skin:{TermNames:["&harr;","&rarr;"]}},
        {Core:[[],[0,[1,[1,0,1],2],[1,0,[1,1,2]]],[]],
         Skin:{TermNames:["&harr;","&and;"]}},
        {Core:[[],[0,[1,0,[1,1,2]],[1,[2,0,1],2]],[]],
         Skin:{TermNames:["&harr;","&rarr;","&and;"]}},
        {Core:[[],[0,[0,0,1],[1,[2,0,1],[2,1,0]]],[]],
         Skin:{TermNames:["&harr;","&and;","&rarr;"]}},
        {Core:[[],[0,[1,0,1],[1,[1,2,0],[1,1,2]]],[]],
         Skin:{TermNames:["&rarr;","&harr;"]}},
        {Core:[[],[0,[0,0,1],[0,[0,1,0],[1,0,1]]],[]],
         Skin:{TermNames:["&rarr;","&harr;","&and;"]}},
        {Core:[[],[0,[1,[2,0,1],[2,0,2]],[2,0,[1,1,2]]],[]],
         Skin:{TermNames:["&harr;","&and;","&rarr;"]}},
        {Core:[[],[0,[1,[2,0,1],[2,0,2]],[2,1,2]],[]],
         Skin:{"TermNames":["&rarr;","&and;","&harr;"]}},
    ],
},
{
    name:"&not;",
    depends:["&rarr;"],  // TODO: figure out a content-addressable scheme
    axioms:[
        // ax3
        {Core:[[],[0,[0,[1,0],[1,1]],[0,1,0]],[]],
         Skin:{TermNames:["&rarr;","&not;"]}},
    ],
    goals:[
        {Core:[[],[0,[1,0],[0,0,1]],[]],
         Skin:{TermNames:["&rarr;","&not;"]}},
        {Core:[[],[0,[1,[1,0]],0],[]],
         Skin:{TermNames:["&rarr;","&not;"]}},
        {Core:[[],[0,0,[1,[1,0]]],[]],
         Skin:{TermNames:["&rarr;","&not;"]}},
        {Core:[[],[0,[0,0,1],[0,[1,1],[1,0]]],[]],
         Skin:{TermNames:["&rarr;","&not;"]}},
        {Core:[[],[0,[1,[0,0,1]],[1,1]],[]],
         Skin:{TermNames:["&rarr;","&not;"]}},
        {Core:[[],[0,[1,[0,0,1]],0],[]],
         Skin:{TermNames:["&rarr;","&not;"]}},
        {Core:[[],[0,0,[0,[1,1],[1,[0,0,1]]]],[]],
         Skin:{TermNames:["&rarr;","&not;"]}},
        {Core:[[],[0,[0,[1,0],0],0],[]],
         Skin:{TermNames:["&rarr;","&not;"]}},
        {Core:[[],[0,[1,[1,0,0],[0,[1,1,1]]]],[]],
         Skin:{TermNames:["&not;","&rarr;"]}},
    ],
},
{
    name:"&or;",
    depends:["&harr;"],  // TODO: figure out a content-addressable scheme
    goals:[
        {Core:[[],[0,[1,[2,0],1],[3,0,1]],[]],
         Skin:{TermNames:["&harr;","&rarr;","&not;","&or;"]},
         Tree:{Cmd:"defthm",Definiendum: 3}},

        {Core:[[],[0,0,[1,1,0]],[]],
         Skin:{TermNames:["&rarr;","&or;"]}},
        {Core:[[],[0,0,[1,0,1]],[]],
         Skin:{TermNames:["&rarr;","&or;"]}},
        {Core:[[],[0,[0,0,1],[0,[1,0,2],[1,1,2]]],[]],
         Skin:{TermNames:["&rarr;","&or;"]}},
        {Core:[[],[0,[1,0,1],[1,[2,0,2],[2,1,2]]],[]],
         Skin:{TermNames:["&rarr;","&harr;","&or;"]}},
        {Core:[[],[0,[0,0,1],[0,[1,2,0],[1,2,1]]],[]],
         Skin:{TermNames:["&rarr;","&or;"]}},
        {Core:[[],[0,[1,0,1],[1,[2,2,0],[2,2,1]]],[]],
         Skin:{TermNames:["&rarr;","&harr;","&or;"]}},
        {Core:[[],[0,[1,0,1],[1,1,0]],[]],
         Skin:{TermNames:["&harr;","&or;"]}},
        {Core:[[],[0,[1,[1,0,1],2],[1,0,[1,1,2]]],[]],
         Skin:{TermNames:["&harr;","&or;"]}},
    ],
},
{
    name:"&Oslash;",
    depends:["&equals;"],  // TODO: figure out a content-addressable scheme
    axioms:[
        // TODO: this axiom is unnecessary, though it does force equal into 
        // termvars, and gives us something to put in this file.
        {Core:[[],[0,[1],[1]],[]],
         Skin:{TermNames:["&equals;","&Oslash;"]}},
    ],
    goals:[

    ],
},
{
    name:"&plus;",
    depends:["&Osect;"],  // TODO: figure out a content-addressable scheme
    axioms:[
        {Core:[[],[0,[1,0,1],[0,[1,2,3],[1,[2,0,2],[2,1,3]]]],[]],
         Skin:{TermNames:["&rarr;","&equals;","&plus;"]}},
        {Core:[[],[0,[1,0,[2]],0],[]],
         Skin:{TermNames:["&equals;","&plus;","&Oslash;"]}},
        {Core:[[],[0,[1,0,[2,1]],[2,[1,0,1]]],[]],
         Skin:{TermNames:["&equals;","&plus;","&sect;"]}},
    ],
    goals:[
    ],
},
{
    name:"&rarr;",
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
         Skin:{TermNames:["&rarr;"]}},
        // ax1
        {Core:[[],[0,0,[0,1,0]],[]],
         Skin:{TermNames:["&rarr;"]}},
        // imim1
        {Core:[[],[0,[0,0,1],[0,[0,1,2],[0,0,2]]],[]],
         Skin:{TermNames:["&rarr;"]}},
        // imim2
        {Core:[[],[0,[0,0,1],[0,[0,2,0],[0,2,1]]],[]],
         Skin:{TermNames:["&rarr;"]}},
        // pm2.43
        {Core:[[],[0,[0,0,[0,0,1]],[0,0,1]],[]],
         Skin:{TermNames:["&rarr;"]}},
    ],
    goals:[
        // ax2
        {Core:[[],[0,[0,0,[0,1,2]],[0,[0,0,1],[0,0,2]]],[]],
         Skin:{TermNames:["&rarr;"]}},
        {Core:[[],[0,[0,[0,0,1],2],[0,1,2]],[]],
         Skin:{TermNames:["&rarr;"]}},
        {Core:[[],[0,[0,0,[0,1,2]],[0,1,[0,0,2]]],[]],
         Skin:{TermNames:["&rarr;"]}},
        {Core:[[],[0,[0,0,1],[0,0,0]],[]],
         Skin:{TermNames:["&rarr;"]}},
        {Core:[[],[0,0,[0,1,1]],[]],
         Skin:{TermNames:["&rarr;"]}},
        {Core:[[],[0,0,0],[]],
         Skin:{TermNames:["&rarr;"]}},
        {Core:[[],[0,0,[0,1,[0,[0,1,2],2]]],[]],
         Skin:{TermNames:["&rarr;"]}},
        {Core:[[],[0,0,[0,[0,0,1],1]],[]],
         Skin:{TermNames:["&rarr;"]}},
        {Core:[[],[0,[0,[0,0,0],1],1],[]],
         Skin:{TermNames:["&rarr;"]}},
    ],
},
{
    name:"&sect;",
    depends:["&Oslash;"],  // TODO: figure out a content-addressable scheme
    axioms:[
        // TODO: this axiom is unnecessary, though it does force equal into 
        {Core:[[],[0,[1,[2],[3,0]]],[]],
         Skin:{TermNames:["&not;","&equals;","&Oslash;","&sect;"]}},
        {Core:[[],[0,[1,0,1],[1,[2,0],[2,1]]],[]],
         Skin:{TermNames:["&rarr;","&equals;","&sect;"]}},
        {Core:[[],[0,[1,[2,0],[2,1]],[1,0,1]],[]],
         Skin:{TermNames:["&rarr;","&equals;","&sect;"]}},
        {Core:[[],[0,[1,0,[0,[2,0,[3]],1]],[0,[1,2,[0,[1,0,[0,[2,0,2],1]],[1,0,[0,[2,0,[4,2]],1]]]],[1,0,1]]],[[1,2]]],
         Skin:{TermNames:["&rarr;","&forall;","&equals;","&Oslash;","&sect;"]}},
    ],
    goals:[
        {Core:[[],[0,[1,0,[1,1,[0,[2,1,[3]],[4,2,3]]]],[0,[1,0,[1,1,[0,[2,1,0],[4,2,4]]]],[0,[1,0,[1,1,[0,[2,1,[5,0]],[4,2,5]]]],[0,[1,0,[1,1,[0,[2,1,6],[4,2,7]]]],[0,3,[0,[1,0,[0,4,5]],7]]]]]],[[2,0],[3,1],[4,1],[5,1],[6,1],[7,1]]],
         Skin:{TermNames:["&rarr;","&forall;","&equals;","&Oslash;","&harr;","&sect;","&and;","&exist;"]}},
    ],
}];
})(module);
