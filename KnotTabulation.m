(* ::Package:: *)

(* ::Title:: *)
(*Tabulating Composite Knots in Mathematica*)


(* ::Subtitle:: *)
(*This package implements the action of the various Whitten group elements on KnotTheory's PD codes, and includes code for automatically determining some facts about the Whitten symmetry groups of knots and links.*)


BeginPackage["KnotTabulation`"]
Needs["KnotTheory`"]
Needs["whitten`"]
Needs["Combinatorica`"]
Needs["PlotLegends`"]


(* ::Section:: *)
(*Tabulate Composite Knots*)


(* ::Text:: *)
(*The code in this section implements the procedure for tabulating composite knots.*)


(* ::Text:: *)
(*First we include the code for generating the group GAMMA. This group is a function of a list of integers BaseNumsList={n_1,n_2,..,n_k} corresponding the the number of summands involved that belong to the k distinct base types as well as a list of symmetry groups SymGroupsList={Gamma(K_1), Gamma(K_2),..., Gamma(K_k)} corresponding to the symmetry type of the k basetypes.*)


(*Gives the n fold product of group gam. It is expected that group will be the symmetry group of the base type*)
GAMMAn[NumFactors_,gam_]:=Tuples[gam,NumFactors];

(*Gives the permuation group on n elements in the style of whitten.m*)
Perms[n_]:=Select[Tuples[Table[i,{i,1,n}],n],Length[DeleteDuplicates[#]]==n&];

(*Gives the cartesian product of GAMMAn and Perm*)
EachGAMMA[n_,gam_]:=CartesianProduct[GAMMAn[n,gam],Perms[n]];

(*Generates the group GAMMA*)
GAMMA[BaseNumsList_,SymGroupsList_]:=Table[EachGAMMA[BaseNumsList[[i]],SymGroupsList[[i]]],{i,1,Length[BaseNumsList]}];


(* ::Text:: *)
(*Now we define the set X that represents the possible connected sums coming from summands described by BaseNumsList={n_1,n_2,..,n_k}.*)


(*EachX is just the n fold product of gam with itself
This represents the choices for the summands of a single base type 
Note that it would be ideal to use the WhittenEltCompare method here, but it doesn't seem to thread properly for our list structure*)
EachX[NumComps_]:=Reverse[Sort[Tuples[gam,NumComps]]];

(*XSet gives the direct sum of EachX for each basetype involved in the connected sum*)
XSet[BaseNumsList_]:=Table[EachX[BaseNumsList[[i]]],{i,1,Length[BaseNumsList]}];


(* ::Text:: *)
(*Next is the implementation of the action of GAMMA on X that will generate the distinct composites produced from the summands described by BaseNumsList={n_1,n_2,..,n_k}.*)


(*The action of an individual GAMMA element on an element of EachX*)
GTimesX[g_,x_]:=Table[Times[g[[1]][[i]],x[[g[[2]][[i]]]]],{i,1,Length[g[[2]]]}];

(*For an element g of EachGAMMA, compute the g orbit of a element of EachX*)
GetOrbit[g_,x_]:=Module[{orbit},
orbit={x};
FixedPoint[Last[DeleteDuplicates[AppendTo[orbit,GTimesX[g,#]]]]&,x];
Drop[orbit,-1]
];

(*Get the set of orbits of EachGAMMA on an element of EachX
Note that it would be ideal to use the WhittenEltCompare method here, but it doesn't seem to thread properly for our list structure*)
GetOrbitsx[EachGAMMA_,x_]:=Reverse[Sort[DeleteDuplicates[Flatten[Table[GetOrbit[EachGAMMA[[i]],x],{i,1,Length[EachGAMMA]}],1]]]];

(*Get the orbits of EachGAMMA on EachX
Note that it would be ideal to use the WhittenEltCompare method here, but it doesn't seem to thread properly for our list structure*)
GetEachOrbits[EachGAMMA_,EachX_]:=Reverse[Sort[DeleteDuplicates[Table[GetOrbitsx[EachGAMMA,EachX[[i]]],{i,1,Length[EachX]}]]]];

(*Compute the GAMMA orbits of X*)
GetOrbits[GAMMA_,X_]:=Table[GetEachOrbits[GAMMA[[i]],X[[i]]],{i,1,Length[GAMMA]}];

(*Selects a representative from each orbit
Orbits should be of the type outputted by GetOrbits*)
GetOrbitReps[Orbits_]:=Table[Table[Orbits[[i]][[j]][[1]],{j,1,Length[Orbits[[i]]]}],{i,1,Length[Orbits]}];

(*Selects all choice of orbit reps
These correspond to building the distinct composite knots*)
GetCompDirections[OrbitReps_]:=Tuples[OrbitReps];


(* ::Text:: *)
(*We now demonstrate the code by computing the orbits corresponding to the connected sum of two reversible knots of the same basetype.*)


gam={{1,{1},{1}},{1,{-1},{1}},{-1,{1},{1}},{-1,{-1},{1}}};
rev={{1,{1},{1}},{1,{-1},{1}}};
mir={{1,{1},{1}},{-1,{1},{1}}};
neg={{1,{1},{1}},{-1,{-1},{1}}};
none={{1,{1},{1}}};

(*rev2=GetOrbits[GAMMA[{2},{rev}],XSet[{2}]];
rev2reps=GetOrbitReps[rev2];
rev2comps=GetCompDirections[rev2reps]
Length[rev2comps]*)


(* ::Text:: *)
(*Here we can see the 3 distinct composite knots. For example, if we take the connected sum of two trefoils the second and third elements above are the right and left-handed granny knots and the first is the square knot.*)
(**)
(*Let's try a more interesting example! The following example is a 4 summand connected sum of two distinct basetypes. One with reversible symmetry and the other with mirror symmetry.*)


(*comporbs=GetOrbits[GAMMA[{2,2},{rev,mir}],XSet[{2,2}]];
compreps=GetOrbitReps[comporbs];
comps=GetCompDirections[compreps]
Length[comps]*)


(* ::Text:: *)
(*There are 9 distinct composite knots in this case.*)


(* ::Text:: *)
(*Each element of comps tells you what flavors you need to combine.*)


(*comps[[1]]*)


(* ::Section:: *)
(*Composite Whitten Groups*)


(* ::Text:: *)
(*We now implement the computation of the Whitten group of a composite knot.*)


(*Tests if a given element g of EachGAMMA is in the stabilizer of EachOrbit*)
InOrbitQ[g_,EachOrbit_]:=Not[MemberQ[Table[MemberQ[EachOrbit,GTimesX[g,EachOrbit[[i]]]],{i,1,Length[EachOrbit]}],False]]

(*Returns the stabilizer of EachOrbit*)
(*GetEachStab[NumFactors_,EachOrbit_]:=Select[EachGAMMA[NumFactors,gam],InOrbitQ[#,EachOrbit]&];*)
GetEachStab[EachOrbit_]:=Select[EachGAMMA[Length[EachOrbit[[1]]],gam],InOrbitQ[#,EachOrbit]&];

(*Find the diagonal elements of an EachStab*)
GetEachDiags[EachStab_]:=Select[EachStab,Length[DeleteDuplicates[#[[1]]]]==1&];

(*Take the projection of the diagonal elements into the Whitten group*)
ProjEachDiags[EachDiag_]:=DeleteDuplicates[Table[EachDiag[[i]][[1,1]],{i,1,Length[EachDiag]}]];

(*Returns the symmetry group of knot described by EachOrbit*)
GetEachSymGroup[EachOrbit_]:=ProjEachDiags[GetEachDiags[GetEachStab[EachOrbit]]];

(*Returns the symmetry group of the composite knot by taking the intersection of the symmetry group of the knot described
by each collection of base types*)
CompSymGroup[Orbits_]:=Module[{SymGroups,PosSyms},
SymGroups=Table[GetEachSymGroup[Orbits[[i]]],{i,1,Length[Orbits]}];
(*Print[SymGroups];*)
PosSyms=Flatten[SymGroups,1];
Sort[DeleteDuplicates[Intersection@@ SymGroups],WhittenEltCompare]
];


EndPackage[]
