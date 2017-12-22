(* ::Package:: *)

BeginPackage["Loop2`"]


OneLoop::usage="OneLoop[], i.e. OneLoop[{{k-p},{k,\!\(\*SuperscriptBox[\(m\), \(2\)]\)}";
TwoLoop::usage="";
FeynmanParametrize::usage="";
Ffeyn::usage="";
FeynmanParametrize::listQ="Variable \"`1`\" is not a list. ";
FeynmanParametrize::denor="Denorminator list is too short. ";
(*FeynmanParametrize::numer="The last line of the input list is not numbers, please add the power of denorminators. ";*)


Begin["Private`"]


(* ::Input:: *)
(*1/(4 \[Pi])^(d/2) Gamma[\[Beta]+d/2]/Gamma[d/2] Gamma[n-d/2-\[Beta]] / Gamma[n] (1/\[CapitalDelta])^(n-d/2-\[Beta])*)


(* ::DisplayFormula:: *)
(*Integration: \[Integral]\[DifferentialD]^dk/(2\[Pi])^d k^(2\[Beta])/(k^2+\[CapitalDelta])^n*)


Ffeyn[\[CapitalDelta]_,d_,n_,\[Beta]_,OptionsPattern[{NoDelta->False}]]:=
If[OptionValue[NoDelta],1/(4 \[Pi])^(d/2) Gamma[\[Beta]+d/2]/Gamma[d/2] Gamma[n-d/2-\[Beta]] / Gamma[n],1/(4 \[Pi])^(d/2) Gamma[\[Beta]+d/2]/Gamma[d/2] Gamma[n-d/2-\[Beta]] / Gamma[n] (1/\[CapitalDelta])^(n-d/2-\[Beta])];


FeynmanParametrize[denor_]:=Module[{xivars,measure,xipart,gammapart,integranddenor,explist},
If[ListQ@denor,,Message[FeynmanParametrize::listQ,denor];Abort[]];
explist=Last@#&/@denor;
xivars=ToExpression["x"<>ToString[#]]&/@Range@Length@denor;
(*If[AllTrue[explist,NumberQ],,Message[FeynmanParametrize::numer]];*)
measure=({#,0,1}&/@xivars);
xipart=DiracDelta[Plus@@xivars-1] Times@@MapThread[#1^(#2-1)&,{xivars,explist}];
gammapart=Gamma[Plus@@explist]/Times@@Gamma/@explist;
integranddenor=MapThread[Which[Length@#1>2,#2(#1[[1]]^2-#1[[2]]),Length@#1==2,#2 #1[[1]]^2]&,{denor,xivars}];
If[AllTrue[integranddenor,!MatchQ[#,Null]&],,Message[FeynmanParametrize::denor];Abort[]];
Put[{measure,xipart,gammapart,integranddenor},LocalObject["FeynmanParametrization"]]
];


ExpandVector[expr_]:=ReplaceAll[expr,


(* ::Input:: *)
(*(k^2+2k.p+p^2)^2//Expand*)


(* ::Input:: *)
(*CoefficientList[%,k]*)


OneLoop[denor_,nor_,var_,dim_,opts:OptionsPattern[{DisplayTempResults->False,ListForm->False}]]:=
Module[{feyn,colist,shift,Delta,newnor,nnapart,res,int},
feyn=Get[FeynmanParametrize[denor]];
colist=FactorTerms[#,{x1,x2,x3}]&/@CoefficientList[Plus@@Last@feyn,var]//.{x1+x2+x3->1};
shift=colist[[2]]/2;
Delta=colist[[1]]-(shift)^2;
newnor=nor/.{var->var-shift};
nnapart=DeleteCases[MapIndexed[#1 Boole[OddQ[First@#2]]&,CoefficientList[newnor,var]],_?(#==0&)];
If[OptionValue[DisplayTempResults],Print["integrand=",Plus@@MapIndexed[#1 Ffeyn[Subscript[\[CapitalDelta], var],dim,Total[Last@#&/@denor],2(First[#2]-1)]&,nnapart],"\n",Subscript[\[CapitalDelta], var],"=",Delta];
MapIndexed[Print["nor",2(First@#2-1),"=",#1]&,nnapart],];
res=MapIndexed[#1 Ffeyn[Delta,dim,Total[Last@#&/@denor],2(First[#2]-1)]&,nnapart];
If[OptionValue[ListForm],
Put[
{Drop[feyn,-1],MapIndexed[#1 Ffeyn[Delta,dim,Total[Last@#&/@denor],2(First[#2]-1),NoDelta->True]&,nnapart],{Sqrt[Delta],Total[Last/@denor]-dim/2-#}&/@(2(Range@Length@nnapart-1))},
LocalObject["OneLoop"]],
{res Times@@feyn[[2;;-2]],Sequence@@feyn[[1]]}]
(*{shift,Delta,newnor}*)
];


(* ::Code:: *)
(*Get@OneLoop[{{l-d,1},{l,m,1},{l-p,2}},m l^2+s+d l^4,l,d,ListForm->True]*)


(* ::Code:: *)
(*OneLoop[{{l-d,1},{l,m,1},{l-p,2}},m l^2+s+d l^4,l,d]*)


TwoLoop[denor1_,denor2_,nor_,var1_,var2_,dim_,opts:OptionsPattern[{DisplayTempResults->False,ListForm->False}]]:=
Module[{oneloop,res,denor},
oneloop=Get@OneLoop[denor1,nor,var1,dim,ListForm->True];
denor=Coefficient[First@#,var2^2]&/@Last[oneloop];
intgrate[res Times@@oneloop[[2;;-3]],Sequence@@oneloop[[1]]]
];


End[]


EndPackage[]
