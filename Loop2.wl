(* ::Package:: *)

BeginPackage["Loop2`"]


OneLoop::usage="OneLoop[denor,nor,k,exm,dim], \n i.e. OneLoop[{{k-p},{k,m^2}},k2,k,p,d]";
TwoLoop::usage="TwoLoop[denor1,denor2,nor,k1,k2,exm,dim], \n i.e. TwoLoop[{{k2-k1,1},{k2,2mE,1}},{{k1-p,1},{k1,2mE,2}},k1^4,k2,k1,p,d]";
NLoop::usage
LoopIntegrate::usage="LoopIntegrate[integrand,Assumptions->{}]";
FeynmanParameterize::usage="";
AlphaParameterize::usage="";
Ffeyn::usage="";
SP3::usage="";
ExpandSP;
EliminateVarProduct;
CheckDenorForm::usage="";
FeynmanParameterize::listQ="Variable \"`1`\" is not a list. ";
FeynmanParameterize::denor="Denorminator list is too short. ";
AlphaParameterize::listQ="Variable \"`1`\" is not a list. ";
GaussianIntegral::usage="GaussianIntegral[alpha,v,d] gives Gaussian integral Exp[i(\[Alpha]k^2-2v\[CenterDot]k)] in d dimension Euclidean space. ";
ShiftVar::usage;
ShiftVar::CTSIC="Complete the square operation results in incomplete square. ";
WithDiracDelta::usage="";
DisplayFeynPara::usage="";
DisplayTempResults::usage="";
DisplayOneLoop;
DisplayTwoLoop;
ExpandD::usage="";
ExpandDOrder::usage="";
ExpandDValue::usage="";
DivideNumerators::usage="";
DisplayNumerators;
ShowSecondLoopCommand::usage="";
$FeynParaVarList;
(*ScaleValue::usage="";*)
(*FeynmanParameterize::numer="The last line of the input list is not numbers, please add the power of denorminators. ";*)
Euclidean;
FeynParaVariable;
ExpForm;
ShiftAndIntegrate::usage="ShiftAndIntegrate[expr,var,d]";


Begin["Private`"]


(* ::Input:: *)
(*(Gamma[\[Beta]+d/2] Gamma[n-d/2-\[Beta]] (1/\[CapitalDelta])^(n-d/2-\[Beta]))/((4 \[Pi])^(d/2) Gamma[d/2] Gamma[n])*)


(* ::DisplayFormula:: *)
(*Integration: \[Integral]\[DifferentialD]^dk/(2\[Pi])^d k^(2\[Beta])/(k^2+\[CapitalDelta])^n*)


(*Unprotect[Dot];*)
CenterDot[o__]:=Dot[o];
SetAttributes[CenterDot,Orderless];
(*Dot[a_, Times[b_?(And @@ Map[Function[h, FreeQ[#, h]], Vector] &),
  c___]] := b Dot[a, c];*)

Ffeyn[\[CapitalDelta]_,d_,n_,\[Beta]_,OptionsPattern[{NoDelta->False,Euclidean->True}]]:=
If[OptionValue[NoDelta],(If[OptionValue[Euclidean],1,I (-1)^(n-\[Beta])])1/(4 \[Pi])^(d/2) Gamma[\[Beta]+d/2]/Gamma[d/2] Gamma[n-d/2-\[Beta]] / Gamma[n],(If[OptionValue[Euclidean],1,I (-1)^(n-\[Beta])])1/(4 \[Pi])^(d/2) Gamma[\[Beta]+d/2]/Gamma[d/2] Gamma[n-d/2-\[Beta]] / Gamma[n] (1/((If[OptionValue[Euclidean],1,-1])\[CapitalDelta](*/.\[CapitalDelta]/;(!OptionValue[Euclidean])->-\[CapitalDelta]*)))^(n-d/2-\[Beta])];


(*denor is either {k-l,1}=(k-l)^2 or {k,m^2,1}=k^2-m^2*)


FeynmanParameterize[denor_,OptionsPattern[{FeynParaVariable-> Global`x ,WithDiracDelta->False}]]:=Module[{xivars,measure,xipart,gammapart,integranddenor,explist},
If[ListQ@denor,Null,Message[FeynmanParameterize::listQ,denor];Abort[]];
explist=Last/@denor;
(*If[AllTrue[explist,NumberQ],,Message[FeynmanParameterize::numer]];*)
If[OptionValue[WithDiracDelta],
  xivars=OptionValue[FeynParaVariable][#]&/@Range@Length@denor;
  measure=({#,0,1}&/@xivars);
  xipart=DiracDelta[Plus@@xivars-1] Times@@MapThread[#1^(#2-1)&,{xivars,explist}];
  integranddenor=MapThread[Which[Length@#1>2,#2(#1[[1]]^2-#1[[2]]),Length@#1==2,#2 #1[[1]]^2]&,{denor,xivars}],

  xivars=OptionValue[FeynParaVariable][#]&/@Range@(Length@denor-1);
  measure=MapThread[{#1, 0, #2} &, {xivars,
    Drop[FoldList[#1 - #2 &, 1, xivars],-1]}];
  xipart=Times@@MapThread[#1^(#2-1)&,{xivars~Join~{1-Total@xivars},explist}];
  integranddenor=MapThread[Which[Length@#1>2,#2(#1[[1]]^2-#1[[2]]),Length@#1==2,#2 #1[[1]]^2]&,{denor,xivars~Join~{1-Total@xivars}}]
];
gammapart=Gamma[Plus@@explist]/Times@@Gamma/@explist;
If[AllTrue[integranddenor,!MatchQ[#,Null]&],Null,Message[FeynmanParameterize::denor];Abort[]];
Put[{measure,xipart,gammapart,integranddenor},LocalObject["FeynmanParametrization"]]
];


AlphaParameterize[denor_,OptionsPattern[{ParaVariable-> Global`\[Alpha]}]]:=Module[{explist, xivars, measure, coe, intg},
  If[ListQ@denor,Null,Message[AlphaParameterize::listQ,denor];Abort[]];
  explist=Last/@denor;
  xivars=OptionValue[ParaVariable][#]&/@Range@Length@denor;
  measure=({#,0,Infinity}&/@xivars);
  coe=Times@@MapThread[((-I)^#2)/Gamma[#2]#1^(#2-1)&,{xivars,explist}];
  intg=Times@@MapThread[Exp[I #1(If[Length@#2>2,#2[[1]]^2-#2[[2]],#2[[1]]^2])]&,{xivars,denor}];
  {coe, intg, measure}
];

GaussianIntegral[alpha_,v_,d_]:=(\[Pi]/alpha)^(d/2)Exp[-I v^2/alpha+I d \[Pi]/4];

CompleteTheSquare[expr_, Vars : {__Symbol}] := Module[{array, A, B, Cc, s, vars, sVars},
  vars = Intersection[Vars, Variables[expr]];
  Check[array = CoefficientArrays[expr, vars], Return[expr], CoefficientArrays::poly];
  If[Length[array] != 3, Message[CompleteTheSquare::notquad, vars]; Return[expr]];
  {Cc, B, A} = array; A = Symmetrize[A];
  s = Simplify[1/2 Inverse[A].B, Trig -> False];
  sVars = Hold /@ (vars + s); A = Map[Hold, A, {2}];
  Expand[A.sVars.sVars] + Simplify[Cc - s.A.s, Trig -> False] // ReleaseHold
];

ShiftVar[expr_,var_,opts:OptionsPattern[{ExpForm->True}]]:=Module[{exp, shift, newexp},
  exp=CompleteTheSquare[
    -I expr /. Power[E, o__] :> o, var];
  shift = {};
  exp/. (Power[o_?(ContainsAny[Variables[#], var] &),
    2] :> (AppendTo[
    shift, ({# // First,
      o - First@(Check[Length@# == 1, Abort,ShiftVar::CTSIC]; #)} &@
        Intersection[Variables[o], var])];));
  newexp=exp/. MapThread[#1 -> #1 - #2 &, {var, SortBy[shift, var][[All, 2]]}];
  If[OptionValue[ExpForm],Exp[I newexp],newexp]
];

ShiftAndIntegrate[expr_?(!MatchQ[(# /. Exp[o_] :> 1), 1]&),var_,d_,opts___]:=(expr/. Exp[_] :> 1)ShiftAndIntegrate[Cases[expr, Exp[__], Infinity] // First,var,d,opts]

ShiftAndIntegrate[expr_?(MatchQ[(# /. Exp[o_] :> 1), 1]&),var_,d_,opts:OptionsPattern[{Simplify->True}]]:=Module[{exp, tmp},
  exp=ShiftVar[expr,var,ExpForm->False];
  tmp=Fold[(
    ({#/.Exp[o_]:>1,Plus@@Cases[#, Power[E, o_] :> -I o, Infinity]//Simplify })&[#1[[1]]Exp[I Coefficient[#1[[2]],#2,0]]GaussianIntegral[Coefficient[#1[[2]],#2,2],-Coefficient[#1[[2]],#2,1]/2,d]]
  )&,{1,exp},var];
  tmp[[1]]Exp[I tmp[[2]]]//(Times/.Times/;OptionValue[Simplify]->Simplify[#,And @@ Thread[Variables[#] > 0]]&)
];

(*NLoopA[denor_,nor_,var_,d_];*)
(*Numerator forced to be 1*)

(*Up to k^4*)


AllPossiblePermutation[list_]:=DeleteDuplicates[Sort[Times@@(CenterDot@@#&/@Sort[Sort/@Partition[#,2]])&/@Permutations[list]]];


SP3[a_]:=a\[CenterDot]a;
SP3[a_,b_]:=a\[CenterDot]b;
ExpandSP[expr_,mem_]:=(expr//.CenterDot[o__,a___]:>Distribute[CenterDot[o,a]]//Expand)//. {CenterDot[Times[a__,
  b__?(Or @@ Map[Function[h, ! FreeQ[#, h]], mem] &)],
  o_] :> a CenterDot[b, o]}//.CenterDot[o_,o_]:>o^2;
EliminateVarProduct[expr_,var_,d_]:=
(expr//((#/.var->-var//.CenterDot[-a_,b_]:>(-CenterDot[a,b]))+(# //. CenterDot[-a_, b_] :> (-CenterDot[a, b]) ))/2&//Expand)/.CenterDot[p_,var]:>CenterDot[var,p]/.{Power[f_?(!MatchQ[#,Power[_,_?(!#!=1&)]]&&MatchQ[#,CenterDot[var,_]]&&!MatchQ[#,Power]&&!NumberQ[#]&),n_]:>Inactive[Times]@@ConstantArray[f,n]}/.Times[CenterDot[var,a_],CenterDot[var,b_]]:>Inactive[Times][CenterDot[var,a],CenterDot[var,b]]/.Times[CenterDot[var,a_] Inactive[Times][b__]]:>Inactive[Times][CenterDot[var,a],b]/.Inactive[Times][CenterDot[var,a1_],CenterDot[var,a2_],CenterDot[var,a3_],CenterDot[var,a4_],CenterDot[var,a5_],CenterDot[var,a6_]]:>var^6/(d(d+2)(d+4)) {a1\[CenterDot]a6 a2\[CenterDot]a5 a3\[CenterDot]a4,a1\[CenterDot]a5 a2\[CenterDot]a6 a3\[CenterDot]a4,a1\[CenterDot]a6 a2\[CenterDot]a4 a3\[CenterDot]a5,a1\[CenterDot]a4 a2\[CenterDot]a6 a3\[CenterDot]a5,a1\[CenterDot]a5 a2\[CenterDot]a4 a3\[CenterDot]a6,a1\[CenterDot]a4 a2\[CenterDot]a5 a3\[CenterDot]a6,a1\[CenterDot]a6 a2\[CenterDot]a3 a4\[CenterDot]a5,a1\[CenterDot]a3 a2\[CenterDot]a6 a4\[CenterDot]a5,a1\[CenterDot]a2 a3\[CenterDot]a6 a4\[CenterDot]a5,a1\[CenterDot]a5 a2\[CenterDot]a3 a4\[CenterDot]a6,a1\[CenterDot]a3 a2\[CenterDot]a5 a4\[CenterDot]a6,a1\[CenterDot]a2 a3\[CenterDot]a5 a4\[CenterDot]a6,a1\[CenterDot]a4 a2\[CenterDot]a3 a5\[CenterDot]a6,a1\[CenterDot]a3 a2\[CenterDot]a4 a5\[CenterDot]a6,a1\[CenterDot]a2 a3\[CenterDot]a4 a5\[CenterDot]a6}/.Inactive[Times][CenterDot[var,a1_],CenterDot[var,a2_],CenterDot[var,a3_],CenterDot[var,a4_]]:>var^4/(d(d+2)) (a1\[CenterDot]a2 a3\[CenterDot]a4+a1\[CenterDot]a3 a2\[CenterDot]a4+a1\[CenterDot]a4 a2\[CenterDot]a3)/.Inactive[Times][CenterDot[var,a1_],CenterDot[var,a2_]]:>1/d var^2 a1\[CenterDot]a2/.CenterDot[a_,a_]:>a^2;




CheckDenorForm[denor_,dim_]:=If[NumberQ@Last[#]||!FreeQ[#,dim],#,#~Join~{1}]&/@denor;


OneLoop[odenor_,nor_List,var_,exm_,dim_,rules:OptionsPattern[]]:=OneLoop[odenor,#,var,exm,dim,rules]&/@nor;


Options[OneLoop]={(*ScaleValue->1,*)DisplayFeynPara->False,DisplayTempResults->False,FirstLoop->False,SecondLoop->False,FeynParaVariable->Global`x,ExpandD->False,ExpandDOrder->-1,ExpandDValue->3,DisplayNumerators->False,FeynParaIN->{},DivideNumerators->False,WithDiracDelta->False,Euclidean->True};

OneLoop[odenor_,nor_?(!ListQ[#]&),var_,exm_,dim_,opts:OptionsPattern[{(*ScaleValue->1,*)DisplayFeynPara->False,DisplayTempResults->False,FirstLoop->False,SecondLoop->False,FeynParaVariable->Global`x,ExpandD->False,ExpandDOrder->-1,ExpandDValue->3,DisplayNumerators->False,FeynParaIN->{},DivideNumerators->False,WithDiracDelta->False,Euclidean->True}]]:=
Module[{denor, feyn, colist, shift, Delta, newnor, nnapart, res, int, feynpara, allfeynpara(*,sphere*)},
  (*Vector=DeleteDuplicates[Join[{var},exm,Vector]];*)
  (*If[OptionValue[Euclidean]\[Equal]False,SetOptions[OneLoop,ExpandDValue\[Rule]4],Null];*)
  If[OptionValue[SecondLoop],denor=odenor,denor=CheckDenorForm[odenor,dim]];
  denor=Flatten[(# //. {f___, {a_, d___, b_}, {a_, d___, c_},
    e___} :> {f, {a, d, b + c}, e}) & /@
      GatherBy[denor,
        Which[Length@# == 3, #[[1 ;; 2]], Length@# == 2, #[[1]]] &], 1];
  If[Length@denor<=1,Print["Denom number \[LessEqual] 1, scaleless integral. "];Abort[],Null];

  feyn=Get[FeynmanParameterize[denor,FilterRules[{opts},{FeynParaVariable,WithDiracDelta}]]];
  feynpara=If[OptionValue[WithDiracDelta],feyn[[1,All,1]],feyn[[1,All,1]]~Join~{1-Total[feyn[[1,All,1]]]}] ;(*Print[feynpara];*)
  allfeynpara=feynpara~Join~OptionValue[FeynParaIN];

  (*sphere=(2\[Pi]^(dim/2))/Gamma[dim/2];*)

  If[OptionValue[DisplayFeynPara],Print[feyn],Null];

  colist=FactorTerms[#,feynpara /. feynpara /; !OptionValue[WithDiracDelta] :> Drop[feynpara, -1]]&/@CoefficientList[Plus@@Last@feyn,var]//.{Total[feynpara]->1};
  If[Length[colist]<2,shift=0,shift=colist[[2]]/2];
  Delta=colist[[1]]-(shift)^2;
  If[OptionValue[DisplayTempResults],Print[colist,"\n",feynpara]];

  newnor=nor/.Power[a_?((!Or@@ (Map[Function[x, !FreeQ[#, x]], allfeynpara])) && (!MatchQ[#, CenterDot[_, __]]) &),n_?EvenQ]:>SP3[a]^(n/2)/.{var->var-shift};

  If[OptionValue[DisplayNumerators],Print["Numerators after SP3 substitution: ",newnor],Null];

  newnor=EliminateVarProduct[newnor//ExpandSP[#,exm~Join~{var}]&,var,dim]/.CenterDot[a_(c_?(Or@@(Map[Function[h,!FreeQ[#,h]],allfeynpara])&)),b_]:>c  CenterDot[a,b]/.CenterDot[b_,a_(c_?(Or@@(Map[Function[h,!FreeQ[#,h]],allfeynpara])&))]:>c  CenterDot[a,b]/.CenterDot[a_(c_?(Or@@(Map[Function[h,!FreeQ[#,h]],feynpara])&)),b_(d_?(Or@@(Map[Function[h,!FreeQ[#,h]],allfeynpara])&))]:>c d CenterDot[a,b]/.CenterDot[p_,p_]:>p^2;

  If[OptionValue[DisplayNumerators],Print["Numerators after eliminate power odd term: ",newnor],Null];
  (*Print[newnor];*)
  nnapart=DeleteCases[MapIndexed[#1 Boole[OddQ[First@#2]]&,CoefficientList[newnor,var]],_?(#==0&)];

  If[OptionValue[DisplayNumerators],Print["Numerators after division: ",nnapart],Null];
  (*Print[nnapart];*)
  If[OptionValue[DisplayTempResults],Print["integrand=",Plus@@MapIndexed[#1 Ffeyn[Subscript["\[CapitalDelta]", var],dim,Total[Last/@denor],2(First[#2]-1)]&,nnapart],"\n",Subscript["\[CapitalDelta]", var],"=",Delta];

  MapIndexed[Print["nor",2(First@#2-1),"=",#1]&,nnapart],Null];


  res=MapIndexed[#1 Ffeyn[Delta,dim,Total[Last/@denor],(First[#2]-1),FilterRules[{opts},{Euclidean}]]&,nnapart];


  (*a/.a/;!OptionValue[FirstLoop]->Print[res];*)

  Which[OptionValue[FirstLoop],
    {Drop[feyn,-1],(*sphere *)MapIndexed[#1 Ffeyn[Delta,dim,Total[Last@#&/@denor,FilterRules[{opts},{Euclidean}]],(First[#2]-1),NoDelta->True]&,nnapart],{Sqrt[Delta],Total[Last/@denor]-dim/2-#}&/@((Range@Length@nnapart-1))},
  OptionValue[SecondLoop],
    {Drop[feyn,-1],(*sphere *)MapIndexed[#1 Ffeyn[Delta,dim,Total[Last@#&/@denor,FilterRules[{opts},{Euclidean}]],(First[#2]-1)]&,nnapart]},
  True,
    {If[OptionValue[ExpandD],Normal@Series[#,{dim,OptionValue[ExpandDValue]/.{OptionValue[ExpandDValue]/;(!OptionValue[Euclidean]):>4},OptionValue[ExpandDOrder]}](*+If[!MatchQ[OptionValue[ScaleValue],1],Normal@Series[OptionValue[ScaleValue],{dim,OptionValue[ExpandDValue],OptionValue[ExpandDOrder]}](dim-OptionValue[ExpandDValue])Normal@Series[#,{dim,OptionValue[ExpandDValue],OptionValue[ExpandDOrder]}],0]*),(*OptionValue[ScaleValue]*) #]&[If[OptionValue[DivideNumerators],res Times@@feyn[[2;;-2]],Simplify[Total[res] Times@@feyn[[2;;-2]]]]],Sequence@@feyn[[1]]}]
  (*{shift,Delta,newnor}*)
];


(* ::Input::Initialization:: *)
(*Output form of ListForm is {{feynman parameters measure,DiracDelta and power of parameters,Gamma function in FeynmanPara},results with different power of numerators (without Delta part),Delta part ({Delta,dimension})*) 


(* ::Code:: *)
(* OneLoop[{{k1-p,1},{k1,2 m \[CapitalEpsilon],1},{Sqrt[k1^2-(2 m \[CapitalEpsilon] )/ x[1]],3-d/2}}, k1^4,k1,d,FeynParaVariable->y,SecondLoop->True,DisplayFeynPara->True,DisplayTempResults->True]*)


(* ::Code:: *)
(*Get@OneLoop[{{k2-k1,1},{k2,2 m \[CapitalEpsilon],1}},1,k2,d,FirstLoop->True]*)


(* ::Code:: *)
(*OneLoop[{{k2-k1,1},{k2,2 m \[CapitalEpsilon],1}},1,k2,d,DisplayFeynPara->True]*)


(* ::Input:: *)
(*m (p.(q x1))^2+2 m p^2 p.(p x3)/.CenterDot[a_(c_?(Or@@(Map[Function[x,!FreeQ[#,x]],{x1,x2,x3}])&)),b_(d_?(Or@@(Map[Function[x,!FreeQ[#,x]],{x1,x2,x3}])&))]:>c d CenterDot[a,b]*)


TwoLoop[denor1_,odenor2_,nor_,var1_,var2_,exm_,dim_,opts:OptionsPattern[{(*ScaleValue->1,*)DisplayOneLoop->False,DisplayTwoLoop->False,ExpandD->False,ExpandDOrder->-1,ExpandDValue->3,ShowSecondLoopCommand->False,DivideNumerators->False,DisplayNumerators->True}]]:=
Module[{feynpara1,oneloop,nor1,res,codenor,denor,denor2,twoloop},
  Vector=Union[{var1,var2},{exm}//Flatten];

  denor2=CheckDenorForm[odenor2,dim];

  If[FreeQ[denor1,var2],oneloop=OneLoop[denor1,nor,var1,exm~Join~{var2},dim];OneLoop[denor2,oneloop[[1]],var1,exm~Join~{var2},dim,FeynParaVariable->Global`y]~Join~oneloop[[2;;-1]],

  oneloop=OneLoop[denor1,nor,var1,exm~Join~{var2},dim,FirstLoop->True,FilterRules[{opts},{DisplayNumerators}]];

  feynpara1=oneloop[[1,1,All,1]];

  nor1=oneloop[[2]];
  codenor=ReplaceAll[(temprep/;OptionValue[WithDiracDelta]:>Total[feynpara1]):>1][Coefficient[(First@#)^2,var2^2]]&/@Last[oneloop];

  If[OptionValue[DisplayOneLoop],Print["oneloop=",oneloop,"\n Denorminator coefficient=",codenor],Null];

  denor=MapThread[Simplify[(First@#1)^2/#2]&,{Last[oneloop],codenor}];

  If[OptionValue[ShowSecondLoopCommand],MapThread[Print["OneLoop["<>StringTrim[ToString[InputForm@{denor2~Join~{{Simplify[Sqrt[#1],var2>0],#2}},#4/#3^#2,var2,exm,dim,FeynParaVariable->Global`y,SecondLoop->True,FeynParaIN->feynpara1}],"{"|"}"]<>"]"]&,{denor,Last[oneloop][[All,2]],codenor,nor1}],Null];

  twoloop=MapThread[OneLoop[denor2~Join~{{Simplify[Sqrt[#1],var2>0],#2}},#4/#3^#2,var2,exm,dim,FeynParaVariable->Global`y,SecondLoop->True,FeynParaIN->feynpara1,FilterRules[{opts},{DisplayNumerators(*,ScaleValue*)}]]&,{denor,Last[oneloop][[All,2]],codenor,nor1}];

  (*Print["oneloop=",oneloop,"\n codenor=",codenor,"\n denor=",denor];*)
  (*Print[nor1];*)

  If[OptionValue[DisplayTwoLoop],Print["twoloop=",twoloop],Null];

  (*{(If[OptionValue[ExpandD],Normal@Series[#,{dim,OptionValue[ExpandDValue],OptionValue[ExpandDOrder]}]+If[!MatchQ[OptionValue[ScaleValue],1], Print[Normal@Series[OptionValue[ScaleValue],{dim,OptionValue[ExpandDValue],OptionValue[ExpandDOrder]+2}]];Normal@Series[OptionValue[ScaleValue],{dim,OptionValue[ExpandDValue],OptionValue[ExpandDOrder]+2}] (dim-OptionValue[ExpandDValue]) Normal@Series[#,{dim,OptionValue[ExpandDValue],OptionValue[ExpandDOrder]}],0],OptionValue[ScaleValue] #])&[If[OptionValue[DivideNumerators],twoloop[[All,1]] Times@@oneloop[[1,2;;-1]],Times@@twoloop[[All,1]] Times@@oneloop[[1,2;;-1]]],Sequence@@oneloop[[1,1]]],Sequence@@twoloop[[1,2;;-1]]}*)

  {(If[OptionValue[ExpandD],Normal@Series[#,{dim,OptionValue[ExpandDValue],OptionValue[ExpandDOrder]}],#])&[If[OptionValue[DivideNumerators],Flatten[twoloop[[All,-1]] Times@@@twoloop[[All,1,2;;-1]]] Times@@oneloop[[1,2;;-1]],Plus@@(Flatten[twoloop[[All,-1]]Times@@@twoloop[[All,1,2;;-1]]]) Times@@oneloop[[1,2;;-1]]]],Sequence@@oneloop[[1,1]],Sequence@@twoloop[[1,1,1]]}]
];

$FeynParaVarList={Global`x,Global`y,Global`z,Global`r,Global`s,Global`t};

NLoop[denor_,nor_,var_,exm_,dim_,opts:OptionsPattern[{ExpandD->False,ExpandDOrder->-1,ExpandDValue->3}]]:=
    Module[{denorlist,collist,reslist},
      Vector=Union[var,{exm}//Flatten];

      denorlist=Reap[Fold[
        Complement[#1, Sow[Select[#1, Function[a, ! FreeQ[a, #2]]]]] &,
        denor, var]] // Flatten[#, 2] &  ;

      reslist=Reap[Fold[
        Function[tmpresult, Sow[tmpresult[[1, 1]], #2[[2]]];
        Print[#2[[2]], tmpresult[[1, 1]]]; tmpresult]@
            OneLoop[#2[[1]]~Join~#1[[-1]], #1[[2]]*
                Times @@ (#1[[1, 2 ;; 3]]), #2[[2]], exm, dim,
              FeynParaVariable -> #2[[3]], {FirstLoop ->
                True} /. {FirstLoop -> True} /; #2[[2]] == Last[var] ->
                Sequence[FirstLoop -> False,
                  FilterRules[{}, {ExpandD, ExpandDOrder,
                    ExpandDValue}]]] &, {{{}, 1, 1}, nor, {}},
        Transpose@{denorlist, var, Take[$FeynParaVarList, Length@var]}],
        var[[1 ;; -2]]];

      reslist[[1,1]]~Join~(reslist[[1,2;;-1]]~Join~(reslist[[-1]]// Flatten[#, 3] &))



    ];


LoopIntegrate[integrand_, asmp:OptionsPattern[{Assumptions->{}}]]:=Integrate@@(integrand~Join~FilterRules[{asmp},Options[Integrate]])
LoopIntegrate[integrand_, asmp_, opt:OptionsPattern[]]:=LoopIntegrate[integrand,Assumptions->asmp,opt]


(* ::Code:: *)
(*integrand=TwoLoop[{{k2-k1,1},{k2,2 m \[CapitalEpsilon],1}},{{k1-p,1},{k1,2m \[CapitalEpsilon],2}},k1^4,k2,k1,d]*)


(* ::Code:: *)
(*integrand[[1]]=(Series[integrand[[1]],{d,3,-1}]//Normal)/.\[CapitalEpsilon]->0*)


(* ::Code:: *)
(*Integrate@@integrand*)


End[]


EndPackage[]
