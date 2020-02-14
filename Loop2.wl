(* ::Package:: *)

BeginPackage["Loop2`"]


L2OneLoop::usage="L2OneLoop[denor,nor,k,exm,dim], \n i.e. L2OneLoop[{{k-p},{k,m^2}},k2,k,p,d]";
L2TwoLoop::usage="L2TwoLoop[denor1,denor2,nor,k1,k2,exm,dim], \n i.e. L2TwoLoop[{{k2-k1,1},{k2,2mE,1}},{{k1-p,1},{k1,2mE,2}},k1^4,k2,k1,p,d]";
NLoop::usage
L2LoopIntegrate::usage="L2LoopIntegrate[integrand,Assumptions->{}]";
FeynmanParameterize::usage="";
AlphaParameterize::usage="";
EikonalParameterize::usage="";
FPFormat;
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
DisplayL2OneLoop;
DisplayL2TwoLoop;
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


(*Auxiliary functions*)
ResSolve::usage="ResSolve[expr_(List|Expr),var,\[Epsilon]Value->\[Epsilon],Assumptions->$Assumptions,Plane->1]";
ResSolve::condfail="ResSolve returns empty list, possible non-sufficient conditions. ";
ResSolve::voidinput="Your input is an empty list, check again. ";
ResSolve::listinput="Your input is a list, ResSolve will process it individually, but you should check if it's what you want. ";
GatherCoefficients::usage="GatherCoefficients[expr,var_List]";
(*Dot functions*)
ExpandDot::usage="ExpandDot[expr,vec_List]";
RemoveDot::usage="RemoveDot[expr,l,D->d] | RemoveDot[expr,l,d]";
SortDot::usage="SortDot[expr]";
SphericalMeasurement::usage="SphericalMeasurement[l,D->d] | SphericalMeasurement[l,\[Theta],D->d], including $1/(2\[Pi])^d$";


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


GatherCoefficients[expr_,var_List]:=PadRight[Map[Times@@#&,GatherBy[List@@expr,And@@(Function[x,FreeQ[#,x]]/@var)&]],2,1]
GatherCoefficients[expr_,var: Except[_List]]:=GatherCoefficients[expr,{var}]


ExpandDot[expr_,vec_?(!ListQ@#&)]:=ExpandDot[expr,{vec}];
ExpandDot[expr_,vec_List]:=expr/. a_Dot:>Distribute[a,Plus]//. (a___).(d_ b_/;FreeQ[d,Alternatives@@vec]).(c___):>d a.b.c;

SortDot[expr_]:=expr/.Dot[a_,b_]:>Dot[Sequence@@Sort[{a,b}]];

OrderlessDelete[expr_]:=DeleteDuplicatesBy[expr,Sort[#]&];

PermutateDotProduct[dotvars_,4]:=SortDot[Plus@@Map[Times@@#&,OrderlessDelete[DeleteCases[Permutations[Map[Dot@@#&,OrderlessDelete[Permutations[dotvars,{2}]]],{2}],_?(Length[Variables[#/.Dot[a_,b_]:>{a,b}]]<4&)]]]];

(*RemoveDot[expr_,l_,d_?Symbol]:=RemoveDot[expr,l,D->d];*)
RemoveDot[expr_,l_,OptionsPattern[{D->Global`d}]]:=(Print["Dimension set at ", OptionValue[D]];Plus@@(Block[{dotlist=Cases[#,Dot[l,a_],{0,Infinity}],dotvars= Cases[# , Dot[l, a_] :> a, {0, Infinity}]},If[OddQ[Length@dotlist],0,Switch[Length@dotlist,0,#,2,1/OptionValue[D] l^2 Dot@@dotvars,4,1/(OptionValue[D](OptionValue[D]+2)) l^4 PermutateDotProduct[dotvars,4]]]]&/@List@@Expand[expr/. (a_).l:>l.a]));


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
{measure,xipart,gammapart,{integranddenor,Total[denor[[All,-1]]]}}
];


(* ::Code:: *)
(*Image[CompressedData["*)
(*1:eJztnQeQFMXbh1EUAwZQyzKhQqkoYoEEA5gFzAEQDIgKCogiCpizmANmUQFz*)
(*RDFhzmJExKwYMWPOOdIfT/+/vurr65npmZ2N9z5VA3d7O7uzOzPdb/i9b7ce*)
(*fHCfofM3adJkzMLz/ukz6IjNR48edFTfFvN+6TdyzPBhI4fst83IQ4cMGzJ6*)
(*g8FN5z3Ya97WdN7zF5j3vxIEQRAEQRAEQRAEQRAEQRAEQRAEQRAEQRAEQRAE*)
(*QRAEQRAEQRAEQRAEQRAEQRAEQRAEQRAEQRAEQRAEQRAEQRAEQRAEQRAEQRAE*)
(*QRAEQRAEQRAEQRAEQRAEQRAEQRAEQRAEQRCEMvPJJ5+oSy65pNyHIQiCIAhC*)
(*Gbj11lvV5Zdfrtq3b1/uQxEEoQC++eabch9C2fj666/L+v7//fdfqscFIQ/y*)
(*vr6+/PJLsQUEoQL4+eef1WeffRa7zZ07t8F+l112mXruuefKcMRKnXrqqapJ*)
(*kyZq4403VrvttluDbdddd1U77rij6t69u1piiSX0c9mGDBmS2zG89dZbaty4*)
(*cbm9Xig33HCDOuCAA9R2222n+vXrpz766CP9+P3336+OP/54deGFF+rjmjNn*)
(*TsmPTSgNTz/9tOrYsaO+phdccEHvPcDWv3//umt/gw02UG+88Yb39f7991/1*)
(*8MMP67Egiueff16deeaZ6q677lITJ06s97eZM2dm/ixiCwgu+FkjRoxQ06ZN*)
(*K/ehNCpeffVVdd5556nFFltMtWnTRo0fP15NmjRJP7bPPvuo+eefv26+MTzy*)
(*yCPq3HPPLdMRK/Xrr7+qtm3bqm7duulxLA7smOnTp6utt95aLbnkkuqPP/7I*)
(*7ThuuukmHecsBr/88ovaf//91ZVXXqnfB2bPnq3uvffeuudMmDBBLb/88jrf*)
(*eumll9bb/+qrry7KcQmVA/N7ixYtIv/OvYEdsNNOOyW+1s0336w6dOigrzsf*)
(*ffv2VVOnTlV//vmnuv766+v97Z133qn3O2P5+++/790+/fTTes8VW0Aw/PXX*)
(*X+rYY4/Vc1DLli3VPffcU+5DapSsv/76+n53Yc5/4okn6n7/+++/1ZZbbqn+*)
(*+eefXN8f+yINL730kmrWrJk67rjjgvc5//zz1eTJk9MeWizYGFHjZyFgB3Cs*)
(*Bx10kFprrbX0Y7fffnsD24dYwDLLLKO+/fbbeo8Xy0YRKgd8/xBb4JBDDgl6*)
(*vdVXX13n7308/vjjeoxYeuml1Z133qkfY+zmGrXHB7jvvvvUxRdf7N1cG1Vs*)
(*AcHHcsstJ7ZAmcDH2GWXXRo8zhxz1VVX1f2OX3ryySfn/v6Ma2khdkHcgnEq*)
(*FHzpPCFX4vpJhfLVV1+ppZZaSscwPv/8c/Xaa6/px2fNmqVmzJhR97zffvtN*)
(*5z3Y1ltvvTqbhFiIGycQao+8bYGTTjpJ591cuP9ffPFF/fOTTz6p7VN49tln*)
(*dd7h4IMPznD0/0NsAcGH2ALlI8oWgKeeeqru56FDh+rcoQu6AhMrIHbw8ccf*)
(*p3r/LLYAc962226rVlxxxQZ+cVbIP7gxzzjeffddbzylEC666CLVs2dP79/Q*)
(*C5CvJS9w2GGH6bGU7+Hss89WnTp1UiNHjtQxhQ8//DD1+6KBIA5c7WAz3X33*)
(*3eU+jKKTty1ADH+++eZrkBPErpwyZYrO36IZoA7QcMQRR6hXXnlFff/996mP*)
(*/6GHHlJHHXWUjmtxzb/55pupX0OoTcQWKB9xtoDNqquuqnOGNrfddpt69NFH*)
(*9WsQN0BfhO9wwQUXBL9/FlsAyE1y3aAVLJRzzjlHXXvttXpsY251x8QoWrVq*)
(*lWvOpEePHrGxF+IF2CwuaLyz2kTYP/iEP/zwQ6b9Kw20R1yHtUzetgBsuOGG*)
(*6rTTTmvwONf3jz/+2ODx3XffXcf9iWUJQl6ILVA+QmwB/H18cBfmUHxTtHlo*)
(*kID4AXZ/KFltAUADjT+Db5EV4vC2PbHJJptovbaBOEeUr0k+/4svvsj83jbM*)
(*8WjDsa1KBe/J+cefrhWYu7bZZpuarqcohi1w1lln1elTQsD+zFs7JAhiC5SP*)
(*EFuAcdU3ThBbxpcm1uerP7RhfKJOgTy7vXXp0qXBYw8++GDw8ROrXGihhfRx*)
(*ZAHNwSKLLKK1iM8884y2e2zwe+xcvc1GG22k6zHy4IEHHtB2jc8HKxYHHnig*)
(*rkW06dq1a109mtnQMKy00kqxm7sP36nJNZcaYs4hGvpqJW9bgNw/8bymTZtq*)
(*ba4glIvGaAv89NNPun6C2Bz3rL1xX1LXt+mmm2rNPGOxG5/PixBbgNz0mmuu*)
(*6f0b+YA+ffoEvRf+Ntpje9tiiy0aPIaNEQpzd7t27TLX0mHDEN9Ax8T4afRR*)
(*9t+joLYxr1wnNg167lLB+L/yyit7ay3JN9CrwczrJuYTx8ILL6yfS61jIXXn*)
(*eTF48GBdl1mL5GkLvP766zrej49Pbczo0aMbPId7y5ebEoS8aYy2ANAnBp8a*)
(*7U4UaPO4V0PG4yyE2AKMLb4cAfTu3buBb5mGQnIEgO0wfPjwTPuihTJ1UkBc*)
(*YNlll9U/M0dSr7Dnnnvqc+Bj7bXXzk27GKrbyAv6FcWdN/zDLLYAGsZKgDku*)
(*yn6tdvKyBciP2VoR9KmMxW79KjEryQcIpYD50B6TGxPk6fBr43p/cR/GreNR*)
(*SH9QYsI777xz4vPo8eMeIz4zdceFxMkLsQXQ+BELpt45C4yVth1BP5Q99thD*)
(*/4wWgV7L1FbT68eF77x169aJuZEQfv/9d60VGDt2bMGvFQJxnsUXX1y/bxRv*)
(*v/12JlvgyCOPzPNQC4K4Wi32MMvDFuCexVay/RBqVek9Zut98ri+BSGJM844*)
(*Q9eoNm/eXPexYSyM6pdZywwYMEDPaVnuO2qDb7nlFm0rpKknI15PryfyDyus*)
(*sIL+2e4n4HLooYfqGmMb5mL2LWS8yGoLMG5tv/32BWn3+Dz05iGvjfYczYDt*)
(*53MtbrbZZt59+Rt5nDxAs8DYXSp7mJwI91scpbAF6ItArTraTDdXEdIfNwnq*)
(*4IxtV0sUagtgO1MXZNcMG6hLNVoL4gHUFVaSfScI1Qj9Yg4//HCdCyb/GtWb*)
(*hnGwc+fOupdcGoiDopkm1s3cbtsCjOV55viIn48aNarB41nqi22y2gLMw75+*)
(*B1Fcd911kX/j+8O2cBkzZow+Z7781emnn57b3G3WWcjSGyAL2FC8ZxylsAWI*)
(*T2D/sx8/uyT1x03i5Zdf1utS1Jpvm0dcIKqGFDvB6HVuvPFG3Utw7733Luh4*)
(*BaExQ/x10KBBdbk3/Fd0VeQEfBCf5u9pevIyxu277756v80337xenu+9997L*)
(*dQzktZhD4uLKWUijEzQQT0qjFURDlqUfHz190Ay4fX35nul1lLQmQiisN1TK*)
(*OYu8TtL6UqXKEZBribIFIK4/bhJ8n8Qcs1xjlUwxagqjQMPi9hoWBCEc+vAw*)
(*P9t+M/EBYvI+sNMHDhwY7MvjK9G7CxjzevXqVbeeLrHVYmgN0RrxGcoJekuf*)
(*1tnHd999p+vmqDnMutaw73wQEyBOkhfMzfQ1KAXM8fRvdmsnfc8rlV4gzhaI*)
(*6o8bCnEF+kjVEjvssIP+vqNsUWqU8lifk/sHfSwxs1L2vRCEWoIaeTS5dt9O*)
(*8rTco+78Qr0gMYQ0PbyoQyeHT24Av/WKK67QjzOmkjvIox+fD/oLEjcsB8Q6*)
(*+E6J3TPnuBt2CnkM8gfMH9S4831TK5UXfN9m/cA8QLvlq2UsFqxzRD+AJIpt*)
(*C6A1Mdd7nC0Q1R83FPzaUNux0iF2yJphxDrMNfPCCy/Uew4aGGL6/B1NNjqi*)
(*rLUuxDKJWTFu1UpfSkGoBIjtrbvuuvUeI0bKuvT0t4/Dp/MB4g5uHQG+M2vz*)
(*YdcXg7xi42kh1kv+Pu2GbZQXeX92crKM28aWKza8D+sZJVEsW4DcBHWa2JT4*)
(*mlyncbYARPXHDYEax7322ivTvpUG9pB7bbu5HnSo7nMK6RNMTrCQOiVBqGbQ*)
(*lDNvJ23U/UfVnrvQk4ZeveimbY4++mg1ffr02H3JNyRpvWzQT9OX130vofIg*)
(*p8tcWKoefay3QH+nJIphC+DX0r+BWk0DeskkWyCuP25SHxzur2LFyASh1kFr*)
(*VW0b9XBptlKCNtes32PDuEyc3+2799hjj2ntOut+owPIEiON6lOIX1jrWzmv*)
(*sbSQy1hggQWK1lfSBY0Jcd8kimELnHDCCVpDY8M8HmcLJPXHTeqDgw3t02JQ*)
(*g3LNNdfIlrBha+WxpR2f47Y87uW8xppa54MPPqj5rVSg6yMH4NbmE2smD4cm*)
(*PmmbMGFCbsdT7u+91re01wY9f9ZZZ53czm8S1EaUyxYglub2VoyzBZL6484N*)
(*qLtg3UfWjXAhHhG6lfuakq1yN6G2Cc0R0MckKUeA5tzuy0dfoKx98oTagvWC*)
(*mQfJn5cKdPmub+6jGLYAvZzc/ESULZDUHze0Dw45GMkRCELjpFK0Luii0PES*)
(*90fTQ63fsGHDyn1YmbHzvHFkrd8rJVwjhWgr8/iMzLHMg6zvVCrQoZdLO8j6*)
(*z2jb7e8dHTz72fU2If1xQ/vgoBuUXjmNB+JA9POmlthe743+tvRU7Nu3r+65*)
(*yDVHjlYoHdS+4YeQ7+P732qrrSL9bMYJnkN/kSx1W8xV9O6jbor4eznX06Cm*)
(*kDy/u5ZrSHy2mNDTlVhG3DbXE3tlLeGk/jQG9P7jxo2LfQ42Euvk8Z2w7lHU*)
(*NUEPYJ5Dj4CePXs2eB3Oedxn8WmosQPQaRRiC4R8xiTQtfHZ3LqwYjJ58mT9*)
(*vSdRrDoCcmXE0/DruU9NHQFjNDZAaH9cCOmDw/2WR88dobKI8vfom4E+JG6N*)
(*LMY3rr3u3bsX6/AaHfackeSLU/vNPR+3zjx5PfquZJ3D0c7TV5+4IraEXf+V*)
(*d0/eaoXxll56+Fht2rRR48ePV5MmTdKPUZdPHxpXp0gvRPzJNPD9u/36XLBL*)
(*sOHj1kbivbluOD4f1E+SA+c52ApoKyZOnKhzM/zOvOKC7xBq18QR8hnjoGcM*)
(*PRCS+v7kCfUsnOMkrWKx+wsQI6D3NuMG9bTUxprxJKQ/bmgfHDS72LFCbcE9*)
(*HwUxu1VWWSVR28fYQZ5OKAzuXWIs2OboMtGcYrdHwf0YYgt07Ngx8zHhB6Ix*)
(*orcfPpdN3j15qx3W38MXc2HOt30t5inWsclin3EuknrJkwMOsQXiev8zp/Ac*)
(*bEGXPn361Dt2roM8681DPmMU2Cml6jdo4Hxif2ETxFHp6xSG9MHBF0CbWcg6*)
(*mkJpCfUvk2I9rEXRsmXLguqqKyXXXOmQq8MmZ506+lrxs73WpUuxbQHqs01N*)
(*Fz047b6lxerJW83gL7mabuBc2rVx1EHiR2eBcx61HpMhD1sAH5fnUIPpMmXK*)
(*lHpr/uBPRPVtykLIZ/RBTKRca/wSG8V+j6PSbQFI6oND3w5sgdAxnXFDdL3F*)
(*J0prk8a/DMn7oNNmrZbQHjAG6k3p0YKGnBijATulVH1AKhXsbl/ND7W/PXr0*)
(*CHqNvG0Bjske47H/yN/SJ544MTX6UOyevNVKlC0A9lw5dOhQ73qA3Lf2erKz*)
(*Z89uEHch9uuLPdgU2xZgHLCvk06dOsX2DmScsnVsSYR8Rh9crxwz402pId9C*)
(*rV4c1WALJEE9LvqkEDjvrClaDbFDs64l/o5PY8OaqIx32HyseWXOY6HrE/hg*)
(*fGXMTdOPM0prE+df8jtaUrORz7R/j9I1H3PMManXs+B+njp1qh5XbDsfm9LW*)
(*szYmiL2ieyfvgn9ITZB9rzP2nnLKKUGvlZctQE0na/ORq2XOokbKxtd7u9g9*)
(*eauROFvAhji2m1vmXma9F9ZLZu151gPm/DIGubRq1So2v1BsW8CG/EBUTJ5r*)
(*nXUOuFZmzpypNaih80LSZ/TB2nscczlqLrB16P8XN34bfT8bepI4+P7RIPBc*)
(*9NuVAn26QjTInGfyRuUeH0LXOEf31LZtW9WtW7fEOZjPRnyEXBZ9T7nO84T3*)
(*55wPHjw41X5RWpso/xJNCPe32dAU279HxaTxC6k5SQM1X+RQ0a6ZcQefglhF*)
(*1nUxqh3WZbVjif369dPXqoHzn9Q/15CHLcA8jwbazv+F2LrSk7chIbYAuWU0*)
(*/i7Y9HP/fw1jE8NDg+hbj5neseR2oyilLUCuCA27D64P46uQ/+e4QsfNpM/o*)
(*Y8SIEWq11VZLtU+ecG9TU+DC2I6eirnD2AJo9LAN3Pg518CcOXN0Ly3zXHK0*)
(*1AjkvbZ1WojXYO+E9HPEri2GvjDN+uNp1zinB2OzZs20fxYK/pDvnBcKtiW2*)
(*ILGkNPi0NqH+ZUiOAD8lSnMcBflRkweg5sWsGYYtgk9M/UFjg89MrMbOtdEf*)
(*jVo5Qxr9cx62ADEK/Dri0awXxxxPr/4QStXjtVoIsQUY53194GfNmqXnATSa*)
(*9ISJg3Map90qpS1Av5rhw4d7/0Z/XGIgjJfMI+61je6dscVH0meM2of4Vrng*)
(*eFnzx4V4KufEtzE32fYAdmDUc9l8PYNLBT0FouZRF7SxxagxIl4fSto1zoF5*)
(*jjkYPzaUPHuY2nDsaewS8GltQv3LJFuA13D14y6sj+H6+fSvQmM0bdo0Pb/Y*)
(*+ULqfvBHy1mrXg7IJ2KnGsjHYIdmvWfysAXoP8L1Rj2Y1AUURogtQC6Q79wH*)
(*cwn9IJLOAXHMOM16KW0B8t5RWiT6YOADMN/RC8P1n+hTMGPGDO++SZ/RBd9v*)
(*0UUX1baJDX4I8Uzip6Xwq4mLl2v96WJCHnGNNdYIsv+J/RIjiYMccRZNeRpb*)
(*IM0a5wbuPY6d2F3WdYld+M7w79OOrfjMrVu3TrWPT2sT6l/G2QK8LrGquHNG*)
(*PIK4hO8+Y65nPLDBBu7du7fO7TU2OnTooOO+Bmwl5g9IGwuCPGwBauJ9OjYb*)
(*NINpxuXGSogtwJzlyxEAvfKo10uC+HLcOFVKWwD/yaeZw7Y0/X4YA+lN0L9/*)
(*/3rPiRsbkz6jC3YUx0vcxcD7m5ppHvdpL/IGW4/YAPr5WoFxnHwzccMQ0Imj*)
(*DfHBWELsBh8RfTvXTpp8cRpbIGp/d41zF/Qm3EOFaqOZG8n/Yn+gl+FaRLsX*)
(*CnMn+tG0edgsWhvAF/TBNU1sizyVvd6b6fuKnU28BS1AWo1DY60x4dqipgOY*)
(*E9DjsjYI2vEs67HlYQvQyxxtlw12mp2rJdeDBkeIp2vXrrFzsAGNkl0vYMAO*)
(*SOqdi12OrxA3j+ZhCzBm8Rzi+3HgA/r67zIfmmsd0EIa+x/NALFY1gzw1SaF*)
(*fEYX4rTude720EP3VgqblrGbOSeNDrySIbaTZBPaoDP3xc2xJfCHzHzIuWA9*)
(*yTR2UyG2QNQa5z6Y4+hx6uuvEYKJL9j78x3aYzXzdZKmgtfAH3eJ2zeL1iYO*)
(*zlvIem9s5DqFZMj1obPCnsJPQj9ATJFx0c5phZKHLUBueuDAgbqGhTV96WNr*)
(*n0/JGSTDvUJvRvKQ6EH4Oc62o1evu8Yi0LMw6V5CE0ztTxyF2gLE2al7bN68*)
(*uercubOuKzH1pD64xtw4JK/BeIo/hB2AD2jmRh4nP4auGJ1Kls/own3FWGSD*)
(*jpDaVwNxAWJxpQC/N0uPhEqD78+OZYaA9tjNBzGOYAfY8xf5fJ++woCWhOfb*)
(*W5cuXRo8xvq9SUStcR4Hvi59uuPG1yjwlak9pD6IcR872NVacD+4fpj7GozN*)
(*+Nvu/RW3bxatjVB68ImozTZzLHGgNHEjm7xqCrmuyN+5eR5iRrwHtQ5CfmB3*)
(*jRo1qsHjIfYgNmScPw95xAXSQG22r6Yf/548s88/Zr6nhslHyGe0YZzHDrN7*)
(*HgB2GXlOA7ZAUi2fUDjoR9z+CWb9SPSiBuo+4rRo2CF2TJqNOKb7WFLv67kR*)
(*a5wnwfzbrl27IFvDhe+AmiDudT6HL2cf52dhS48dO1bn6lq0aKFr80P3Tau1*)
(*EaqfYvcdRHPF/IRmSMgPUzuYVsvGnErMMCn2XGpbAA1g2tgtfQfwm4lF2YR+*)
(*RrTJJjfB6/i0APihthYGXVNen1mIhvoRVw92xx136HpEm/bt2+scNNq+UH8o*)
(*S44g6xrn2BlRNTJJcH+jmY+CunL6yvhsaK7nAQMG1P1OnMXW2sTtC2m1NkL1*)
(*Q+02Yzq2ZxToZFijMCvkuE488cTM+wt+yM0Qg0wDY1rcuQbsDGKTvvUHDYwh*)
(*XDeu5r4Q0DynWVMIHRW5MXefkM8I+J2Ml/RIp37N118IXTRzkAF/ybfGopAv*)
(*XFfuOjfEyW1NPD46+Xh0M+TUQ2sK0toCWdc4R8/I+o1ZtW349O79TZ6Nz40W*)
(*j5/RFbq5RPoy4L/ZfTjIN6EhRFcRty9k0doI1QtxI2xD/HXGdDRRbgyJ2Cj9*)
(*Jcy6xtjqWXQd5Oew213/TSgccpeh9WdoEpL6vZGbJ/fA+WatPvTLbu9f5lBy*)
(*tDwHLQC5/LzANvXl/6Nw67pCPqMNn43vMMqnJKZFDS92F6+bNu8tZINe5r4+*)
(*xdQP4JPj96InYB0k4jTMf6GkrSnMssY51xN+fSH6O+ZtYlXEPbBBiOFihxjQ*)
(*/uGj2X2BsJfQuLj2KvM6uQrT48e3ryGL1kaoXrAZuZ/szY19Mu+7z0nqYeOD*)
(*WiLsz1KuB9+YCNWahzyPeLh7zsnX22ALuM/Jk0K088XS3WOflLtnX2ODudQX*)
(*q6EXjV1Dk3a+LbSmMATm0qQ6a5s4exp71acDQhe533776dyFsdfx6X31RYB9*)
(*ZZ7n29eQVmsjCKFwfebdb1sQhNoGnzwuX54VdPnFhFqUNFpB4rNoV9JCHBft*)
(*ZFLNbpp9Q7U2giAIglAqmK/S5IzKDTV69HsJgTWXWD+ImsOsa2EV0qPZt2+o*)
(*1kYQBEEQSgXxRPoOVcO6JdRPU39DfQsafXdDB4gWh/wBPfjQ46A9oDalEkir*)
(*tREEQRCEUkGOsRo07eQeXB1NyGb3sionkhcQBEEQBEEQBEEQBEEQBEEQBEEQ*)
(*BEEQBEEQBEEQBEEQBEEQBEEQBEEQBEEQBEEQBEFI5v8AVKrucw==*)
(*"], "Byte", ColorSpace -> "RGB", Interleaving -> True]*)


EikonalParameterize[quadpro_List,eikpro_List,OptionsPattern[{FPFormat->False, EikParaVariable->Global`\[Lambda]}]]:=Module[{qexp,qexplist,explist,feynmeasure,feynxipart,feyngammapart,feynintg,measure,xipart,gammapart,integranddenor,xivars},
	{feynmeasure,feynxipart,feyngammapart,{feynintg,qexp}}=If[OptionValue[FPFormat],quadpro,{{},1,1,quadpro}];
	explist=Last/@eikpro;
	qexplist={qexp};
	xivars=OptionValue[EikParaVariable][#]&/@Range@Length@eikpro;
	measure=({#,0,\[Infinity]}&/@xivars);
	xipart=Times@@MapThread[#1^(#2-1)&,{xivars,explist}];
	gammapart=2^Total@explist Gamma[Plus@@(Join[explist,qexplist])]/((Times@@Gamma/@explist)(Times@@Gamma/@qexplist));
	integranddenor={{Total[feynintg]+2Plus@@MapThread[#1 #2&,{eikpro[[All,1]],xivars}]},Plus@@(Join[explist,qexplist])};
	{feynmeasure~Join~measure,feynxipart xipart, feyngammapart gammapart, integranddenor}
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


GaussianIntegral[alpha_,v_,d_]:=(2\[Pi])^(-d)(\[Pi]/alpha)^(d/2)Exp[-I v^2/alpha+I d \[Pi]/4];

L2CompleteTheSquare[expr_?(Length[#]==1&), Vars : {__Symbol}] :=L2CompleteTheSquare[expr[[1]],Vars];
L2CompleteTheSquare[expr_?(!ListQ[#]&), Vars : {__Symbol}] := Module[{array, A, B, Cc, s, vars, sVars},
  vars = Intersection[Vars, Variables[expr]];
  Check[array = CoefficientArrays[expr, vars], Return[expr], CoefficientArrays::poly];
  If[Length[array] != 3, Message[L2CompleteTheSquare::notquad, vars]; Return[expr]];
  {Cc, B, A} = array; A = Symmetrize[A];
  s = Simplify[1/2 Inverse[A].B, Trig -> False];
  sVars = Hold /@ (vars + s); A = Map[Hold, A, {2}];
  Expand[A.sVars.sVars] + Simplify[Cc - s.A.s, Trig -> False] // ReleaseHold
];

ShiftVar[expr_,var_,opts:OptionsPattern[{ExpForm->True}]]:=Module[{exp, shift, newexp},
  exp=L2CompleteTheSquare[
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


L2OneLoop[odenor_,nor_List,var_,exm_,dim_,rules:OptionsPattern[]]:=L2OneLoop[odenor,#,var,exm,dim,rules]&/@nor;


Options[L2OneLoop]={(*ScaleValue->1,*)DisplayFeynPara->False,DisplayTempResults->False,FirstLoop->False,SecondLoop->False,FeynParaVariable->Global`x,ExpandD->False,ExpandDOrder->-1,ExpandDValue->3,DisplayNumerators->False,FeynParaIN->{},DivideNumerators->False,WithDiracDelta->False,Euclidean->True};

L2OneLoop[odenor_,nor_?(!ListQ[#]&),var_,exm_,dim_,opts:OptionsPattern[{(*ScaleValue->1,*)DisplayFeynPara->False,DisplayTempResults->False,FirstLoop->False,SecondLoop->False,FeynParaVariable->Global`x,ExpandD->False,ExpandDOrder->-1,ExpandDValue->3,DisplayNumerators->False,FeynParaIN->{},DivideNumerators->False,WithDiracDelta->False,Euclidean->True}]]:=
Module[{denor, feyn, colist, shift, Delta, newnor, nnapart, res, int, feynpara, allfeynpara(*,sphere*)},
  (*Vector=DeleteDuplicates[Join[{var},exm,Vector]];*)
  (*If[OptionValue[Euclidean]\[Equal]False,SetOptions[L2OneLoop,ExpandDValue\[Rule]4],Null];*)
  If[OptionValue[SecondLoop],denor=odenor,denor=CheckDenorForm[odenor,dim]];
  denor=Flatten[(# //. {f___, {a_, d___, b_}, {a_, d___, c_},
    e___} :> {f, {a, d, b + c}, e}) & /@
      GatherBy[denor,
        Which[Length@# == 3, #[[1 ;; 2]], Length@# == 2, #[[1]]] &], 1];
  If[Length@denor<=1,Print["Denom number \[LessEqual] 1, scaleless integral. "];Abort[],Null];

  feyn=FeynmanParameterize[denor,FilterRules[{opts},{FeynParaVariable,WithDiracDelta}]];
  feynpara=If[OptionValue[WithDiracDelta],feyn[[1,All,1]],feyn[[1,All,1]]~Join~{1-Total[feyn[[1,All,1]]]}] ;(*Print[feynpara];*)
  allfeynpara=feynpara~Join~OptionValue[FeynParaIN];

  (*sphere=(2\[Pi]^(dim/2))/Gamma[dim/2];*)

  If[OptionValue[DisplayFeynPara],Print[feyn],Null];

  colist=FactorTerms[#,feynpara /. feynpara /; !OptionValue[WithDiracDelta] :> Drop[feynpara, -1]]&/@CoefficientList[Plus@@First@Last@feyn,var]//.{Total[feynpara]->1};
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
(* L2OneLoop[{{k1-p,1},{k1,2 m \[CapitalEpsilon],1},{Sqrt[k1^2-(2 m \[CapitalEpsilon] )/ x[1]],3-d/2}}, k1^4,k1,d,FeynParaVariable->y,SecondLoop->True,DisplayFeynPara->True,DisplayTempResults->True]*)


(* ::Code:: *)
(*Get@L2OneLoop[{{k2-k1,1},{k2,2 m \[CapitalEpsilon],1}},1,k2,d,FirstLoop->True]*)


(* ::Code:: *)
(*L2OneLoop[{{k2-k1,1},{k2,2 m \[CapitalEpsilon],1}},1,k2,d,DisplayFeynPara->True]*)


(* ::Input:: *)
(*m (p.(q x1))^2+2 m p^2 p.(p x3)/.CenterDot[a_(c_?(Or@@(Map[Function[x,!FreeQ[#,x]],{x1,x2,x3}])&)),b_(d_?(Or@@(Map[Function[x,!FreeQ[#,x]],{x1,x2,x3}])&))]:>c d CenterDot[a,b]*)


L2TwoLoop[denor1_,odenor2_,nor_,var1_,var2_,exm_,dim_,opts:OptionsPattern[{(*ScaleValue->1,*)DisplayL2OneLoop->False,DisplayL2TwoLoop->False,ExpandD->False,ExpandDOrder->-1,ExpandDValue->3,ShowSecondLoopCommand->False,DivideNumerators->False,DisplayNumerators->True}]]:=
Module[{feynpara1,L2OneLoop,nor1,res,codenor,denor,denor2,L2TwoLoop},
  Vector=Union[{var1,var2},{exm}//Flatten];

  denor2=CheckDenorForm[odenor2,dim];

  If[FreeQ[denor1,var2],L2OneLoop=L2OneLoop[denor1,nor,var1,exm~Join~{var2},dim];L2OneLoop[denor2,L2OneLoop[[1]],var1,exm~Join~{var2},dim,FeynParaVariable->Global`y]~Join~L2OneLoop[[2;;-1]],

  L2OneLoop=L2OneLoop[denor1,nor,var1,exm~Join~{var2},dim,FirstLoop->True,FilterRules[{opts},{DisplayNumerators}]];

  feynpara1=L2OneLoop[[1,1,All,1]];

  nor1=L2OneLoop[[2]];
  codenor=ReplaceAll[(temprep/;OptionValue[WithDiracDelta]:>Total[feynpara1]):>1][Coefficient[(First@#)^2,var2^2]]&/@Last[L2OneLoop];

  If[OptionValue[DisplayL2OneLoop],Print["L2OneLoop=",L2OneLoop,"\n Denorminator coefficient=",codenor],Null];

  denor=MapThread[Simplify[(First@#1)^2/#2]&,{Last[L2OneLoop],codenor}];

  If[OptionValue[ShowSecondLoopCommand],MapThread[Print["L2OneLoop["<>StringTrim[ToString[InputForm@{denor2~Join~{{Simplify[Sqrt[#1],var2>0],#2}},#4/#3^#2,var2,exm,dim,FeynParaVariable->Global`y,SecondLoop->True,FeynParaIN->feynpara1}],"{"|"}"]<>"]"]&,{denor,Last[L2OneLoop][[All,2]],codenor,nor1}],Null];

  L2TwoLoop=MapThread[L2OneLoop[denor2~Join~{{Simplify[Sqrt[#1],var2>0],#2}},#4/#3^#2,var2,exm,dim,FeynParaVariable->Global`y,SecondLoop->True,FeynParaIN->feynpara1,FilterRules[{opts},{DisplayNumerators(*,ScaleValue*)}]]&,{denor,Last[L2OneLoop][[All,2]],codenor,nor1}];

  (*Print["L2OneLoop=",L2OneLoop,"\n codenor=",codenor,"\n denor=",denor];*)
  (*Print[nor1];*)

  If[OptionValue[DisplayL2TwoLoop],Print["L2TwoLoop=",L2TwoLoop],Null];

  (*{(If[OptionValue[ExpandD],Normal@Series[#,{dim,OptionValue[ExpandDValue],OptionValue[ExpandDOrder]}]+If[!MatchQ[OptionValue[ScaleValue],1], Print[Normal@Series[OptionValue[ScaleValue],{dim,OptionValue[ExpandDValue],OptionValue[ExpandDOrder]+2}]];Normal@Series[OptionValue[ScaleValue],{dim,OptionValue[ExpandDValue],OptionValue[ExpandDOrder]+2}] (dim-OptionValue[ExpandDValue]) Normal@Series[#,{dim,OptionValue[ExpandDValue],OptionValue[ExpandDOrder]}],0],OptionValue[ScaleValue] #])&[If[OptionValue[DivideNumerators],L2TwoLoop[[All,1]] Times@@L2OneLoop[[1,2;;-1]],Times@@L2TwoLoop[[All,1]] Times@@L2OneLoop[[1,2;;-1]]],Sequence@@L2OneLoop[[1,1]]],Sequence@@L2TwoLoop[[1,2;;-1]]}*)

  {(If[OptionValue[ExpandD],Normal@Series[#,{dim,OptionValue[ExpandDValue],OptionValue[ExpandDOrder]}],#])&[If[OptionValue[DivideNumerators],Flatten[L2TwoLoop[[All,-1]] Times@@@L2TwoLoop[[All,1,2;;-1]]] Times@@L2OneLoop[[1,2;;-1]],Plus@@(Flatten[L2TwoLoop[[All,-1]]Times@@@L2TwoLoop[[All,1,2;;-1]]]) Times@@L2OneLoop[[1,2;;-1]]]],Sequence@@L2OneLoop[[1,1]],Sequence@@L2TwoLoop[[1,1,1]]}]
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
            L2OneLoop[#2[[1]]~Join~#1[[-1]], #1[[2]]*
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


ResSolve[Int_List,l0_,opt___]:=Which[Length[Int]==1,ResSolve[Int[[1]],l0,opt],Length[Int]==0,Message[ResSolve::voidinput],Length[Int]>1,Message[ResSolve::listinput];ResSolve[#,l0,opt]&/@Int];
ResSolve[bIntgV_?(!ListQ[Head[#]]&),l0_,s:OptionsPattern[{\[Epsilon]Value->Global`\[Epsilon],Assumptions->($Assumptions),Plane->1}]]:=
	If[#=={},Message[ResSolve::condfail],#]&@MapAt[OptionValue[Plane] #&,Map[(2\[Pi] I Residue[bIntgV,{l0,l0/.#}]&),
		Select[#,I==Assuming[OptionValue[\[Epsilon]Value]>0&&OptionValue[Assumptions],
		-I OptionValue[Plane] Simplify@Sign[I SeriesCoefficient[l0/.#,{OptionValue[\[Epsilon]Value],0,1}]]]&]&@DeleteDuplicates[Solve[Denominator[bIntgV]==0,l0]]],
		{All,2}];


SphericalMeasurement[l_,OptionsPattern[{D->Global`d}]]:=Module[{d=OptionValue[D]},(((l^(d-1) ) (2 \[Pi]^(d/2)))/((2 \[Pi])^d Gamma[d/2]))]
SphericalMeasurement[l_,\[Theta]_,OptionsPattern[{D->Global`d}]]:=Module[{d=OptionValue[D]},(((l^(d-1) Sin[\[Theta]]^(d-2)) (2 \[Pi]^((d-1)/2)))/((2 \[Pi])^d Gamma[(d-1)/2]))]


L2LoopIntegrate[integrand_, asmp:OptionsPattern[{Assumptions->{}}]]:=Integrate@@(integrand~Join~FilterRules[{asmp},Options[Integrate]])
L2LoopIntegrate[integrand_, asmp_, opt:OptionsPattern[]]:=L2LoopIntegrate[integrand,Assumptions->asmp,opt]


(* ::Code:: *)
(*integrand=L2TwoLoop[{{k2-k1,1},{k2,2 m \[CapitalEpsilon],1}},{{k1-p,1},{k1,2m \[CapitalEpsilon],2}},k1^4,k2,k1,d]*)


(* ::Code:: *)
(*integrand[[1]]=(Series[integrand[[1]],{d,3,-1}]//Normal)/.\[CapitalEpsilon]->0*)


(* ::Code:: *)
(*Integrate@@integrand*)


End[]


EndPackage[]
