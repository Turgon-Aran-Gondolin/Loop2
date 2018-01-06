#!/usr/bin/env wolframscript
(* ::Package:: *)

<<Loop2`


??Loop2`*


(* ::PageBreak:: *)
(**)


TwoLoop[{{k2-k1,1},{k2,2 m \[CapitalEpsilon],1}},{{k1-p,1},{k1,2m \[CapitalEpsilon],2}},k1^4,k2,k1,{p},d,ExpandD->True,DisplayOneLoop->True,DisplayTwoLoop->True,ShowSecondLoopCommand->True,DivideNumerators->True]


Integrate@@%


TwoLoop[{{k1-p,1},{k1,2m \[CapitalEpsilon],2},{k2-k1,1}},{{k2,2 m \[CapitalEpsilon],1}},k1^4,k1,k2,{p},d,ExpandD->True,DisplayOneLoop->True,DisplayTwoLoop->True,ShowSecondLoopCommand->True,DivideNumerators->True]


Integrate@@%


(* ::PageBreak:: *)
(**)


TwoLoop[{{k2-k1,1},{k2,2 m \[CapitalEpsilon],2}},{{k1-p,1},{k1,2m \[CapitalEpsilon],1}},k2^4,k2,k1,{p},d,ExpandD->True,DivideNumerators->True,ShowSecondLoopCommand->True,DisplayOneLoop->True,DisplayTwoLoop->True]


Integrate@@%


TwoLoop[{{k2-k1,1},{k1-p,1},{k1,2m \[CapitalEpsilon],1}},{{k2,2 m \[CapitalEpsilon],2}},k2^4,k1,k2,{p},d,(*ExpandD->True,*)DivideNumerators->True,ShowSecondLoopCommand->True,DisplayOneLoop->True,DisplayTwoLoop->True]


(* ::Print:: *)
(*"OneLoop[{{k2, 2*m*\[CapitalEpsilon], 2}, {(\!\(\*SqrtBox[FractionBox[\(\*SuperscriptBox[\(k2\), \(2\)]\\\ \((\(-1\) + x[1])\)\\\ x[1] + 2\\\ k2\\\ p\\\ x[1]\\\ x[2] + \*SuperscriptBox[\(p\), \(2\)]\\\ \((\(-1\) + x[2])\)\\\ x[2] + 2\\\ m\\\ \[CapitalEpsilon]\\\ x[3]\), \(\((\(-1\) + x[1])\)\\\ x[1]\)]]\)), 3 - d/2}}, (2^(-1 - d)*k2^4*Gamma[3 - d/2]*(x[1] - x[1]^2)^(-3 + d/2))/Pi^(d/2), k2, {p}, d, Private`FeynParaVariable -> y, Private`SecondLoop -> True, Private`FeynParaIN -> {x[1], x[2], x[3]}]"*)


Integrate@@%


Integrate@@{(DiracDelta[-1+x[1]+x[2]] DiracDelta[-1+y[1]+y[2]+y[3]] x[1]^4 x[2] Sqrt[y[3]] (-(25/2) p^2 y[1]^2 (p^2 (-1+y[1]) y[1]+2 m \[CapitalEpsilon] (y[2]+(x[2] y[3])/(x[1]-x[1]^2)))^2-945/32 (p^2 (-1+y[1]) y[1]+2 m \[CapitalEpsilon] (y[2]+(x[2] y[3])/(x[1]-x[1]^2)))^4))/(64 (-3+d) \[Pi]^3 (-(-1+x[1]) x[1])^(3/2) (-p^2 (-1+y[1]) y[1]+2 m \[CapitalEpsilon] (-y[2]+(x[2] y[3])/((-1+x[1]) x[1])))^2),{x[1],0,1},{x[2],0,1},{y[1],0,1},{y[2],0,1},{y[3],0,1}}


Get@OneLoop[{{k2-k1,1},{k2,2 m \[CapitalEpsilon],1}},1,k2,d,FirstLoop->True]





OneLoop[{{k2-k1,1},{k2,2 m \[CapitalEpsilon],1}},1,k2,{p},d,DisplayFeynPara->True,FirstLoop->True]//Get



