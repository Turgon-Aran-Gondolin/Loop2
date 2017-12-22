(* ------------------------------------------------------------------------ *)
(* ------------------------------------------------------------------------ *)

(* :Summary: ExpandScalarProduct expands scalar products *)

(* ------------------------------------------------------------------------ *)

ExpandScalarProduct::usage =
"ExpandScalarProduct[expr]  expands scalar products of sums of \
momenta in expr. ExpandScalarProduct[x, y] expands ScalarProduct[x, y], \
where x and y may contain sums. ExpandScalarProduct does not use Expand on \
expr.";

ScalarProductExpand::usage =
"ScalarProductExpand is equivalent to ExpandScalarProduct.";

(* ------------------------------------------------------------------------ *)

Begin["`Package`"]
End[]

Begin["`ExpandScalarProduct`Private`"]

ScalarProductExpand = ExpandScalarProduct;
tmpHead;

Options[ExpandScalarProduct] = {
	EpsEvaluate -> False,
	FCI -> True,
	Momentum -> All
};

ExpandScalarProduct[x_, OptionsPattern[]] :=
	Block[ {nx = x, pali,moms},

		moms = OptionValue[Momentum];

		If[ OptionValue[FCI],
			nx = FCI[nx]
		];

		(* This is to speed up things when dealing with tirival scalar products *)
		If[	MatchQ[nx, Pair[Momentum[_, ___], Momentum[_, ___]]] && FreeQ[nx,Plus],
			Return[nx]
		];

		If[ FreeQ2[nx,$FCTensorList],
			Return[nx]
		];

		If [moms===All,
			pali = Select[Cases2[nx, $FCTensorList], !FreeQ2[#, TensorArgsList]&],
			pali = Select[Cases2[nx, $FCTensorList], (!FreeQ2[#, TensorArgsList] && !FreeQ2[#, moms])&]
		];

		If[ pali =!= {},
			nx = nx /. Dispatch[Thread[pali -> pairexpand[pali]]]
		];

		If[	OptionValue[EpsEvaluate],
			nx = EpsEvaluate[nx,FCI->True,Momentum->OptionValue[Momentum]]
		];

		nx
	];

(* TODO this is a legacy syntax that one should get rid of! *)
ExpandScalarProduct[x_, y:Except[_?OptionQ], OptionsPattern[]] :=
	scevdoit[Pair,x, y];

pairexpand[x_] :=
	x /. (head : (Alternatives @@ $FCTensorList))[arg__]/; head=!=Eps :>scevdoit[head,arg] ;

scevdoit[head_,arg__] :=
	Distribute[tmpHead@@(Expand[MomentumExpand/@{arg}])]/.tmpHead->head;

FCPrint[1,"ExpandScalarProduct.m loaded."];
End[]
