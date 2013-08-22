(* ::Package:: *)

(* Mathematica Package *)
(* Author: Everett You *)
(* Created by the Code Collector at Fri 23 Aug 2013 01:19:48 *)
(* from file: /Users/everett/Dropbox/Mathematica/Project/PauliAlgebra/developer.nb *)
(* ===== Begin ===== *)
BeginPackage["PauliAlgebra`"];
\[Sigma]::usage="\[Sigma][\!\(i\_1\),\!\(i\_2\),\[Ellipsis]] denotes \!\(\[Sigma]\_\(i\_1,i\_2,\[Ellipsis]\)\).";
Qbit::usage="Qbit[\*StyleBox[\"A\",\"TI\"]] returns \!\(log\_2\) of the dimension of \[Sigma]-polynominal \*StyleBox[\"A\",\"TI\"].";
\[Sigma]PolynomialQ::usage="\[Sigma]PolynomialQ[\*StyleBox[\"expr\",\"TI\"]] yield True if \*StyleBox[\"expr\",\"TI\"] is a \[Sigma]-polynomial, and yields Flase otherwise.";
Abstract::usage="Abstract[\*StyleBox[\"mat\",\"TI\"]] gives the \[Sigma]-polynominal representation for the matrix \*StyleBox[\"mat\",\"TI\"].";
Represent::usage="Represent[\*StyleBox[\"A\",\"TI\"]] gives the matrix representation for the \[Sigma]-polynominal \*StyleBox[\"A\",\"TI\"].";
ActionSpace::usage="ActionSpace[\*StyleBox[\"A\",\"TI\"]] gives a list {\*StyleBox[\"\!\(M\_A\)\",\"TI\"], \*StyleBox[\"basis\",\"TI\"]}, with the matrix \*StyleBox[\"\!\(M\_A\)\",\"TI\"] representing the action of \[Sigma]-polynominal \*StyleBox[\"A\",\"TI\"] in the space spanned by \[Sigma]-monomial \*StyleBox[\"basis\",\"TI\"].";
Begin["`Private`"];

(* ===== Pauli Matrix ===== *)

(* ----- Check Index ----- *)
\[Sigma]::indx="`1` is not a valid index of Pauli matrix, ascribed to `2`.";
me:\[Sigma][___,i_Integer,___]/;i<0||i>3:=(Message[\[Sigma]::indx,i,Mod[i,4]];\[Sigma][Mod[i,4]]);

(* ----- No \[Sigma] Test ----- *)
(* Return True if free from \[Sigma] *)
SetAttributes[\[Sigma]FreeQ,HoldAll];
\[Sigma]FreeQ[expr_]:=FreeQ[Unevaluated[expr],\[Sigma]];

(* ----- \[Sigma]-Polynomial Test ----- *)
(* Return True if input is a \[Sigma]-polynomial *)
SetAttributes[\[Sigma]PolynomialQ,HoldAll];
\[Sigma]PolynomialQ[expr_]:=Switch[Qbit[expr],0,!\[Sigma]FreeQ[expr],_Integer,True,_,False];

(* ----- Qbit ----- *)
(* Return log2 of matrix dimsion *)
SetAttributes[Qbit,HoldAll];
Qbit[\[Sigma][a___]]:=Length[{a}];
Qbit[CircleTimes[x___]]:=Plus@@(Qbit/@Unevaluated[{x}]);
Qbit[(Plus|CenterDot)[x___]]:=If[Equal@@#,First[#],Indeterminate]&@(Qbit/@Unevaluated[{x}]);
Qbit[Power[x_,_]]:=Qbit[x];
Qbit[Times[x__,y_]]:=Qbit[y];
Qbit[_[x_]]:=Qbit[x];
Qbit[_[x__]]:=Max[Qbit/@Unevaluated[{x}]];
Qbit[_]:=0;

(* ----- \[Sigma]0 ----- *)
(* Return the idendity matrix of same dimension as input matrix *)
\[Sigma]0[A_]:=\[Sigma]@@Array[0&,Qbit[A]];

(* ----- Traditional Form ----- *)
Format[\[Sigma][a___],TraditionalForm]:=Subscript[\[Sigma],a]

(* ===== Tensor Product ===== *)

(* ----- Definition ----- *)
(* Tensor product Pauli matrices *)
CircleTimes[A:_\[Sigma]]:=A;
CircleTimes[A___,\[Sigma][a___],\[Sigma][b___],B___]:=CircleTimes[A,\[Sigma][a,b],B];
(* \[Sigma]-free expressions are treated as number times \[Sigma][] *)
CircleTimes[A___,x_?\[Sigma]FreeQ,B___]:=x CircleTimes[A,B];

(* ----- Algebraic Properties ----- *)
(* Pull out factors *)
CircleTimes[A___,B_Times,C___]:=Most[B] CircleTimes[A,Last[B],C];
CircleTimes[___,0,___]:=0;
(* Distribute over plus *)
me:CircleTimes[___,_Plus,___]:=Distribute[Unevaluated[me],Plus];

(* ===== Dot Product ===== *)

(* ----- Definition ----- *)
(* Definition of dot product. *)
CenterDot::dimx="The operators `1` and `2` are incompatable in dimensions.";
CenterDot[A:_\[Sigma]]:=A;
CenterDot[A___,\[Sigma][a___],\[Sigma][b___],B___]/;Length[{a}]==Length[{b}]:=CenterDot[A,(Times@@Flatten[#2]) #1&@@Reap[\[Sigma]@@MapThread[IndexProduct,{{a},{b}}]],B];
(* Index product rule of Pauli algebra. *)
IndexProduct[0,i_]:=i;
IndexProduct[i_,0]:=i;
IndexProduct[i_,i_]:=0;
IndexProduct[1,2]:=(Sow[I];3);
IndexProduct[2,3]:=(Sow[I];1);
IndexProduct[3,1]:=(Sow[I];2);
IndexProduct[2,1]:=(Sow[-I];3);
IndexProduct[3,2]:=(Sow[-I];1);
IndexProduct[1,3]:=(Sow[-I];2);

(* ----- Algebraic Properties ----- *)
(* Pull out factors *)
CenterDot[A___,B_Times,C___]:=Most[B] CenterDot[A,Last[B],C];
(* Distribute over plus *)
me:CenterDot[___,_Plus,___]:=Distribute[Unevaluated[me],Plus];

(* ===== Transformations ===== *)

(* ----- Conjugate ----- *)
Unprotect[Conjugate];
Conjugate[\[Sigma][a___]]:=\[Sigma][a];
Protect[Conjugate];

(* ----- Tr ----- *)
Unprotect[Tr];
Tr[A_?\[Sigma]PolynomialQ]:=2^Qbit[A] nTr[A];
nTr[A_]:=A/.{\[Sigma]0[A]->1,_\[Sigma]->0}
Protect[Tr];

(* ----- Det ----- *)
Unprotect[Det];
Det[A_?\[Sigma]PolynomialQ]:=xDet[A];
Protect[Det];
xDet[A_]:=Module[{Amat,\[Sigma]s,n,M},{Amat,\[Sigma]s}=xActionSpace[A];
n=Qbit[A];
M=Length[\[Sigma]s];
Det[Amat]^(2^n/M)];

(* ----- Transpose ----- *)

(* ===== Represent ===== *)
(* Give matrix represenation of \[Sigma]-polynomial *)
Represent[\[Sigma][]]=1;
Represent[\[Sigma][i_]]:=SparseArray[ArrayRules[PauliMatrix[i]]];
Represent[\[Sigma][a__]]:=KroneckerProduct@@(Represent[\[Sigma][#]]&/@{a});
Represent[expr_]:=Represent/@expr;
Represent[x_?\[Sigma]FreeQ]:=x;

(* ===== Abstract ===== *)
(* Give \[Sigma]-polynominal representation of matrix *)
Abstract[M_?MatrixQ]/;Function[#1==#2&&Log[2,#1]\[Element]Integers]@@Dimensions[M]:=xAbstract[M]

(* ----- Kernel ----- *)
xAbstract[M_]:=If[MatrixQ[M,PossibleZeroQ],0,Total[MapThread[CircleTimes[xAbstract[#1],#2]&,{Transpose[Map[bAbstract,Partition[M,{2,2}],{2}],{2,3,1}],(\[Sigma]/@Range[0,3])}]]];
xAbstract[{{x_}}]:=x \[Sigma][];
bAbstract[{{a_,b_},{c_,d_}}]:=Chop[{a+d,b+c,I (b-c),a-d}/2];

(* ===== ActionSpace ===== *)
(* Represent the action of Pauli polynominal in the Pauli matrix basis. *)
ActionSpace[A_?\[Sigma]PolynomialQ]:=Module[{Amat,\[Sigma]s,ord},{Amat,\[Sigma]s}=xActionSpace[A];
ord=Ordering[\[Sigma]s];
{Amat[[ord,ord]],\[Sigma]s[[ord]]}];

(* ----- Kernel ----- *)
xActionSpace[A_]:=Module[{\[Sigma]s,n,pos,Arule,i,Amat},\[Sigma]s=Cases[A,_\[Sigma],{0,Infinity}];
n=Length[\[Sigma]s];
pos[s_]:=If[Length[#]==0,AppendTo[\[Sigma]s,s];++n,First@First@#]&@Position[\[Sigma]s,s,{1},1];
Arule[p_]:=Module[{As},As=A\[CenterDot]\[Sigma]s[[p]];
Rule[{pos[#],p},Coefficient[As,#]]&/@Cases[As,_\[Sigma],{0,Infinity}]];
i=1;
Amat=SparseArray[Flatten[Last[Reap[While[i<=n&&i<=4^Qbit[A],Sow[Arule[i++]]]]]],{n,n}];
{Amat,\[Sigma]s}];

(* ===== Inversion ===== *)
(* Mordify the definition of Inverse *)
Unprotect[Inverse];
me:Inverse[A_?\[Sigma]PolynomialQ]:=Check[invSimplify[xInverse[A]],Message[Inverse::sing,A];
HoldForm[me]];
Protect[Inverse];

(* ----- Kernel ----- *)
xInverse[A_]:=Module[{Amat,\[Sigma]s,sol,singular=False},{Amat,\[Sigma]s}=xActionSpace[A];
sol=Check[LinearSolve[Amat,nTr[\[Sigma]s]],singular=True];
If[!singular,sol.\[Sigma]s]];
invSimplify[expr_]:=Collect[Numerator[#],_\[Sigma],Factor]/Simplify[Denominator[#]]&@aTogether[expr];
aTogether[expr_]:=expr//.{a_/d_+b_/d_:>(a+b)/d,a_/c_+b_/d_:>With[{lcm=PolynomialLCM[c,d]},(a Cancel[lcm/c]+b Cancel[lcm/d])/lcm]};

(* ===== Power ===== *)
(* Mordify the definition of Power *)
Unprotect[Power];
me:Power[A_?\[Sigma]PolynomialQ,n_Integer]:=Check[Which[n==0,\[Sigma]0[A],n>0,nPower[A,n],n<0,nPower[xInverse[A],Abs[n]]],HoldForm[me]];
me:Power[A_?\[Sigma]PolynomialQ,n_?NumericQ]:=Check[xPower[A,n],HoldForm[me]];
Protect[Power];
(* Mordify the definition of Sqrt *)
Unprotect[Sqrt];
me:Sqrt[A_?\[Sigma]PolynomialQ]:=xPower[A,1/2];
Protect[Sqrt];

(* ----- Kernel (Integer Power) ----- *)
(* Algorithm:divide and conquer *)
nPower[A_,n_]:=Module[{m,B},m=Floor[n/2];
B=nPower[A,m];
Collect[Switch[n-2 m,0,B\[CenterDot]B,1,B\[CenterDot]B\[CenterDot]A],_\[Sigma]]];
nPower[A_,0]:=\[Sigma]0[A];
nPower[A_,1]:=A;
nPower[A_,2]:=Collect[A\[CenterDot]A,_\[Sigma]];

(* ----- Kernel (General Power) ----- *)
xPower[A_,x_]:=Module[{Amat,\[Sigma]s},{Amat,\[Sigma]s}=xActionSpace[A];
MatrixPower[Amat,x,nTr[\[Sigma]s]].\[Sigma]s]

(* ===== Exponent ===== *)
(* Mordify the definition of Exp *)
Unprotect[Exp];
me:Exp[A_?\[Sigma]PolynomialQ]:=xExp[A];
Protect[Exp];

(* ----- Kernel ----- *)
xExp[A_]:=Module[{Amat,\[Sigma]s},{Amat,\[Sigma]s}=xActionSpace[A];
MatrixExp[Amat,nTr[\[Sigma]s]].\[Sigma]s]

(* ===== Logarithm ===== *)
(* Mordify the definition of Log *)
Unprotect[Log];
me:Log[A_?\[Sigma]PolynomialQ]:=xLog[A];
Protect[Log];

(* ----- Kernel ----- *)
xLog[A_]:=Module[{Amat,\[Sigma]s},{Amat,\[Sigma]s}=xActionSpace[A];
\[Sigma]s.MatrixLog[Amat].nTr[\[Sigma]s]]

(* ===== End ===== *)
End[];
EndPackage[];

