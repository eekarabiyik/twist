ChangeDirectory("/homes/ek693/Main/FindingFamilies/MainCode");

load "../OpenImage/main/FindOpenImage.m";
load "../OpenImage/SZ-data/RationalFunctions.m";
load "../OpenImage/SZ-data/GL2Invariants.m";



load "../TwistingCode/H90.m";
load "../FamilyFinder/aggclosurecreator.m";
load "../TwistingCode/GroupToCocycle.m";
load "../TwistingCode/TwistingCode.m";

//This is the input of the code, modular curve we are trying to compute a model of.
G:=sub<GL(2,Integers(14))|[    [ 3, 6, 2, 9 ],    [ 11, 4, 8, 11 ]]>;
//G is contained in G0. The family that contains G is of the form F(G0,G meet SL2)
G0:=sub<GL(2,Integers(14))|[[ 11, 2, 8, 3 ],[ 3, 0, 6, 5 ],[ 3, 10, 8, 13 ],[ 11, 8, 12, 5 ],[ 9, 12, 0, 1 ],[ 13, 10, 2, 7 ]]>;


//This is the representative in the Family F(G0,G meet SL2)
H:=sub<GL(2,Integers(14))|[[ 9, 0, 0, 9 ],[ 9, 12, 12, 5 ],[ 13, 4, 6, 3 ],[ 7, 12, 4, 5 ]]>;
//FIRST RUN THE ABOVE LINES!



//IF YOU RUN THE FOLLOWING THREE LINES A FEW TIMES AT SOME POINT IT GIVES AN ERROR.
M:=FindModelOfXG(CreateModularCurveRec0(H),10 : G0:=G0);

xi,K:=GroupToCocycle(G0,H,G,G meet SL(2,Integers(#BaseRing(G))),M);


psi:=Twist(M,xi,K, G0);