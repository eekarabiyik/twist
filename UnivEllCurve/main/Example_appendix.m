P<x,y,z>:=ProjectiveSpace(Rationals(),2);
C:=Curve(P,-15*x^3 - 60*x^2*y - 60*x*y^2 + 8*x*z^2 - 15*y^3 + 3*y*z^2);
PointSearch(C,100);
/*[ (0 : 0 : 1), (-1 : 1 : 0), (3/10 : -7/10 : 1), (-3/10 : 7/10 : 1), (2/15 : -8/15 : 1), (-2/15 : 8/15 : 1), (-132/95 : 32/95 : 1), (132/95 : -32/95 : 1) ]*/

D:=CremonaDatabase();
P<X,Y>:=FunctionField(Rationals(),2);

f1:=120/Y^2*X^2 + 435/Y*X + (300*Y^2 - 64)/Y^2;
f2:=-1800/Y^2*X^2 - 6525/Y*X + (-4725*Y^2 + 960)/Y^2;
f3:=27000/Y^2*X^2 + 97875/Y*X + (70875*Y^2 - 14400)/Y^2;
P<t>:=PolynomialRing(Rationals());

a1:=Rationals()!Evaluate(f1,[3/10,-7/10]);
a2:=Rationals()!Evaluate(f2,[3/10,-7/10]);
a3:=Rationals()!Evaluate(f3,[3/10,-7/10]);
f:=a1*t+a3;
g:=t^3+a2*t^2;
E:=EllipticCurve(g,f);
E;//Elliptic Curve defined by y^2 + 5*x*y + 4500*y = x^3 - 300*x^2 over Rational Field
jInvariant(E);//-19465109/248832
CremonaReference(E);//150a3

//The generators for adelic image are taken from LMFDB
Gens := [[1, 20, 10, 21], [11, 16, 0, 11], [11, 20, 10, 21], [1, 20, 0, 1], [26, 5, 15, 16], [1, 0, 20, 1], [6, 5, 25, 22], [1, 10, 10, 11]];
H:= sub<GL(2,Integers(30))|Gens>;
G30:=sub<GL(2,Integers(30))|[[ 16, 25, 27, 22 ],[ 11, 10, 17, 11 ]]>;

Ht:=sub<GL(2,Integers(30))|[Transpose(GL(2,Integers(30))!g):g in Gens]>;


Order(G30);//2880
Order(Ht);//960

for H in Subgroups(G30:OrderEqual:=960) do;
IsConjugate(GL(2,Integers(30)),Ht,H`subgroup);
end for;


