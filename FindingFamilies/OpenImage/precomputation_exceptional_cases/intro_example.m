// Some verifications for the "involved example" from the intro of the paper.

load "../FindOpenImage.m";

keys:=[k: k in Keys(X) | X[k]`N eq 27 and X[k]`genus eq 0];
assert #keys eq 1;
k:=keys[1];

GL2:=GL(2,Integers(27));
G:=sub<GL2 | [[1,1,0,1],[1,2,3,2],[2,1,9,5]]>;
assert IsConjugate(GL2,X[k]`G,G);
assert X[k]`G eq G;
assert X[k]`index eq 36;   

F<t>:=FunctionField(Rationals());
J:=(X[k]`map_to_jline[1])([t,1]);
J:=J[1];
assert J eq (t^3 + 3)^3 * (t^9 + 9*t^6 + 27*t^3 + 3)^3 / (t^3*(t^6 + 9*t^3 + 27));
assert J-1728 eq (t^18 + 18*t^15 + 135*t^12 + 504*t^9 + 891*t^6 + 486*t^3 - 27)^2/ (t^3*(t^6 + 9*t^3 + 27));

Gc:=sub<GL(2,Integers(54))|{[7,0,36,1], [7,16,0, 25], [16,7,3,5] }>;
assert X[k]`Gc eq Gc;

G:=gl2Lift(G,54);
assert Index(G,Gc) eq 36;
assert X[k]`cyclic_invariants eq [9,2,2];



Pol<t>:=PolynomialRing(Integers());
models:=&cat X[k]`cyclic_models;
assert &and [Pol!Denominator(f) eq Pol!1 : f in models];
models:=[Evaluate(Numerator(f),[t]): f in models];
c:=[
2*(t^6 + 9*t^3 + 27),
-(t^6 + 9*t^3 + 27),
-(t^6 + 9*t^3 + 27),
-(2*t^2 + 2*t - 3)*(t^6 + 9*t^3 + 27),
3*(t - 1)*(t + 2)*(t^6 + 9*t^3 + 27),
-(2*t - 3)*(t^2 + 3*t + 3)*(t^6 + 9*t^3 + 27),
(3*t^2 + 4*t - 3)*(t^6 + 9*t^3 + 27),
t*(t^6 + 9*t^3 + 27),
-3*t*(t^3 + 3)*(t^6 + 9*t^3 + 27)*(t^9 + 9*t^6 + 27*t^3 + 3)*(t^18 + 18*t^15 + 135*t^12 + 504*t^9 + 891*t^6 + 486*t^3 - 27)
];
#c eq #models;
assert &and [c[i] eq models[i] : i in [1..#c]];

rep:=[ [31, 44, 36, 25], [28, 27, 27, 28], [-1,0,0,-1] ];
assert &and [ ( X[k]`cyclic_generators[i]^(-1) * GL(2,Integers(54))!rep[i] ) in Gc : i in [1..3] ];


E:=EllipticCurve([0,1,1,1,0]);
Evaluate(J,-1) eq jInvariant(E);
_,k0,_:=FindAgreeableClosure(jInvariant(E));
assert k eq k0;
GE:=FindOpenImage(E);
gens:=[
    [ 31, 198, 10, 97 ],
    [ 1, 0, 18, 1 ],
    [ 28, 729, 27, 703 ],
    [149, 681, 271, 448],
    [994, 9, 689, 790]
];
gens:=[GL(2,Integers(1026))!g : g in gens];

assert sub<GL(2,Integers(1026)) | gens> eq GE;