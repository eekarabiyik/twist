load "../main/FindOpenImage.m";

G:=sub<GL(2,Integers(37))|[[1,1,0,1],[1,0,0,2],[2,0,0,1]]>;
G:=gl2Lift(G,2*37);

gens:=Generators(CommutatorSubgroup(G)) join {G![39,0,0,1]};
Gc:=sub<GL(2,Integers(74))|gens>;

Q,iota:=quo<G|Gc>;
assert IsAbelian(Q) and #Q eq 72;

E:=EllipticCurve([1,1,1,-8,6]);
P:=DivisionPolynomial(E,37);
P:=ChangeRing(P,Integers());
f:=&*[f[1]: f in Factorization(P) | Degree(f[1]) le 18];
assert Degree(f) eq 18;

for p in [13,19,29] do
    fp:=ChangeRing(f,GF(p));
    d:=2*[Degree(g[1]): g in Factorization(fp)][1];
    q:=p^d;
    FF:=GF(q);

    Ep:=ChangeRing(E,FF);
    fq:=ChangeRing(f,FF);
    a:=FF!Rep(Roots(fq))[1];

    Pol<y>:=PolynomialRing(FF);
    b:=Rep(Roots(Evaluate(DefiningEquation(Ep),[a,y,1])))[1];

    FrobP:=Ep![a^p,b^p];
    P:=Ep![a,b];
    e:=[i: i in [0..36] | FrobP eq i*P][1];

    [p,e]; // prime p and value beta(Frob_p)
end for;


U1:=sub< GL(1,Integers(20)) | [ [11], [17] ]>; 
assert U1 eq GL(1,Integers(20));
gamma1:=hom<U1->GL(1,Integers()) | [ [-1], [-1] ]>;


U2:=sub< GL(1,Integers(1295)) | [ [13], [19], [29] ]>; 
U_37:=GL(1,Integers(37));
assert U2 eq GL(1,Integers(1295));
gamma2:=hom<U2->U_37 | [[6], [26], [36]]>;


D:=CartesianProduct(GL(1,Integers()),U_37);
pairs:=[];
for q in Q do
    A:= q @@ iota;
    a:=U_37![A[2,2]];
    if Order(ChangeRing(A,Integers(2))) in {1,3} then
        pairs:=pairs cat [<D!<[1],[a]>, q>];
    else
        pairs:=pairs cat [<D!<[-1],[a]>, q>];
    end if;
end for;

f:=map<D->Q | pairs>;

U:=GL(1,Integers(5180));
gamma:=hom<U->Q | u:-> f(<gamma1(u),gamma2(u)>)>;

U:=GL(1,Integers(5180));
assert #U/#sub<U|[[3],[11],[13],[19]]> eq 1;

gens:=[[1,38,0,1],[1,1,37,38], [ 13, 0, 0, 2391 ],[ 64, 3737, 37, 2970 ],[ 70, 851, 37, 5038 ],[ 42, 1961, 37, 4318 ]];

for g in gens do
    d:=Integers()!Determinant(GL(2,Integers(5180))!g);     
    assert iota(g) eq gamma([d]) and Determinant(GL(2,Integers(5180))!g) eq d;
end for;