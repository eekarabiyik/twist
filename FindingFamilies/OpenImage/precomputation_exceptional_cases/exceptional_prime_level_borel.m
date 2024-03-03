//load "../main/FindOpenImage.m";

// We consider six non-CM elliptic curves E over Q that have an isogeny of degree ell in {11, 17, 37}.
// In each case, the isogeny and the 2-adic image determine the full image of rho_E.


for j in elladic_exceptionaljs do


    _,k,G:=FindAgreeableClosure(j);

    S:={ell: ell in PrimeDivisors(gl2Level(G)) |  ell in {11, 17, 37}};
    if #S eq 0 then continue j; end if;
    assert #S eq 1;

    ell:=Rep(S);
    assert IsUnentangled(G meet SL(2,BaseRing(G)));
    assert #[i: i in [2..#k] | k[i] ne "1A0-1a"] eq 1;  
    assert #ChangeRing(G,Integers(ell)) eq (ell-1)^2*ell; //upper triangular matrices in GL(2,Z/ell)

    G_:=gl2Lift(G,LCM(2,#BaseRing(G)));
    sl2level,sl2gens,index:=FindCommutatorSubgroup(G_);
    S:=sub<SL(2,Integers(sl2level)) | sl2gens>;

    E:=EllipticCurveWithjInvariant(j);
    E:=MinimalTwist(E);
    E:=MinimalModel(E);
    F:=DivisionPolynomial(E,ell);
    F:=&*[f[1]: f in Factorization(F) | Degree(f[1]) le (ell-1)/2];
    assert Degree(F) eq (ell-1)/2;
    // The polynomial F defines the kernel of an isogeny of degree ell.

    
    M:=&*({p: p in BadPrimes(E)} join {ell});
    M:=&*[p^(Valuation(ell-1,p)+1) : p in PrimeDivisors(M)];
    M:=LCM(M,16);
    
    // We have a representation Gal_Q -> (Z/ell)^* by taking sigma to the upper-left entry of rho_{E,ell}(sigma); this
    // gives rise to a homomorphism gamma: (Z/M)^* -> (Z/ell)^*
    pairs:=[];
    done:=false;
    p:=3;
    while not done do
        repeat
            p:=NextPrime(p);
        until M mod p ne 0;

        FF:=GF(p^(ell-1));
        Ep:=ChangeRing(E,FF);

        _,a:=HasRoot(ChangeRing(F,FF));
        Pol<y>:=PolynomialRing(FF);
        b:=Rep(Roots(Evaluate(DefiningEquation(Ep),[a,y,1])))[1];

        FrobP:=Ep![a^p,b^p];
        P:=Ep![a,b];
        e:=[i: i in [0..ell-1] | FrobP eq i*P];
        assert #e eq 1;
        e:=e[1];

        pairs:=pairs cat [[p,e]];

        if sub<GL(1,Integers(M)) | [ [a[1]] : a in pairs]> eq GL(1,Integers(M)) then
            done:=true;
        end if;

    end while;
    U:=sub<GL(1,Integers(M)) | [ [a[1]] : a in pairs]>;
    gamma:=hom<U-> GL(1,Integers(ell)) | [ [a[2]] : a in pairs] >;

    // Find a small set of generators D for (Z/M)^*
    U_,iota_:=UnitGroup(Integers(M));
    D:={Integers()!iota_(U_.i): i in [1..Ngens(U_)]};
    
    gens:=[];
    for d in D do
        a:=gamma(U![d])[1,1];
        g:=LiftMatrix( GL(2,Integers(ell))![a,0,0,d*a^(-1)], d);
        gens:=gens cat [g];
    end for;

    ker:=Kernel(gamma);
    for d in Sort(Divisors(M)) do
        if d eq 1 then continue d; end if;
        red:=hom<U->GL(1,Integers(d))| [GL(1,Integers(d))!U.i: i in [1..Ngens(U)]]>;
        if Kernel(red) subset ker then
            M1:=d;
            break d;
        end if;
    end for;
    M1:=LCM(M1,ell);

    // So the isogeny, shows the image lies in a certain subgroup of GL(2,Z/M1) that contains the elements in gens
    // along with the expected determinant 1 elements.

    

    // Now consider 2-adic constraint on Galois image

    k0:=base;
    k0[1]:=k[1];
    assert X[k0]`cover_with_same_commutator_subgroup eq k0;
    SS:=LiftQpoints(X[k0]`map_to_jline[1], {X[base]`C![j,1]});
    SS:={Eltseq(a): a in SS};   
    SS:={a: a in SS | a[#a] ne 0};
    assert #SS ne 0;
    u:=Rep(SS);
          
    //GG:=ComputeHE(k0,u,E); 
    N1,gens1:=ComputeHEGenerators(k0,u,E);
    GG:=sub<GL(2,Integers(N1))|gens1>;  // Gives a subgroup of GL(2,Zhat) that contains the image of rho^*_E
    GG:=sub<GL(2,BaseRing(GG))| [Transpose(GG.i): i in [1..Ngens(GG)]]>; //transpose now!

    assert M mod #BaseRing(GG) eq 0;
    assert PrimeDivisors( sl2Level(GG meet SL(2,BaseRing(GG))) ) eq [2];
    M2:=#BaseRing(GG);

    gens1:=[];
    for g0 in gens do
        d:=Determinant(g0);
        assert exists(g1){g: g in GG | Determinant(g) eq d};
        g:=crt(g0,g1,ell,2^Valuation(M2,2));
        g:=LiftMatrix(g,d);
        gens1:=gens1 cat [g];
    end for;
    // adjust gens so that they satisfy these additional constraints

    M:=LCM([M1,M2]);
    gens:=[ GL(2,Integers(M))!g: g  in gens1] cat [ g: g in Generators(sl2Lift(S,M))];
    GE:=sub<GL(2,Integers(M)) | gens>;

    Hc:=CommutatorSubgroup(ChangeRing(GE,Integers(sl2level)));
    
    output:=[* j, aInvariants(E), GE, index, Hc *]; 
    if assigned exceptional_images then exceptional_images:=exceptional_images cat [output]; end if;
    
   
    // The following code shows that the example given in the paper agrees.
    /*
    if j eq -7*11^3 then
        h:=GL(2,BaseRing(GE))![0,1,1,0];
        for g0 in [[1,38,0,1],[1,1,37,38],[13,0,0,2391],[64,3737,37,2970],[70,851,37,5038],[42,1961,37,4318]] do
            g:=GL(2,BaseRing(GE))!g0;
            g:=h*Transpose(g)^(-1)*h^(-1);
            assert g in GE;
        end for;
    end if;
    */


    
end for;
