//load "../main/FindOpenImage.m";
load "../SZ-data/JacobianRank.m"; // Will use to compute a Frobenius matrices

for j in known_exceptional_jinvariants do

    b,k,G:=FindAgreeableClosure(j);
    if b then continue j; end if;
    if j in elladic_exceptionaljs then continue j; end if;
    if IsUnentangled(G) then continue j; end if;
    if j in {64, -23788477376, -5000} then continue j; end if;

    // Choose an elliptic curve E/Q with j-invariant j
    E:=EllipticCurveWithjInvariant(j);
    E:=MinimalTwist(E);
    assert jInvariant(E) eq j;

    G:=gl2Lift(G, LCM([#BaseRing(G),2]) ); // want to always consider 2-adic component
    m,_,index:=FindCommutatorSubgroup(G);
    G:=gl2Lift(G,LCM([m,#BaseRing(G)]));

    assert k in Keys(X);
    assert X[k]`genus ge 2 or X[k]`has_infinitely_many_points eq false;

    k1:=X[k]`pi[1];
    if X[k1]`is_agreeable eq false then
        k1:=X[k1]`pi[1];
    end if;
    assert X[k1]`is_agreeable; 
    k1:=X[k1]`cover_with_same_commutator_subgroup;
    assert #BaseRing(G) mod #BaseRing(X[k1]`G) eq 0 and G subset gl2Lift(X[k1]`G,#BaseRing(G));

    S:=LiftQpoints(X[k1]`map_to_jline[1], {X[base]`C![j,1]});
    S:={Eltseq(a): a in S};   
    S:={a: a in S | a[#a] ne 0};
    assert #S ne 0;
    u:=Rep(S);
        
    //GG:=ComputeHE(k1,u,E);  
    N1,gens1:=ComputeHEGenerators(k1,u,E);
    GG:=sub<GL(2,Integers(N1))|gens1>; // Contains image of rho^*_E


    GG:=gl2Lift(GG,LCM([#BaseRing(GG),#BaseRing(G)]));

    Gc:=X[k1]`Gc;
    H:= Gc meet SL(2,BaseRing(Gc));   // Will describe the intersection of GG with SL2
    assert Index(SL(2,BaseRing(H)),H) eq X[k1]`commutator_index;
    M:=LCM([#BaseRing(G),#BaseRing(H)]);  assert IsEven(M);

    G:=gl2Lift(G,M);
    H:=sl2Lift(H,M);
        
    if index eq X[k1]`commutator_index then
        // In this case, the constraint on the image of rho^* coming from 
        // the curve X[k1] gives the image exactly.

        GE:=sub<GL(2,BaseRing(GG))| [Transpose(GG.i): i in [1..Ngens(GG)]] >;  // transpose
        
        Hc:=CommutatorSubgroup(ChangeRing(GE,Integers(m)));

        output:=[* j, aInvariants(E), GE, index, Hc *]; 
        if assigned exceptional_images then exceptional_images:=exceptional_images cat [output]; end if;
           
    elif index/X[k1]`commutator_index eq Index(H,H meet G) then            
        // In this case, the constraints on the image of rho^* coming from the curve X[k1] and the 
        // agreeable closure G gives the image exactly.

        // The image of rho_E^* has full determinant and lies in the subgroups of GL(2,Zhat) corresponding to G and GG.
        // In this case, this info is enough to determine the image,

        gens:=[g: g in Generators(sl2Lift(CommutatorSubgroup(G),#BaseRing(GG)))];  
        // will give the intersection of the image of rho_E^* with SL(2,Zhat)        

        // take generators of GG and scale by determinant 1 matrix so that they lie in image of rho_E^*
        T:=[LiftMatrix(t,1): t in Transversal(H,H meet G)];
        GL2:=GL(2,BaseRing(G));

        U_,iota_:=UnitGroup(BaseRing(GG));
        D:=[Integers()!iota_(U_.i): i in [1..Ngens(U_)]];

        for d in D do
            g:=ComputeHEGenerators(k1,u,E : d0:=d);
            
            g:=LiftMatrix(g,d);
            I:=[t: t in T | (GL2!t*GL2!g) in G];
            assert #I eq 1;
            t:=GL(2,BaseRing(GG))!I[1];
            g:=t * GL(2,BaseRing(GG))!g;
            assert GL2!g in G;
            gens:=gens cat [g];
        end for;

        GE:=sub<GL(2,BaseRing(GG)) | gens>;  // desired group; has correct intersection with SL2 and has full determinant.
        assert GL2DetIndex(GE) eq 1;
        assert ChangeRing(GE,BaseRing(G)) subset G;
        assert CommutatorSubgroup(ChangeRing(GE,BaseRing(G))) eq CommutatorSubgroup(G);

        GE:=sub<GL(2,BaseRing(GE))| [Transpose(GE.i): i in [1..Ngens(GE)]] >;  // transpose

        Hc:=CommutatorSubgroup(ChangeRing(GE,Integers(m)));

        output:=[* j, aInvariants(E), GE, index, Hc *]; 
        if assigned exceptional_images then exceptional_images:=exceptional_images cat [output]; end if;

    else    
        assert j eq -13824;  // should be only case left
        assert index/X[k1]`commutator_index eq 2;
        assert Index(H,H meet G) eq 1;

        // In this case, we have a group GG of level 12 that contains the image of rho_E^*
        // and is index 2 larger.  The group GG contains -I while the image of rho_E^* does not.
        
        assert #BaseRing(GG) eq 12;
        assert #BaseRing(G) eq 12;
        assert #CommutatorSubgroup(G) eq #CommutatorSubgroup(GG);
        assert #GG/2 eq #GaloisGroup(DivisionPolynomial(E,12)); // may take a minute or two
        assert GL(2,BaseRing(G))![-1,0,0,-1] notin CommutatorSubgroup(G);
        assert GL(2,BaseRing(G))![-1,0,0,-1] in GG;

        GL2:=GL(2,BaseRing(GG));
        HH:=[H`subgroup : H in Subgroups(GG:OrderEqual:=#GG div 2)]; 
        HH:=[H: H in HH | GL2DetIndex(H) eq 1];
        HH:=[H: H in HH | GL2![-1,0,0,-1] notin H];
        assert #HH eq 4;            
        assert &and[IsConjugate(GL2,H,H_):H, H_ in HH] eq true;
        
        // For each of the four groups H in HH, there is a quadratic twist E' so that rho_E'^* lies in H.
        // We now work out these twists; there are four of them.

        D:=&*PrimeDivisors(&*BadPrimes(E)*2*3);
        D:={d: d in Divisors(D)};
        D:=D join {-d: d in D};

        M:=#BaseRing(GG);
        for d in D do
            Ed:=QuadraticTwist(E,d);
            for p in PrimesUpTo(10000) do
                if M mod p eq 0 or p mod #BaseRing(GG) ne 1 then continue p; end if;
                A:=GL(2,BaseRing(GG))! FrobeniusMatrix(ChangeRing(Ed,GF(p)));
                if A^3 eq GL(2,BaseRing(GG))![-1,0,0,-1] then
                    D:=D diff {d}; break p;
                end if;
            end for;
        end for;
        assert #D eq 4;

        GE:=HH[1]; 
        GE:=sub<GL(2,BaseRing(GE))| [Transpose(GE.i): i in [1..Ngens(GE)]] >;  // transpose
        Hc:=CommutatorSubgroup(ChangeRing(GE,Integers(m)));

        d:=Minimum({d: d in D | d gt 0});
        Ed:=QuadraticTwist(E,d);

        output:=[* j, aInvariants(Ed), GE, index, Hc *]; 
        if assigned exceptional_images then exceptional_images:=exceptional_images cat [output]; end if;

                
    end if;

end for;

for j in {-5000} do
    b,k,G:=FindAgreeableClosure(j);
    assert not b;
    assert IsEven(#BaseRing(G));

    m,gens,index:=FindCommutatorSubgroup(G);
    assert #BaseRing(G) mod m eq 0;
    assert GL(2,BaseRing(G))![-1,0,0,-1] in CommutatorSubgroup(G);
    assert CommutatorSubgroup(G) eq G meet SL(2,BaseRing(G));
    
    E:=EllipticCurveWithjInvariant(j);
    E:=MinimalTwist(E);

    GE:=sub<GL(2,BaseRing(G))| [Transpose(G.i): i in [1..Ngens(G)]] >;
    Hc:=CommutatorSubgroup(ChangeRing(GE,Integers(m)));


    output:=[* j, aInvariants(E), GE, index, Hc *]; 
    if assigned exceptional_images then exceptional_images:=exceptional_images cat [output]; end if;


end for;

