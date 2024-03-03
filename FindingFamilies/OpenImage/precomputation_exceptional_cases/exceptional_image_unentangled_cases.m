//load "../main/FindOpenImage.m";

function crt0(seq)
    // given a sequence a_i of elements of Z/N_i with the N_i pairwise relatively prime,
    //  we find the element of Z/(N_1*...*N_n arising from the Chinese remainder theorem.
    if #seq eq 1 then return seq[1]; end if;
    if #seq eq 2 then 
        N1:=#BaseRing(Parent(seq[1]));
        N2:=#BaseRing(Parent(seq[2]));
        return crt(seq[1],seq[2],N1,N2);
    end if;
    return crt0([*seq[1]*] cat [*crt0([*seq[i]: i in [2..#seq]*])*]);
end function;


for j in known_exceptional_jinvariants do

    b,k,G:=FindAgreeableClosure(j);
    if b then continue j; end if;

    if j in elladic_exceptionaljs then continue j; end if;
    if IsUnentangled(G) eq false and j notin {64, -23788477376} then continue j; end if;

    index1:=IndexOfCommutator(G);

    index2:=1;
    G:=gl2Lift(G,LCM([#BaseRing(G),2])); // want to always consider the prime 2
    N:=#BaseRing(G);
    P:=PrimeDivisors(N);
    for p in P do
        Gp:=ChangeRing(G,Integers(p^Valuation(N,p)));
        _,_,ind:=FindCommutatorSubgroup(Gp);
        index2:=index2*ind;
    end for;


    assert index1 eq index2;  // this is a measure of unentanglement as in paper

    // Choose an elliptic curve E/Q with j-invariant j
    E:=EllipticCurveWithjInvariant(j);
    E:=MinimalTwist(E);
    assert jInvariant(E) eq j;

    assert #BaseRing(G) mod 2 eq 0;
    m,gens0,index:=FindCommutatorSubgroup(G);
    Hc:=sub<SL(2,Integers(m))|gens0>;

    G:=gl2Lift(G,LCM([m,#BaseRing(G)]));

    S:=CommutatorSubgroup(G);
    S:=ChangeRing(S,Integers(sl2Level(S)));
    assert IsUnentangled(S);
    
    P0:=[2,3,5,7,11,13,17,37];
    
    K:=[];
    P:=[];
    //Gp:=[];    
    GG:=[];
    U:=[];
    
    for i in [1..#P0] do
        if i gt 1 and k[i] eq "1A0-1a" then continue i; end if;
        k0:=base;
        k0[i]:=k[i];
        assert k0 in Keys(X) and X[k0]`has_infinitely_many_points;

        k1:=X[k0]`cover_with_same_commutator_subgroup;
        SS:=LiftQpoints(X[k1]`map_to_jline[1], {X[base]`C![j,1]});
        SS:={Eltseq(a): a in SS};   
        SS:={a: a in SS | a[#a] ne 0};
        assert #SS ne 0;
        u:=Rep(SS);

        K:=K cat [k1];
        U:=U cat [u];

        //HE:=ComputeHE(k1,u,E);
        N1,gens1:=ComputeHEGenerators(k1,u,E);
        HE:=sub<GL(2,Integers(N1))|gens1>;
    
      // Contains image of rho^*_E

        P:=P cat [P0[i]];
        if IsOdd(P0[i]) then
            Nq:=#BaseRing(HE) div 2^Valuation(#BaseRing(HE),2);
            HE:=sub<GL(2,BaseRing(HE)) | Generators(HE) join {SL(2,BaseRing(HE))![1-Nq,-Nq,Nq,1+Nq]}>;
        end if;
        GG:=GG cat [HE];
    end for;

    S:=CommutatorSubgroup(G);


    N:=LCM([#BaseRing(H): H in GG]);
    G:=gl2Lift(G,LCM(N,#BaseRing(G)));
    SN:=sl2Lift(S,N);
    
    UN,iotaN:=UnitGroup(Integers(N));
    D:=[ Integers()!iotaN(UN.i): i in [1..Ngens(UN)]];
    
    gens:=[s: s in Generators(SN)];
    for d in D do
        g:=[* *];
        for i in [1..#P] do
            q:=P[i]^Valuation(N,P[i]);

            gp:=ComputeHEGenerators(K[i],U[i],E: d0:=d);
            gp:=LiftMatrix(gp,d);

            g:=g cat [*GL(2,Integers(q))!gp*];
        end for;
        g:=LiftMatrix(crt0(g),d);
        gens:=gens cat [GL(2,Integers(N))!g];
        
    end for;

    GE:=sub<GL(2,Integers(N))| gens>;
    GE:=sub<GL(2,BaseRing(GE))| [Transpose(GE.i): i in [1..Ngens(GE)]] >;  // transpose

    Hc:=sub<SL(2,BaseRing(Hc))| [Transpose(Hc.i): i in [1..Ngens(Hc)]] >;  // transpose

    output:=[* j, aInvariants(E), GE, index, Hc *]; 
    if assigned exceptional_images then exceptional_images:=exceptional_images cat [output]; end if;

    
end for;


