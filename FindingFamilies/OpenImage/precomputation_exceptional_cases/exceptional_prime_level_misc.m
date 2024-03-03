

//load "../main/FindOpenImage.m";


for j in {-160855552000/1594323, 90616364985637924505590372621162077487104/197650497353702094308570556640625, 11225615440/1594323} do

    E:=EllipticCurveWithjInvariant(j);
    E:=MinimalTwist(E);
    b,k,G:=FindAgreeableClosure(j);
    assert not b;

    assert #BaseRing(G) eq 13;

    m,gens0,index:=FindCommutatorSubgroup(gl2Lift(G,2*#BaseRing(G)));
    Hc:=sub<SL(2,Integers(m))|gens0>;
    assert index eq 2 * Index(GL(2,BaseRing(G)),G);
    // This means that only constraing on rho_E^* is Serre curve constraint and 13-adic constraint.

    T:=Transversal(SL(2,Integers(13)),G meet SL(2,Integers(13)));
    T:=[crt(t,[1,0,0,1],13,2): t in T];
    T:=[LiftMatrix(t,1): t in T];
   
    u:=X[base]`C![j,1];
    //HE:=ComputeHE(base,u,E);  
    N1,gens1:=ComputeHEGenerators(base,u,E);
    HE:=sub<GL(2,Integers(N1))|gens1>;  // Contains image of rho^*_E
    M:=LCM(#BaseRing(HE),13); 

    U_,iota_:=UnitGroup(Integers(M));
    D:={Integers()!iota_(U_.i): i in [1..Ngens(U_)]};

    S:=CommutatorSubgroup(gl2Lift(G,2*#BaseRing(G)));
    S:=sl2Lift(S,M);
    gens:=[g: g in Generators(S)];

    GL2:=GL(2,BaseRing(G));
    for d in D do
        g:=ComputeHEGenerators(base,u,E : d0:=d);
        g:=LiftMatrix(g,d);
        
        T0:=[t: t in T | (GL2!t*GL2!g) in G ];
        assert #T0 eq 1;

        g:=T0[1]*g;
        g:=GL(2,Integers(M))!g;
        gens:=gens cat [g];
    end for;

    GE:=sub<GL(2,Integers(M)) | gens>;

    GE:=sub<GL(2,BaseRing(GE))| [Transpose(GE.i): i in [1..Ngens(GE)]] >;  // transpose
    Hc:=sub<SL(2,BaseRing(Hc))| [Transpose(Hc.i): i in [1..Ngens(Hc)]] >;

    output:=[* j, aInvariants(E), GE, index, Hc *]; 

    if assigned exceptional_images then exceptional_images:=exceptional_images cat [output]; end if;

end for;





J:={136878750000, 210720960000000/16807};  

for j in J do
    _,k,G:=FindAgreeableClosure(j);
    

    assert #BaseRing(G) mod 25 eq 0;
    assert 100 mod #BaseRing(G) eq 0;

    G_:=ChangeRing(G,Integers(#BaseRing(G) div 5));
    G_:=ChangeRing(G_,Integers(gl2Level(G_)));
    K:=[k: k in Keys(X) | X[k]`N eq #BaseRing(G_) and X[k]`genus le 1];
    K:=[k: k in K | IsConjugate(GL(2,BaseRing(G_)), G_, X[k]`G) ];
    assert #K eq 1;
    k1:=K[1];
    assert X[k1]`has_infinitely_many_points;

    _,h:=IsConjugate(GL(2,BaseRing(G_)), G_, X[k1]`G);
    assert Conjugate(G_,h) eq X[k1]`G;
    h:=GL(2,BaseRing(G))![Integers()!a: a in Eltseq(h)];
    G:=Conjugate(G,h);
    assert ChangeRing(G,BaseRing(G_)) eq X[k1]`G;

    k1:= X[k1]`cover_with_same_commutator_subgroup;
    assert ChangeRing(G,Integers(X[k1]`N)) subset X[k1]`G;
    T:=Transversal( gl2Lift(ChangeRing(G,Integers(5)),25) meet SL(2,Integers(25)),ChangeRing(G,Integers(25)) meet SL(2,Integers(25)));
    assert #T eq 5;
    T:=[crt(t,[1,0,0,1],25,4): t in T];
    T:=[LiftMatrix(t,1): t in T];
    
    
    E:=EllipticCurveWithjInvariant(j);
    E:=MinimalTwist(E);
    
    SS:=LiftQpoints(X[k1]`map_to_jline[1], {X[base]`C![j,1]});
    SS:={Eltseq(a): a in SS};   
    SS:={a: a in SS | a[#a] ne 0};
    assert #SS ne 0;
    u:=Rep(SS);

    //HE:=ComputeHE(k1,u,E); 
    N1,gens1:=ComputeHEGenerators(k1,u,E);
    HE:=sub<GL(2,Integers(N1))|gens1>; // Contains image of rho^*_E  

    m,gens_,index:=FindCommutatorSubgroup(gl2Lift(G,LCM(#BaseRing(G),2)));
    assert X[k1]`commutator_index * 5 eq index;
    // This shows the image of rho^*_E can be determined from HE and G.

    M:=LCM([#BaseRing(HE),25,m]);
    S:=sub<SL(2,Integers(m)) | gens_>;
    S:=sl2Lift(S,M);
    gens:=[g: g in Generators(S)];


    U_,iota_:=UnitGroup(Integers(M));
    D:={Integers()!iota_(U_.i): i in [1..Ngens(U_)]};

    
    GL2:=GL(2,Integers(25));
    for d in D do
        g:=ComputeHEGenerators(k1,u,E : d0:=d);
        g:=LiftMatrix(g,d);
        
        T0:=[t: t in T | (GL2!t*GL2!g) in ChangeRing(G,Integers(25)) ];
        assert #T0 eq 1;

        g:=T0[1]*g;
        g:=GL(2,Integers(M))!g;
        gens:=gens cat [g];
    end for;

    GE:=sub<GL(2,Integers(M)) | gens>;

    m,gens0,index:=FindCommutatorSubgroup(gl2Lift(G,LCM(2,#BaseRing(G))));
    Hc:=sub<SL(2,Integers(m))|gens0>;

    GE:=sub<GL(2,BaseRing(GE))| [Transpose(GE.i): i in [1..Ngens(GE)]] >;  // transpose
    Hc:=sub<SL(2,BaseRing(Hc))| [Transpose(Hc.i): i in [1..Ngens(Hc)]] >;

    output:=[* j, aInvariants(E), GE, index, Hc *]; 

    if assigned exceptional_images then exceptional_images:=exceptional_images cat [output]; end if;


end for;




J:={2268945/128};
for j in J do
    _,k,G:=FindAgreeableClosure(j);
    
    assert gl2Level(G) eq 8*7;

    // Construct a certain group G_ that is index 2 larger than G
    NG:=Normalizer(GL(2,BaseRing(G)),G);
    assert Index(NG,G) eq 4;
    HH:=[H`subgroup: H in Subgroups(NG: OrderEqual:=#NG div 2 )];
    HH:=[H: H in HH | G subset H and GL2DetIndex(H) eq 1];
    HH:=[H: H in HH | ChangeRing(H,Integers(7)) ne ChangeRing(G,Integers(7))];
    HH:=[H: H in HH | GL2Genus(H) le 1];
    assert #HH eq 1;
    G_:=HH[1];
    assert gl2Level(G_) eq 56;

    // The modular curve X_{G_} has genus 1 and infinitely many rational points;
    // we find the corresponding label
    K:=[k: k in Keys(X) | X[k]`N eq #BaseRing(G_) and X[k]`genus le 1];
    K:=[k: k in K | IsConjugate(GL(2,BaseRing(G_)), G_, X[k]`G) ];
    assert #K eq 1;
    k1:=K[1];
    assert X[k1]`has_infinitely_many_points;

    // replace G and G_ by conjugating so that G_ occurs exactly in our classification
    _,h:=IsConjugate(GL(2,BaseRing(G_)), G_, X[k1]`G);
    assert Conjugate(G_,h) eq X[k1]`G;
    h:=GL(2,BaseRing(G))![Integers()!a: a in Eltseq(h)];
    G:=Conjugate(G,h);  assert #BaseRing(G) eq 56;

    k1:= X[k1]`cover_with_same_commutator_subgroup;

    m,gens_,index:=FindCommutatorSubgroup(G);

    assert #CommutatorSubgroup(ChangeRing(X[k1]`G,Integers(7)))/#CommutatorSubgroup(ChangeRing(G,Integers(7))) eq 2;
    assert index/X[k1]`commutator_index eq 2;
    
    E:=EllipticCurve([1, -1, 1, -2680, -50053]);
    assert jInvariant(E) eq j;
    // We have chosedn this particular curve since one can show that its image mod 7 is index 2 smaller than
    // most other quadratic twists.
    
    SS:=LiftQpoints(X[k1]`map_to_jline[1], {X[base]`C![j,1]});
    SS:={Eltseq(a): a in SS};   
    SS:={a: a in SS | a[#a] ne 0};
    assert #SS ne 0;
    u:=Rep(SS);

    //HE:=ComputeHE(k1,u,E);  
    N1,gens1:=ComputeHEGenerators(k1,u,E);
    HE:=sub<GL(2,Integers(N1))|gens1>; // Contains image of rho^*_E  

    assert #BaseRing(HE) eq #BaseRing(G); 
    // This is so simple, we can just intersect.
    GE:=HE meet G;

    assert CommutatorSubgroup(GE) eq CommutatorSubgroup(G);
    assert GL2DetIndex(GE) eq 1;


    // The group GE contains the image of rho_E^* as an index 2 subgroup.
    // Our choice of E show that this difference can be detected modulo 7; we now
    // find all possible such subgroups (they are unique up to conjugacy in GL(2,Zhat).
    GG:=[H`subgroup: H in Subgroups(GE:OrderEqual:=#GE div 2)];
    GG:=[H: H in GG | GL2DetIndex(H) eq 1 and ChangeRing(H,Integers(7)) ne ChangeRing(GE,Integers(7)) 
                                and CommutatorSubgroup(GE) eq CommutatorSubgroup(H) ];
    assert #GG eq 2 and IsConjugate(GL(2,BaseRing(GE)),GG[1],GG[2]);
    GE:=GG[1];

    //m,gens0,index:=FindCommutatorSubgroup(gl2Lift(G,LCM(2,#BaseRing(G))));


    Hc:=CommutatorSubgroup(GE);
    sl2level:=sl2Level(Hc);
    Hc:=ChangeRing(Hc,Integers(sl2level));



    GE:=sub<GL(2,BaseRing(GE))| [Transpose(GE.i): i in [1..Ngens(GE)]] >;  // transpose
    Hc:=sub<SL(2,BaseRing(Hc))| [Transpose(Hc.i): i in [1..Ngens(Hc)]] >;

    output:=[* j, aInvariants(E), GE, index, Hc *]; 

    if assigned exceptional_images then exceptional_images:=exceptional_images cat [output]; end if;

end for;