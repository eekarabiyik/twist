//load "../main/FindOpenImage.m";


// Describe the 2-adic projections of rho_E^* for some E/Q with exceptional j-invariants.  This info is due to Rouse-(Zureick-Brown)
RZBdata:=AssociativeArray();
RZBdata[2048]:= sub<GL(2,Integers(16))| [ [7,14,0,1], [1,5,6,11], [3,0,0,7] ]>;
RZBdata[78608]:= sub<GL(2,Integers(16))| [ [7,0,0,3], [3,5,14,7], [7,7,2,1]  ]>;
RZBdata[68769820673/16]:= sub<GL(2,Integers(16))| [ [3,5,6,3], [3,5,14,7], [7,7,2,1] ]>;
RZBdata[16974593/256]:= sub<GL(2,Integers(16))| [ [7,14,0,1], [5,0,0,1], [1,5,6,3] ]>;
RZBdata[-631595585199146625/218340105584896]:= sub<GL(2,Integers(32))| [ [25,18,2,7], [25,25,2,7], [1,0,8,1], [25,11,2,7] ]>;
RZBdata[777228872334890625/60523872256]:= sub<GL(2,Integers(32))| [ [29,0,4,1], [31,27,0,1], [1,4,0,1], [31,31,2,1] ]>;
RZBdata[-18234932071051198464000/48661191875666868481]:= sub<GL(2,Integers(16))| [ [4,7,15,12], [7,14,7,9], [2,1,11,9] ]>;
RZBdata[-35817550197738955933474532061609984000/2301619141096101839813550846721]:= sub<GL(2,Integers(16))| [ [4,7,15,12], [7,14,7,9], [2,1,11,9] ]>;



// Only interested in exceptional j-invariants with level a power of 2
J:={};
for j in known_exceptional_jinvariants do
    b,k,G:=FindAgreeableClosure(j);
    if b then continue j; end if;
    if PrimeDivisors(#BaseRing(G)) eq [2] then 
        J:=J join {j};
    end if;
end for;



for j in J do  // Consider each such j-invariant

    b,k,G:=FindAgreeableClosure(j);  
    assert IsEven(#BaseRing(G));
    sl2level,_,index:=FindCommutatorSubgroup(G);

    // There is a unique group G0 strictly large than G with [G0:G] minimal;
    // the index [G0:G] will be 2 or 4.  The curve X_G0 will have 
    // infinitely many rational points.  Note that X_G has finitely many rational points.

    // We find G0
    GL2:=GL(2,BaseRing(G));
    T:=[t: t in Transversal(GL2,G) | t notin G];  
    groups:=[];
    for t in T do
        H:=sub<GL2|Generators(G) join {t}>;
        if true notin [ IsConjugate(GL2,H,H_) : H_ in groups] then
            groups:=groups cat [H];
        end if;
    end for;
    min:=Minimum([ Index(H,G): H in groups]);
    groups:=[H: H in groups | Index(H,G) eq min];
    assert #groups eq 1;
    G0:=groups[1];    
    assert Index(G0,G) in {2,4} and GL2Genus(G0) in {0,1};
    
    // Find key k for G0 in our array X of modular curves
    level:=gl2Level(G0);
    G0:=ChangeRing(G0,Integers(level));
    GL2:=GL(2,Integers(level));
    assert exists(k){k: k in Keys(X) |  X[k]`N eq level and IsConjugate(GL2,G0,X[k]`G) };
    assert X[k]`has_infinitely_many_points;


    // Find a group G1 even larger than G0, up to conjugacy, with the same commutator subgroup.
    k1:=X[k]`cover_with_same_commutator_subgroup;
    G1:=X[k1]`G;
 

    // Choose an elliptic curve E/Q with j-invariant j
    E:=EllipticCurveWithjInvariant(j);
    E:=MinimalTwist(E);
    assert jInvariant(E) eq j;
    S:=LiftQpoints(X[k1]`map_to_jline[1], {X[base]`C![j,1]});
    S:={Eltseq(a): a in S};   
    S:={a: a in S | a[#a] ne 0};
    assert #S ne 0;
    u:=Rep(S);
          
    //GG:=ComputeHE(k1,u,E);  
    N1,gens1:=ComputeHEGenerators(k1,u,E);
    GG:=sub<GL(2,Integers(N1))|gens1>; // Gives a subgroup of GL(2,Zhat) that contains the image of rho^*_E

    // From Rouse and Zurieck-Brown, we know the 2-adic image of rho^*_E up to conjugacy.
    N:=LCM([#BaseRing(GG),#BaseRing(RZBdata[j])]);
    GG:=gl2Lift(GG,N);
    assert 2^Valuation(#BaseRing(GG),2) eq #BaseRing(RZBdata[j]);
    N2:=#BaseRing(RZBdata[j]);
    G:=RZBdata[j];

    GL2:=GL(2,Integers(N2));
    subgroups:=[W`subgroup: W in Subgroups(ChangeRing(GG,Integers(N2)):OrderEqual:=#G) ];
    subgroups:=[W: W in subgroups | IsConjugate(GL2,W,G)];
    assert #subgroups ne 0  and  &and[ IsConjugate(GL2,subgroups[1],W): W in subgroups];
    G:=subgroups[1];

    // Choose G so that it is the 2-adic image of rho_E^* wrt the same basis as that for GG.


    G1:=gl2Lift(G1,N2);
    HH:=CommutatorSubgroup(G1);
    H:=CommutatorSubgroup(G);
    assert H subset HH;
    T:=[LiftMatrix(t,1): t in Transversal(HH,H)];
    


        _,_,G_:=FindAgreeableClosure(j);
        assert IsEven(#BaseRing(G_));
        _,_,ind:=FindCommutatorSubgroup(G_);
        assert (ind/X[k1]`commutator_index) eq Index(HH,H);
        // This says we have enough info to work out the image

   
    N1:=#BaseRing(G);
    N2:=#BaseRing(GG) div N1;
    assert PrimeDivisors(N1) eq [2] and IsOdd(N2) and #BaseRing(GG) eq N1*N2;
    


    gens:=[g: g in Generators(sl2Lift(H,#BaseRing(GG)))];
    U_,iota_:=UnitGroup(BaseRing(GG));
    D:={Integers()!iota_(U_.i): i in [1..Ngens(U_)]};
    for d in D do
        g:=ComputeHEGenerators(k1,u,E: d0:=d);
        g:=LiftMatrix(g,d);
        T0:=[t: t in T | (GL(2,BaseRing(G))!t * GL(2,BaseRing(G))!g) in G ];
        assert #T0 eq 1;
        t:=T0[1];
        g:=GL(2,BaseRing(GG))!(t*g);
        gens:=gens cat [g];
    end for;

    GE:=sub<GL(2,BaseRing(GG))|gens>;
    GE:=sub<GL(2,BaseRing(GE))| [Transpose(GE.i): i in [1..Ngens(GE)]] >;  // transpose
    
    assert sl2level eq sl2Level(CommutatorSubgroup(G));
    
    Hc:=CommutatorSubgroup(ChangeRing(GE,Integers(sl2level)));
    output:=[* j, aInvariants(E), GE, index, Hc *]; 
    if assigned exceptional_images then exceptional_images:=exceptional_images cat [output]; end if;
    
end for;

