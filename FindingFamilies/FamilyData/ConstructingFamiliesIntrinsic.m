
/*
This is the code for finding all groups that contain the agreeable groups up to a certain genus. 
*/
//Details will be added.
//Fork of zywina's code will come soon.




filename:="CummingsPauli/CPdata.dat";  
I:=Open(filename, "r"); 
_,cp_data:=ReadObjectCheck(I);
//Code by David Zywina



gonality_equals_2:=[ "8B3", "10B3", "12C3", "12D3", "12E3", "12F3", "12G3", "12H3", "12K3",
"12L3", "14A3", "14C3", "14F3", "15F3", "15G3", "16B3", "16C3", "16D3", "16E3", "16F3",
"16I3", "16J3", "16M3", "16S3", "18A3", "18C3", "18F3", "18G3", "20C3", "20F3", "20G3",
"20H3", "20I3", "20J3", "20M3", "20O3", "21A3", "21B3", "21D3", "24A3", "24B3", "24C3",
"24G3", "24I3", "24K3", "24L3", "24M3", "24S3", "24U3", "24V3", "24W3", "28C3", "28E3",
"30B3", "30G3", "30J3", "30K3", "30L3", "32B3", "32C3", "32D3", "32H3", "32K3", "32M3",
"33C3", "34B3", "35A3", "36E3", "36F3", "36G3", "39A3", "40D3", "40E3", "40F3", "40I3",
"41A3", "42E3", "48C3", "48E3", "48F3", "48H3", "48I3", "48J3", "48M3", "50A3", "54A3",
"60C3", "60D3", "64A3", "96A3", "18B4", "25A4", "25D4", "32B4", "36C4", "42A4", "44B4",
"47A4", "48C4", "50A4", "50D4", "10A5", "14C5", "16G5", "18A5", "24A5", "24D5", "26A5",
"30C5", "30F5", "36A5", "36B5", "36H5", "40A5", "42A5", "44B5", "45A5", "45C5", "46A5",
"48A5", "48E5", "48F5", "48G5", "48H5", "50A5", "50D5", "50F5", "52B5", "54A5", "57A5",
"58A5", "59A5", "60A5", "96A5", "48A6", "71A6", "32E7", "48N7", "56B7", "64D7", "82B7",
"96A7", "93A8", "50A9", "50D9", "96B9", "48B11", "72A11", "96B11"];
//By David Zywina
function ContainsScalars(G)
    // For a subgroup of GL(2,Z/N) with N>1, return true if G contains all the scalar matrices and false otherwise.
    N:=#BaseRing(G);
    GL2:=GL(2,Integers(N));
    U,iota:=UnitGroup(Integers(N));
    return &and [ (GL2![iota(U.i),0,0,iota(U.i)]) in G : i in [1..Ngens(U)] ];
end function;

//By David Zywina
function AdjoinScalars(G)
    // For a subgroup of GL(2,Z/N) with N>1, return the group obtained by adding all the scalar matrices to G.
    N:=#BaseRing(G);
    GL2:=GL(2,Integers(N));
    gens:=[G.i: i in [1..Ngens(G)]];
    U,iota:=UnitGroup(Integers(N));
    gens:= gens cat [ GL2![iota(U.i),0,0,iota(U.i)] : i in [1..Ngens(U)] ];
    return sub<GL2|gens>;
end function;

function FindSpecialSubgroup(G,W)
    /*  Input:
            - G an open subgroup of GL(2,Zhat), given as a group in GL(2,Z/NZ), that contains
                all the scalar matrices.
            - W an open subgroup of SL(2,Zhat) that is contained in G and contains [G,G];
                it is given as a subgroup of SL(2,Z/MZ)
    
        Output:
            This function find an open subgroup B of G such that B intersected with SL(2,Zhat) 
            is W and such that the index [det(G):det(B)] is minimal.

            Let m be the lcm of N and M.  
            When m is odd, B will be a group given modulo m.
            When m is odd, B will be a group given modulo m times some power of 2.
    */

    N:=LCM(#BaseRing(G),#BaseRing(W));
    if IsEven(N) then N:=LCM(N,8); end if;

    UN,iotaN:=UnitGroup(Integers(N));
    G1:=GL2Lift(G,N); 
    W1:=SL2Lift(W,N);

    // We work with 2-Sylow subgroups to work out the 2-adic part
    G1_2:=SylowSubgroup(G1,2);
    W1_2:=W1 meet G1_2; // a 2-sylow subgroup of W1
    Q1,phi1:=quo<G1_2|W1_2>;
    Q,phi2:=AbelianGroup(Q1);
    detQ:=hom<Q->UN | [ Determinant((Q.i @@ phi2) @@ phi1) @@ iotaN : i in [1..Ngens(Q)]] >;
    K:=Kernel(detQ);
    U:=detQ(Q);
    m:=2^Valuation(N,2);
    Um,iotam:=UnitGroup(Integers(m));
    redm:=hom<UN->Um | [ (Integers(m)!iotaN(UN.i))@@ iotam : i in [1..Ngens(UN)] ]>;            
    S:=(sub<Um|[(-1)@@iotam]> @@ redm) meet U;  //2-torsion subgroup

    C,phiC:=quo<U|S>;
    assert IsCyclic(C);
    if #C ne 1 then
        c:=AbelianBasis(C)[1];
        u0:=c@@phiC;
        e:=Minimum({Order(u0+s) : s in S });
        u:=Rep({u0+s: s in S | Order(u0+s) eq e});

        if e gt Order(c) then
            G1:=GL2Lift(G,N*2);  
            W1:=SL2Lift(W,N*2);    
            return FindSpecialSubgroup(G1,W1);
        end if;
    
        g0:=u @@ detQ;

        done:=false;
        for k in K do
            if Order(g0+k) eq Order(u) then
                done:=true;
                g:=g0+k;
                break k;
            end if;
        end for;

        if not done then
            G1:=GL2Lift(G,N*2); 
            W1:=SL2Lift(W,N*2);    
            return FindSpecialSubgroup(G1,W1);
        end if;

        g:=(g @@ phi2) @@ phi1;
        gens1:=[g];
    else
        gens1:=[];
    end if;

    V:={u: u in S | exists{g: g in Q | detQ(g) eq u and Order(u) eq Order(g)} };
    subgroups_S:=[H`subgroup: H in Subgroups(S)];
    ord:=[#H: H in subgroups_S]; 
    ParallelSort(~ord,~subgroups_S);
    subgroups_S:=Reverse(subgroups_S);    // The groups should be ordered by cardinality

    ord:=[#H: H in subgroups_S]; 
    assert Reverse(ord) eq Sort(ord);

    for H in subgroups_S do
        if {g: g in H} subset V then
            S0:=H;
            break H;
        end if;
    end for;
    
    basis_S0,I:=AbelianBasis(S0);
    C:=[];
    for u in basis_S0 do
        C:=C cat [ Rep({g: g in Q | detQ(g) eq u and Order(u) eq Order(g)}) ];
    end for;
    gens2:=[(c @@ phi2) @@ phi1: c in C];
    gens2:=[GL(2,Integers(N))!c: c in gens2];
    
    // Odd part.
    basis,I :=PrimaryAbelianBasis(UN);
    basis:=[basis[i]: i in [1..#I] | IsOdd(I[i])];
    gens3:=[];
    for b0 in basis do
        b:=Integers(N)!iotaN(b0);
        gens3:=gens3 cat [GL(2,Integers(N))![b,0,0,b]];
    end for;
        
    gens4:=[g: g in Generators(W1)];

    B:=sub<GL(2,Integers(N))| gens4 cat gens3 cat gens2 cat gens1>;
    //time b:=W1 eq B meet SL(2,Integers(N));  // check
    return B;
end function;



//By Zywina
function FindCommutatorSubgroupSL(G)
    /* 
        Input:
            G: a subgroup of SL(2,Z/NZ) for some N>1

        Taking the inverse image under the reduction modulo N map, we may view G as an open subgroup of SL(2,Z_N),
        where Z_N is the ring of N-adic integers.
        Let [G,G] be the commutator subgroup of G; it is an open subgroup of SL(2,Z_N).

        Output:
            M:      the level of [G,G] in SL(2,Z_N)
            gens:   generators for the image of [G,G] modulo M
            index:  index of [G,G] in SL(2,Z_N).
    */
    G`SL:=true;  //TODO: dangerous?
    N:=#BaseRing(G);
    P:=PrimeDivisors(N);

    // First consider the prime power case
    if #P eq 1 then
        p:=P[1];
        
        M:=SL2Level(G);
        // Deal directly with the case M=1
        if M eq 1 then
            if p eq 2 then
                return 4, [[3,1,3,0], [2,3,3,1]], 4;
            elif p eq 3 then
                return 3, [[2,2,2,1], [0,1,2,0], [2,0,0,2]], 3;
            else
                return 1, [], 1;
            end if;
        end if;

        G:=SL2Project(G,M);
        if M eq 2 then M:=4; G:=SL2Lift(G,4); end if; 

        repeat
            G_M:=SL2Lift(G,M);     
            S:=CommutatorSubgroup(G_M); S`SL:=true;
       
            G_Mp:=SL2Lift(G,M*p);
            Sp:=CommutatorSubgroup(G_Mp);  Sp`SL:=true;

            i_M:=SL2Index(S);   
            i_Mp:=SL2Index(Sp); 
            
            if  i_M ne i_Mp then
                M:=M*p;
            end if;        
        until i_M eq i_Mp;
    
        M:=SL2Level(S); 
        if M eq 1 then return 1, [], 1; end if;

        gens:= [Eltseq( SL(2,Integers(M))!g ): g in Generators(S)];
        return M, gens, i_M;          
    end if;

    // When N is not a prime power, we first find an integer M that is divisible by the level of [G,G].
    // We go prime by prime and use the above computations.
    M:=1;
    for p in P do
        q:= p^Valuation(N,p);
        m:= N div q;

        phi:=hom<G->SL(2,Integers(m))| [ChangeRing(G.i,Integers(m)): i in [1..Ngens(G)]]>;
        B:=ChangeRing(Kernel(phi),Integers(q));
        //  B x {I} is a subgroup of GL(2,Z/q) x GL(2,Z/m) = GL(2,Z/N)
        Mp,_,_:=FindCommutatorSubgroupSL(B);        
        M:=M*Mp;
    end for;
    // The level of [G,G] divides M.
    G_:=SL2Lift(G,LCM([M,N]));  
    G_:=SL2Project(G_,M);  
    S:=CommutatorSubgroup(G_);  // have lifted group so that this will be the desired commutator subgroup
    S`SL:=true;

    M,S:=SL2Level(S);
    gens:= [Eltseq(g): g in Generators(S)];
    index:=SL2Index(S);

    return M, gens, index; 
end function;


function ContainsScalars(G)
    // For a subgroup of GL(2,Z/N) with N>1, return true if G contains all the scalar matrices and false otherwise.
    N:=#BaseRing(G);
    GL2:=GL(2,Integers(N));
    U,iota:=UnitGroup(Integers(N));
    return &and [ (GL2![iota(U.i),0,0,iota(U.i)]) in G : i in [1..Ngens(U)] ];
end function;


// Based on SZ.
// Given a subgroup H of SL(2,Z/nZ), returns a (possibly empty) list of subgroups G of GL(2,Z/nZ) of level n
// for which gl2DetIndex(G)=1 and ContainsScalars(G) and G meet SL(2,Z/nZ) eq H
function gl2QImagesFromSL2eray(H)
    GL2:=GL2Ambient(#BaseRing(H));
    SL2:=SL2Ambient(#BaseRing(H));
    assert H subset SL2;
    G0:=AdjoinScalars(H);
    if SL2Order(SL2Intersection(G0))/SL2Order(H) gt 1 then return []; end if;
    N:=Normalizer(GL2,G0);
    Q,pi:=quo<N|G0>;
    S0:=SL2Intersection(N); 
    S1:=pi(S0);
    MM:=[M`subgroup: M in Subgroups(Q)];
    MM:=[M: M in MM | #(M meet S1) eq 1];
    S:=[Inverse(pi)(K) : K in MM];
    return [G: G in S | GL2DeterminantIndex(G) eq 1 and ContainsScalars(G) and SL2Order(SL2Intersection(G))/SL2Order(H) eq 1];
end function;



//This is a function to find the families by finding the groups in calG meet SL2/[calG,calG].


function gl2QImagesForFamiliiesEray(GGG,H)
    GGG`SL:=true;
    H`SL:=true;
    N1:=SL2Level(GGG);
    if N1 eq 1 then N1:=2; end if;
    N2:=SL2Level(H);
    if N2 eq 1 then N2:=2; end if;
    N:=LCM([N1,N2]);
    GGG:=SL2Lift(SL2Project(GGG,N1),N);
    H:=SL2Lift(SL2Project(H,N2),N);
    assert H subset GGG;
    Q,pi:=quo<GGG|H>;
    S:=[Inverse(pi)(K`subgroup) : K in Subgroups(Q)];
    return [T: T in S];
end function;


//First family is the family of Serre Curves.
//Second family is the family consisting of j-line.


intrinsic FindAllFamilies(r::Rec, genus::RngIntElt) -> SeqEnum
{Given a Congruence subgroup (given as a record in CP database) this function returns a list of records of families that arise from the record r, that have genus at most genus.}
    if r`genus gt genus then return []; end if;
    if r`level ne 1 then 
        level:=r`level;
        matgens:=r`matgens;
    else
        level:=2;
        matgens:=[[1,1,0,1],[1,0,1,1]];
    end if;
    SL2:=SL2Ambient(level);
    H0:=sub<SL2|matgens>; H0`SL:=true;
    assert SL2![-1,0,0,-1] in H0;

    M1,gens1,index1:=FindCommutatorSubgroupSL(H0);
    H1:=SL2Lift(H0,M1); 
    Q1,iota1:=quo< H1 | sub<SL(2,Integers(M1))|gens1> >;

    M2:=1;
    if GCD(M1,2) eq 1 then M2:=M2*4; end if;
    if GCD(M1,3) eq 1 then M2:=M2*3; end if;
    if M2 ne 1 then
        Q2,iota2:=quo<SL2Ambient(M2) | CommutatorSubgroup(SL2Ambient(M2)) >;
    else
        M2:=2;
        Q2,iota2:=quo<SL(2,Integers(2)) | SL(2,Integers(2)) >; 
        // This is just the trivial group.  Really want M1=1, but magma doesn't like matrices in M_2(Z/(1)).
    end if;    

    Q,alpha:=DirectProduct(Q1,Q2);  // This group is isomorphic to H/[H,H]
    assert IsAbelian(Q);

    M:=LCM(M1,M2);
    H:=SL2Lift(H0,M);

    iota:=hom<H->Q | [ alpha[1](iota1(H.i)) * alpha[2](iota2(H.i)) : i in [1..Ngens(H)] ] >;

    assert #Q*SL2Index(H)/index1 eq #Q2;
    //Okay makes sense -Eray
    //comm_map[r`name]:=iota;
    //comm_level[r`name]:=M;  
     
     
    if r`level eq 1 then
        N0:=2;
        SL2:=SL2Ambient(N0);
        matgens:=[[1,1,0,1],[1,0,1,1]];
    else
        N0:=r`level;
        matgens:=r`matgens;
        SL2:=SL2Ambient(N0);
    end if;
    H:=sub<SL2|matgens>;
    H`SL:=true;
    assert SL2![-1,0,0,-1] in H;
    N1:=2*LCM([12,N0]);
    HH:=SL2Lift(H,N1);
    AllAgreeableGroups:=AssociativeArray();
    a:=1;
    R:=gl2QImagesFromSL2eray(HH); 
    for group in R do
        HG:=HH;
        G:=group;
        assert SL2Intersection(G) eq HG;
        assert #BaseRing(G) eq #BaseRing(HG);
        HG`Genus:=r`genus;
        G`Genus:=r`genus;
        aa:=GL2Order(G);

        N:=GL2Level(G);
        HGlevel:=SL2Level(HG);
        assert IsDivisibleBy(N,HGlevel);
        CPname:=r`name;
        if N eq 1 then 
            Hc:=CommutatorSubgroup(GL(2,Integers(2)));
            Hc`SL:=true;
            level1:=true;
            AllAgreeableGroups[a]:=<G,HG,Hc,CPname,level1>;
            a:=a+1;
            continue group;
        end if;

        G:=GL2Project(G,N);
        HG:=SL2Project(HG,N);
        assert SL2Intersection(G) eq HG;
        HG:=SL2Project(HG,HGlevel);
        phi:=iota;
        Q:=Codomain(phi);
        G1:=GL2Project(GL2Lift(G,LCM(N,M)), M);
        
    
        // Compute Hc=[G,G]
        found:=false;
        W:=sub<Q|{ phi(a*b*a^(-1)*b^(-1)): a,b in Generators(G1)}>;
        Hc:=W @@ phi; 
        while not found do
            Hc:=W @@ phi;
            found:=true;
            for g in Generators(G1) do
                W_:=sub<Q|{phi(g*h*g^(-1)) : h in Generators(Hc)}>;
                if W_ ne W then
                    W:=sub<Q|Generators(W) join Generators(W_)>;
                    found:=false;
                    break g;
                end if;
            end for;
        end while;
        Hc`SL:=true;
        D:=SL2Level(Hc);
        
        Hc:=SL2Project(Hc,D);
        if not Set(PrimeDivisors(N)) subset Set(PrimeDivisors(#BaseRing(Hc))) then continue group; end if;
        level1:=false;
        AllAgreeableGroups[a]:=<G,HG,Hc,CPname,level1>;
        a:=a+1;
    end for;

"Find Potential Family Records";
FAM1:=AssociativeArray();
level1things:=0;
for k in Keys(AllAgreeableGroups) do
    if AllAgreeableGroups[k][5] then
        level1things:= level1things +1;
        N0:=2;
        SL2:=SL(2,Integers(N0));
        matgens:=[[1,1,0,1],[1,0,1,1]];
        R:=gl2QImagesForFamiliiesEray(sub<SL(2,Integers(2))|matgens>,CommutatorSubgroup(GL(2,Integers(2))));
    else
        H:=AllAgreeableGroups[k][2];
        Hc:=AllAgreeableGroups[k][3];
        H`SL:=true;
        Hc`SL:=true;
        if not SL2ContainsNegativeOne(H) then continue k; end if;
        R:=gl2QImagesForFamiliiesEray(AllAgreeableGroups[k][2],AllAgreeableGroups[k][3]);
    end if;
       
        FAM1[k]:=<AllAgreeableGroups[k],R>; //second coordinate is group and third coordinate is key. Frist coordinate are the list above.
end for;


"Creating Family Records for those satisfying the correct genus.";
BS:=AssociativeArray();
a:=1;
for k in Keys(FAM1) do
    if FAM1[k][2] eq [] then continue;
    else
        for i in [1..#FAM1[k][2]] do
            g:=GL2Genus(FAM1[k][2][i]);
            if g gt genus then continue i; //change g gt x accordingly//GEEEEEEEEEEEEENUSSSSSSSSSSSSSSSSSSSSS
            else 
                BS[a]:=CreateFamilyUnivRec(FAM1[k][1][1],FAM1[k][2][i],FAM1[k][1][3],FAM1[k][1][2],FAM1[k][1][4]); //first coordinate is B, second is calG, third one is calG's key in CP
                a:=a+1;
            end if;
        end for;
    end if;
end for;
"Fixing the levels";
for k in Keys(BS) do
    if BS[k]`calG_level eq 1 then 
         BS[k]`calG:=GL2Project(BS[k]`calG,2); 
         if BS[k]`B_level eq 1 then BS[k]`B`SL:=true; BS[k]`B:=SL2Project(BS[k]`B,2); end if;  
    else
    BS[k]`B`SL:=true;
    BS[k]`calG:=GL2Project(BS[k]`calG,BS[k]`calG_level);  
    BS[k]`B:=SL2Project(BS[k]`B,BS[k]`B_level);  
    end if;

end for;    


FAM:=BS;



"Finding Representatives with full determinant";
for k in Keys(FAM) do
    if not assigned FAM[k]`H then
        FAM[k]`B`SL:=true;
        H:=FindSpecialSubgroup(FAM[k]`calG,FAM[k]`B);
        if GL2DeterminantIndex(H) eq 1 then 
            if GL2Level(H) eq 1 then FAM[k]`H:=GL2Project(H,2); else            
            FAM[k]`H:=GL2Project(H,GL2Level(H)); end if;
        end if;
    end if;
end for;


print(#FAM);


"Getting rid of redundant families";
for k in Keys(FAM) do
    F:=FAM[k];
    calG:=F`calG;
    B:=F`B;
    if F`calG_level eq 1 or F`B_level eq 1 then continue; end if;
    N:=LCM([F`calG_level,F`B_level]);

    calG:=GL2Lift(calG,N);
    B`SL:=true;
    B:=SL2Lift(B,N);
    GL2:=GL2Ambient(N);

    norm:=Normalizer(GL2,calG);
    A:=[s: s in Conjugates(norm,B)];
    conjs:=[];
    for i in [1..#A] do
        a,s:=GL2Level(A[i]);
        conjs:= conjs cat [s];
    end for; 
    FAM[k]`conjugacyofB:=conjs;//Be careful about the levels

end for;


keys:=Keys(FAM);
allthekeysneeded:={};
removed:={};
for k in Keys(FAM) do
    if k in removed then continue k; end if;
    F:=FAM[k];
    calG:=F`calG;
    B:=F`B;
    if F`calG_level eq 1 or F`B_level eq 1 then continue; end if;
    for t in Keys(FAM) do
        if t eq k then continue t; end if;
        if FAM[t]`calG_level eq 1 or FAM[t]`B_level eq 1 then continue t; end if;
        if F`calG_level eq FAM[t]`calG_level and F`B_level eq FAM[t]`B_level and F`genus eq FAM[t]`genus and calG eq FAM[t]`calG then
            N:=LCM([F`calG_level,F`B_level]);
            calG1:=GL2Lift(calG,N);
            B`SL:=true;
            B:=SL2Lift(B,N);
            GL2:=GL2Ambient(N);
            //norm:=Normalizer(GL2,calG1);
            Bt:=FAM[t]`B;
            Bt`SL:=true;
            Bt:=SL2Lift(Bt,N);
            for i in [1..#FAM[k]`conjugacyofB] do
                Bi:=FAM[k]`conjugacyofB[i];
                Bi`SL:=true;
                Bi:=SL2Lift(Bi,N);
                if  Bi eq Bt then
                    printf "key %o is redundant!\n",t;
                    keys:= keys diff {t};
                    removed:=removed join {t};
                end if;
            end for;
        end if;

    end for;


end for;

redundant:=removed;
NonRedFam:=AssociativeArray();

for k in Keys(FAM) do 
    if k in redundant then continue k; end if;

    NonRedFam[k]:=FAM[k];
end for;

FAM:=NonRedFam;

printf "There are %o families\n", #FAM;
"Computing the models";
for k in Keys(FAM) do
    if assigned FAM[k]`H then
        G:=FAM[k]`H;
        calG:=FAM[k]`calG;
        if #BaseRing(G) eq 2 and #BaseRing(G) eq #BaseRing(calG) and G eq calG then continue; end if; //The family consisting of only the j line.
        if assigned G`SL then delete G`SL; end if;
        if assigned calG`SL then delete calG`SL; end if;
        if not GL2ContainsNegativeOne(calG) then continue k; end if;
        if not GL2ContainsNegativeOne(G) then continue k; end if;
        //printf "Making the model\n";
        M:=CreateModularCurveRec(G);
        //printf "Computing the model\n";
        M:=FindModelOfXG(M: G0:=calG);
        FAM[k]`M:=M;
        if not GL2Level(calG) eq 1 then 
        MG:=CreateModularCurveRec(calG);
        MG:=FindModelOfXG(MG);
        FAM[k]`calGModCurve:=MG;
         end if;
        //"Computing AutOfMF";
        H:=G;
        calG:=GL2Lift(calG,LCM([#BaseRing(calG),#BaseRing(H)]));
        M:=IncreaseModularFormPrecision(M,[Maximum(M`prec[i]+2,((M`prec_sturm[i]-1) * (M`sl2level div M`widths[i]))+5) : i in [1..M`vinf]]);
        for i in [1..Ngens(calG)] do
            FAM[k]`AOfMF[i]:=AutomorphismOfModularForms(M,M`F0,calG.i);
        end for;    

    end if;
end for;



"Computing the Jmaps";
for k in Keys(FAM) do 
    if assigned FAM[k]`H and GL2ContainsNegativeOne(FAM[k]`H) then
         G:=FAM[k]`H;
        calG:=FAM[k]`calG;
        if #BaseRing(G) eq 2 and #BaseRing(G) eq #BaseRing(calG) and G eq calG then continue; end if;
        M:=FAM[k]`M;
        C, jmap, model_type, F0, M1,mind,maxd, maxprec:=AbsoluteJmap(M);
        FAM[k]`jmap:=jmap;
        FAM[k]`model_type:=model_type;
        FAM[k]`M:=M1;
        FAM[k]`mind:=mind;
        FAM[k]`maxd:=maxd;
        FAM[k]`maxprec:=maxprec;
    end if;
end for;




"Computation for the gonality 2 modular curves";
for k in Keys(FAM) do
    if assigned FAM[k]`H and GL2ContainsNegativeOne(FAM[k]`H) then
         G:=FAM[k]`H;
        calG:=FAM[k]`calG;
        if #BaseRing(G) eq 2 and #BaseRing(G) eq #BaseRing(calG) and G eq calG then continue; end if;
     if FAM[k]`M`CPname in gonality_equals_2 then
        FAM[k]`CanModelForHyp:=FindCanonicalModel(CreateModularCurveRec(FAM[k]`H));
    end if; 
    end if;
end for;


for k in Keys(FAM) do
    if assigned FAM[k]`H and assigned FAM[k]`CanModelForHyp then
        H:=FAM[k]`H;
        calG:=FAM[k]`calG;
        FAM[k]`AOfMFCanModel:=AssociativeArray();
        if assigned H`SL then delete H`SL; end if;
        if assigned calG`SL then delete calG`SL; end if;
        M:=FAM[k]`CanModelForHyp;
        calG:=GL2Lift(calG,LCM([#BaseRing(calG),#BaseRing(H)]));
        M`H`SL:=true;
        M:=IncreaseModularFormPrecision(M,[Maximum(M`prec[i]+1,((M`prec_sturm[i]-1) * (M`sl2level div M`widths[i]))+5) : i in [1..M`vinf]]);
        for i in [1..Ngens(calG)] do
            FAM[k]`AOfMFCanModel[i]:=AutomorphismOfModularForms(M,M`F0,calG.i);
        end for;    
    end if;
end for;
"Computing wthe fine families";

for k in Keys(FAM) do
    if assigned FAM[k]`H then FAM[k]`fine:= not GL2ContainsNegativeOne(FAM[k]`H); end if;
    if assigned FAM[k]`fine and FAM[k]`fine eq true then FAM[k]`correspondingCoarse:=GL2IncludeNegativeOne(FAM[k]`H); end if;

end for; 


"Done!";


return [FAM[k]: k in Keys(FAM)];
end intrinsic;

