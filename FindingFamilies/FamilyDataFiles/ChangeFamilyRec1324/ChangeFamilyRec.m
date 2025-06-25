AttachSpec("./spec");
FAM:=LoadFamilies(["/homes/ek693/Main/Fam24.dat"]);
FAM:=[FAM[k]: k in Keys(FAM)|FAM[k]`genus gt 12];
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

//FAM:=[FAM[k]: k in Keys(FAM)| FAM[k]`genus le 6 and FAM[k]`fine eq true];
FAM1:=AssociativeArray();
for k in Keys(FAM) do
    //if FAM[k]`genus gt 20 then continue; end if;
    print(k);
    FAM1[k]:= CreateFamilyUnivRec(FAM[k]`calG, FAM[k]`B, FAM[k]`commutator_sub, FAM[k]`W, FAM[k]`CPname);
  
    if assigned FAM[k]`calG_level then FAM1[k]`calG_level:=FAM[k]`calG_level; end if;
    if assigned FAM[k]`B_level then FAM1[k]`B_level:=FAM[k]`B_level; end if;
    if assigned FAM[k]`genus then FAM1[k]`genus:=FAM[k]`genus; end if;
    if assigned FAM[k]`sl2level then FAM1[k]`sl2level:=FAM[k]`sl2level; end if;
    if assigned FAM[k]`level then FAM1[k]`level:=FAM[k]`level; end if;
    if assigned FAM[k]`k then FAM1[k]`k:=FAM[k]`k; end if;
    if assigned FAM[k]`prec then FAM1[k]`prec:=FAM[k]`prec; end if;
    if assigned FAM[k]`commutator_index then FAM1[k]`commutator_index:=FAM[k]`commutator_index; end if;
    if assigned FAM[k]`maxprec then FAM1[k]`maxprec:=FAM[k]`maxprec; end if;
    if assigned FAM[k]`model_type then FAM1[k]`model_type:=FAM[k]`model_type; end if;
    if assigned FAM[k]`maxd then FAM1[k]`maxd:=FAM[k]`maxd; end if;
    if assigned FAM[k]`mind then FAM1[k]`mind:=FAM[k]`mind; end if;
    if assigned FAM[k]`calG_gens then FAM1[k]`calG_gens:=FAM[k]`calG_gens; end if;
    if assigned FAM[k]`B_gens then FAM1[k]`B_gens:=FAM[k]`B_gens; end if;
    if assigned FAM[k]`subgroupsofH then FAM1[k]`subgroupsofH:=FAM[k]`subgroupsofH; end if;
    
    if assigned FAM[k]`calGModCurve then FAM1[k]`calGModCurve:=FAM[k]`calGModCurve; end if;
    if assigned FAM[k]`AOfMF then FAM1[k]`AOfMF:=FAM[k]`AOfMF; end if;
    if assigned FAM[k]`quomap then FAM1[k]`quomap:=FAM[k]`quomap; end if;
    if assigned FAM[k]`quogroup then FAM1[k]`quogroup:=FAM[k]`quogroup; end if;
    if assigned FAM[k]`dataforquotient then FAM1[k]`dataforquotient:=FAM[k]`dataforquotient; end if;
    if assigned FAM[k]`conjugacyofB then FAM1[k]`conjugacyofB:=FAM[k]`conjugacyofB; end if;
    if assigned FAM[k]`AOfMFCanModel then FAM1[k]`AOfMFCanModel:=FAM[k]`AOfMFCanModel; end if;
    if assigned FAM[k]`CanModelForHyp then FAM1[k]`CanModelForHyp:=FAM[k]`CanModelForHyp; end if;
    if assigned FAM[k]`H then FAM1[k]`H:=FAM[k]`H;  end if;

    if assigned FAM[k]`fine then 
        FAM1[k]`fine:=FAM[k]`fine; 
    else
        if assigned FAM1[k]`H then
            FAM1[k]`fine := not GL2ContainsNegativeOne(FAM1[k]`H);
        end if;
    end if;

    if assigned FAM[k]`label then FAM1[k]`agreeable_label:=FAM[k]`label; end if;
    if assigned FAM[k]`parentcalG then FAM1[k]`parentcalG:=FAM[k]`parentcalG; end if;
    if assigned FAM[k]`H and assigned FAM[k]`index then FAM1[k]`index:=FAM[k]`index; else
    if assigned FAM[k]`H then FAM1[k]`index:=GL2Index(FAM[k]`H); end if;     end if;
    if assigned FAM[k]`extra1 then FAM1[k]`extra1:=FAM[k]`extra1; end if;

    if assigned FAM[k]`H and assigned FAM[k]`numberofcusps then FAM1[k]`numberofcusps:=FAM[k]`numberofcusps; else
    if assigned FAM[k]`H then FAM1[k]`numberofcusps:=GL2CuspCount(FAM[k]`H);end if; end if;
    
    if assigned FAM[k]`calG_index then FAM1[k]`calG_index:=FAM[k]`calG_index; else
    FAM1[k]`calG_index:=GL2Index(FAM[k]`calG); end if;

    if assigned FAM[k]`oneelement then FAM1[k]`oneelement:=FAM[k]`oneelement; else
        if assigned FAM1[k]`H and assigned FAM1[k]`fine and FAM1[k]`fine eq false and #BaseRing(FAM1[k]`H) eq #BaseRing(FAM1[k]`calG) and FAM1[k]`calG eq FAM1[k]`H then
            FAM1[k]`oneelement:=true;
        else 
            FAM1[k]`oneelement:=true;
        end if;
    end if;

    //Maps and models
    if assigned FAM[k]`M then

            if assigned FAM[k]`jmap then FAM1[k]`jmap:=FAM[k]`jmap; end if;
            if assigned FAM[k]`M then FAM1[k]`M:=FAM[k]`M; end if;
            if assigned FAM[k]`RelativeJMap then FAM1[k]`RelativeJMap:=FAM[k]`RelativeJMap; end if;

    end if;

    if assigned FAM[k]`calG_cangen then FAM1[k]`calG_cangen:=FAM[k]`calG_cangen; end if;
    if assigned FAM[k]`H_cangen then FAM1[k]`H_cangen:=FAM[k]`H_cangen; end if;




end for;



I:=Open("/homes/ek693/Main/FindingFamilies/FamilyDataFiles/ChangeFamilyRec1324/FamiliesGenus1324.dat", "w");
    for k in Keys(FAM1) do
        x:=FAM1[k];
        WriteObject(I, x);
    end for;
