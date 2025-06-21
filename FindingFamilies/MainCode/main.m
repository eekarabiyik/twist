//This is a rudimantary version of the Twisting Code. The j-map is included, as well as a boolean for being QQ-gonality 2
//The final polynomials are ugly in the sense that there are many unnecessary cubic relations.
//However it is very fast and uses the last version of GL2 magma intrinsics. This will be updated soon. 

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


//Fix this 
intrinsic FindModel(G::GrpMat, T::GrpMat, FAM::SeqEnum, parentcan : redcub:=true, test_hyperelliptic:=true) -> SeqEnum[RngMPolElt], AlgMatElt, SeqEnum, BoolElt, RngIntElt,Any
{
    Input:
    - G is a subgroup of GL2(Zhat). It is given by a subgroup of GL2(Z/NZ) where N is a multiple of the level of G.
    - T is the intersection of G with SL2(Z/NZ)

    Keywords:
    - redcub, whether to reduce the cubics (passed on to TwistCurve)
    - test_hyperelliptic, test if X_G is hyperelliptic over Q

    Output:
    - psi: homogeneous polynomials in Q[x_1,..x_n] defining the curve X_G mentioned above.
      n depends on the model of the family representative used to twist G from.
    - MAT: H90 matrix describing the twist from the family representative to G.
    - a sequence of length 2 giving the numerator and denominator of the absolute j-map
    - a boolean, whether X_G is hyperelliptic over Q (only returned if test_hyperelliptic is true)
    - the genus of X_G
}

    //We first start with finding the family in our database that contains G.
    print("Finding the family...");
    //famkey,famG,Gcong,calGlift,Tcong:=FamilyFinderWithCusps(G,T,FAM);
    famkey,famG,Gcong,calGlift,Tcong:=FamilyFinderCanon(G,T,FAM,parentcan);
    printf "The family key in the database is %o\n",famkey;
    AOfMF:=AssociativeArray();
    for i in Keys(famG`AOfMF) do
        AOfMF[i]:=Transpose(famG`AOfMF[i]);
    end for;
    Tcong`SL:=true;
    if famG`extra1 then
        "IN WAWA!!!";
        printf "Computing the cocycle\n";
        xi,K:=GroupToCocycleProj(famG`calG,famG`H,Gcong,Tcong,AOfMF);
        xinew:=map<Domain(xi)->GL(3,K)| [<t,mat3map(xi(t))>: t in Domain(xi)]>;
        Pol<[x]>:=PolynomialRing(Rationals(),3);
        PP:=ProjectiveSpace(Rationals(),2);
        pis:=[Pol!(x[2]^2-x[1]*x[3])];
        psi,MAT:=TwistCurveGenus0(pis,xinew,K: redcub:=redcub);
        if assigned famG`RelativeJMap then
            L:=famG`RelativeJMap;
        else 
            L:=famG`jmap;
        end if;
        newL:=[];
        for ji in L do
            newL:= newL cat [Evaluate(ji,[x[2],x[3]])];
        end for;
        relmap:= PolynomialTwister(newL, MAT, K);
    else
        printf "Computing the cocycle\n";
        xi,K:=GroupToCocycleProj(famG`calG,famG`H,Gcong,Tcong,AOfMF);//This will be the main one from now on. much much faster!
        //Now the twist
        printf "Twisting the curve...\n";
        psi,MAT,_,unrefined:=TwistCurve(famG`M`psi,xi,K: redcub:=redcub);
        //Now we compute the jmap. Need to do Galois descent to have rational coefficents. So a little messy
        if assigned famG`RelativeJMap then
            L:=famG`RelativeJMap;
        else 
            L:=famG`jmap;
        end if;
        relmap:= PolynomialTwister(L, MAT, K);
    end if;
    //Computing the cocycle related to H and G. See the paper for details. (Paper is not out yet so look at the file)

    printf "Computing the jmap...\n";
    //Computing the jmap. The jmap of the representative is precomputed.

   
    if not test_hyperelliptic then
        return psi,MAT,relmap,/*famG`JmapcalG,*/    _,_,_,_,unrefined;
    end if;
   



    printf "Computing QQ-gonality...\n";
    //Following computes if the curve is hyperelliptic
    if famG`M`CPname in gonality_equals_2 then
        assert assigned famG`CanModelForHyp;
        gonmodel:=famG`CanModelForHyp;
        gonAOfMF:=AssociativeArray();
        for i in Keys(famG`AOfMFCanModel) do
            gonAOfMF[i]:=Transpose(famG`AOfMFCanModel[i]);
        end for;
        xi,K:=GroupToCocycleProj(famG`calG,famG`H,Gcong,Tcong,gonAOfMF);
        gonpsi,gonMAT:=TwistCurve(gonmodel`psi,xi,K);
        Pol<x>:=Parent(gonpsi[1]);
        PP:=ProjectiveSpace(Rationals(),#VariableWeights(Pol)-1);
        C:=Curve(PP,gonpsi);
        C,mapo:=Conic(C);
        T:=HasRationalPoint(C);
        return psi,MAT,relmap,/*famG`JmapcalG,*/ T,famG`genus,K,famkey,unrefined;
    end if;
    return psi,MAT,relmap,/*famG`JmapcalG,*/false,famG`genus,K,famkey,unrefined;
end intrinsic;
