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



intrinsic FindModel(G::GrpMat, T::GrpMat, FAM::SeqEnum: redcub:=true, test_hyperelliptic:=true,already_conjugated:=false,onefamily:=false, use_agg_label:=false, use_family_label:=false, agreeable_label:="", family_label:="", use_parent_can:=false, parentcan:=[],verbose:=false) -> SeqEnum[RngMPolElt], AlgMatElt, SeqEnum, BoolElt, RngIntElt,Any
{
    Input:
    - G is a subgroup of GL2(Zhat). It is given by a subgroup of GL2(Z/NZ) where N is a multiple of the level of G.
    - T is the intersection of G with SL2(Z/NZ)
    - FAM is the list of families as outputed by FindAllFamilies

    Keywords:
    - redcub, whether to reduce the cubics (passed on to TwistCurve)
    - test_hyperelliptic, test if X_G is hyperelliptic over Q

    Output:
    //psi: the equations in a projective space
    //MAT: H90 matrix used
    //relmap: the relative or absoltue jmap
    //rel: if the relative jmap is computed or not, boolean. If false then the absolute j-map is computed. If it is a string then it states that no j-map is computed
    //qgon2: if true then it has Q gonality 2, If false Q gonality 4. Otherwise not geometrically hyperelliptic
    //genus: genus
    //K: the number field over which the modular curve is isomorphic to therepresentative curce in the family
    //famG: family record that the curve is in
    //Gcong: Group G conjugated into the family
    //MFAM: the modular curve record of the representative
    //gonMAT: H90 matrix used for the Gonality 2 comptuation
    //Tcong: T conjugated into the family
    //oneelement : if the curve lies in a one element family i.e., if it is agreeable
    //parentcalG: the parent of the agreeable closure. If it is empty then one should use the absolute j-maps
    //extra: Boolean indicating if the curve lies in a genus 0 family consisting entirely of P^1s.
    //MAT1: if extra then the associated H90 matrix?
}

    //We first start with finding the family in our database that contains G.
    if verbose then print("Finding the family..."); end if;
    //famkey,famG,Gcong,calGlift,Tcong:=FamilyFinderWithCusps(G,T,FAM);

    //We find the family G lies in. Depending on the information input we use different methods.
    if already_conjugated and onefamily then
        Gcong:=G; Tcong:=T; famG:=FAM[1]; 
    elif use_agg_label then 
        famkey,famG,Gcong,calGlift,Tcong:=FamilyFinderCanon(G,T,FAM,parentcan:agreeable_label:=agreeable_label, use_agg_label:=use_agg_label);
    elif use_family_label then
        famkey,famG,Gcong,calGlift,Tcong:=FamilyFinderCanon(G,T,FAM,parentcan:family_label:=family_label, use_family_label:=use_family_label);
    elif use_parent_can then 
        famkey,famG,Gcong,calGlift,Tcong:=FamilyFinderCanon(G,T,FAM,parentcan: use_parent_can:=use_parent_can);
    else
        famkey,famG,Gcong,calGlift,Tcong:=FamilyFinderWithCusps(G,T,FAM);
    end if;
    oneelement:=famG`oneelement;
    parentcalG:=famG`parentcalG;
    if verbose then printf "The family key in the database is %o\n",famkey; end if;
    //AOfMF are the automorphisms induced by the agreeable closure on our model.
    AOfMF:=AssociativeArray();
    for i in Keys(famG`AOfMF) do
        //Initial computation was done in a different order.
        AOfMF[i]:=Transpose(famG`AOfMF[i]);
    end for;
    Tcong`SL:=true;

    //Ignore the commented parts. The genus 0 P^1 case has been proven so it is redundant.

    //extra1 means that the representative in the family is given by the equations []. To reasonably twist we embed it into the projective plane.
    // if famG`extra1 then
    //     if verbose then printf "Computing the cocycle\n"; end if;
    //     xi,K:=GroupToCocycleProj(famG`calG,famG`H,Gcong,Tcong,AOfMF);
    //     //xi;
    //     //K;
    //     _,MAT1:=TwistCurve(famG`M`psi,xi,K: redcub:=redcub);
    //     //"Before\n";
    //     //MAT1;
    //     xinew:=map<Domain(xi)->GL(3,K)| [<t,mat3map(xi(t))>: t in Domain(xi)]>;
    //     Pol<[x]>:=PolynomialRing(Rationals(),3);
    //     PP:=ProjectiveSpace(Rationals(),2);
    //     pis:=[Pol!(x[2]^2-x[1]*x[3])];
    //     if verbose then printf "Twisting the curve...\n"; end if;
    //     psi,MAT:=TwistCurveGenus0(pis,xinew,K: redcub:=redcub);
    //     //"Afterwards\n";
    //     //MAT;
    //     //extra5 means the relative jmaps and absolute jmaps are huge and should not twist them!
    //     if assigned famG`extra5 and famG`genus gt 6 then
    //         if famG`M`CPname in gonality_equals_2 then
    //             assert assigned famG`CanModelForHyp;
    //             gonmodel:=famG`CanModelForHyp;
    //             gonAOfMF:=AssociativeArray();
    //             for i in Keys(famG`AOfMFCanModel) do
    //                 gonAOfMF[i]:=Transpose(famG`AOfMFCanModel[i]);
    //             end for;
    //             xi,K:=GroupToCocycleProj(famG`calG,famG`H,Gcong,Tcong,gonAOfMF);
    //             gonpsi,gonMAT:=TwistCurve(gonmodel`psi,xi,K);
    //             Pol<x>:=Parent(gonpsi[1]);
    //             PP:=ProjectiveSpace(Rationals(),#VariableWeights(Pol)-1);
    //             C:=Curve(PP,gonpsi);
    //             C,mapo:=Conic(C);
    //             T:=HasRationalPoint(C);
    //             return psi,MAT,"no map computed!",_,/*famG`JmapcalG,*/ T,famG`genus,K,famG,Gcong,famG`M,gonMAT,Tcong,oneelement,parentcalG;
    //         else
    //             return psi,MAT,"no map computed!",_,/*famG`JmapcalG,*/    _,famG`genus,K,famG,Gcong,famG`M,_,Tcong,oneelement,parentcalG;
    //         end if;
    //     end if;
    //     //Computing the jmaps
    //     if verbose then printf "Computing the jmap...\n"; end if;
    //     //if the groups is agreeable we use precomputed jmaps.
    //     if famG`oneelement then
    //         rel:=true;//fix later
    //         if not assigned famG`JmapcalG then
    //             rel:=true;
    //             L:=famG`parentrelmapcalG;
    //             relmap:=L;
    //         else
    //             rel:=false;
    //             L:=famG`JmapcalG;
    //             relmap:=L;
    //         end if;
    //     else //if not agreeable we actually twist the jmaps
    //         if assigned famG`RelativeJMap and not assigned famG`extra3 then
    //             rel:=true;
    //             L:=famG`RelativeJMap;
    //              newL:=[];
    //             for ji in L do
    //                 newL:= newL cat [Evaluate(ji,[x[2],x[3]])];
    //             end for;
    //             relmap:= PolynomialTwister(newL, MAT, K);
    //             MAT:=MAT1;
    //         else 
    //             rel:=false;
    //             L:=famG`jmap;
    //              newL:=[];
    //             for ji in L do
    //                 newL:= newL cat [Evaluate(ji,[x[2],x[3]])];
    //             end for;
    //             relmap:= PolynomialTwister(newL, MAT, K);
    //             MAT:=MAT1;
    //         end if;
    //     end if;

    // else
        //Now we are in the generic case! Not genus 0!
        if verbose then printf "Computing the cocycle\n"; end if;
        xi,K:=GroupToCocycleProj(famG`calG,famG`H,Gcong,Tcong,AOfMF);
        //Now the twist
        if verbose then printf "Twisting the curve...\n"; end if;
        // BURA DEGISTI
        if famG`oneelement then
            psi:=famG`M`psi;
            if psi eq [] then 
                MAT:=Identity(MatrixRing(Rationals(), 2));
            else
                rr:=Rank(Parent(psi[1]));
                MAT:=Identity(MatrixRing(Rationals(), rr));
            end if;



        else

            psi,MAT:=TwistCurve(famG`M`psi,xi,K: redcub:=redcub);
        end if;



        if verbose then printf "Twisting the curve...\n"; end if;
        
        //Huge j-maps case
        if assigned famG`extra5 and famG`genus gt 6 then
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
                return psi,MAT,"no map computed!",_,/*famG`JmapcalG,*/ T,famG`genus,K,famG,Gcong,famG`M,gonMAT,Tcong,oneelement,parentcalG;
            else
                return psi,MAT,"no map computed!",_,/*famG`JmapcalG,*/    _,famG`genus,K,famG,Gcong,famG`M,_,Tcong,oneelement,parentcalG;
            end if;
        end if;
        //Now we compute the jmap. Need to do Galois descent to have rational coefficents.
        if verbose then printf "Computing the jmap...\n"; end if;
        //Computing the jmap. The jmap of the representative is precomputed.
        if famG`oneelement then
            rel:=true;//fix later
            if not assigned famG`JmapcalG then
                rel:=true;
                L:=famG`parentrelmapcalG;
                relmap:= PolynomialTwister(L, MAT, K);
            else
                rel:=false;
                L:=famG`JmapcalG;
                relmap:= PolynomialTwister(L, MAT, K);
            end if;
        else
            if assigned famG`RelativeJMap and not assigned famG`extra3 and not (famG`agreeable_label eq "2.3.0.a.1" or famG`agreeable_label eq "2.2.0.a.1" or famG`agreeable_label eq "2.6.0.a.1") then //extra3 indicates that the RelativeJmap is too big and the absolute j map is preferred.
                rel:=true;
                L:=famG`RelativeJMap;
                relmap:= PolynomialTwister(L, MAT, K);

            else 
                rel:=false;
                L:=famG`jmap;
                relmap:= PolynomialTwister(L, MAT, K);

            end if;
        end if;
    // end if;




   
    if not test_hyperelliptic then
        return psi,MAT,relmap,rel,/*famG`JmapcalG,*/    _,famG`genus,K,famG,Gcong,famG`M,_,Tcong,oneelement,parentcalG;
    end if;
   



    if verbose then printf "Computing QQ-gonality...\n"; end if;
    //Following computes if the curve is hyperelliptic. We basically twist the canonical model as above.
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
        return psi,MAT,relmap,rel,/*famG`JmapcalG,*/ T,famG`genus,K,famG,Gcong,famG`M,gonMAT,Tcong,oneelement,parentcalG;
    end if;



    return psi,MAT,relmap,rel,/*famG`JmapcalG,*/"not_hyperelliptic",famG`genus,K,famG,Gcong,famG`M,_,Tcong,oneelement,parentcalG;
end intrinsic;




intrinsic ComputePlaneModel(G::GrpMat, MAT,MFAM::Rec,psi::SeqEnum: giveup_time:=720)->Any
{Given the group, The H90 matrix obtained from FindModel, the representative modular curve and the equations of the curve, computes a list of planemodels for the modular curve}
    assert MFAM`genus gt 3 and not MFAM`CPname in gonality_equals_2;
        MFAM`H`SL:=true;
        cyclevel:=LCM([MFAM`N,#BaseRing(G)]);
        cyctop<o>:=CyclotomicField(cyclevel);
        cycG:=CyclotomicField(#BaseRing(G));
        M:=CreateModularCurveRec(G);
        MFF:=F0Twister(MFAM`F0, MAT^(-1),cyclevel);//Need galois descent coef by coef?
        if psi eq [] then s:=1; else s:=Rank(Parent(psi[1]))-1; end if;
        PP:=ProjectiveSpace(Rationals(),s);
        CG:=Curve(PP,psi);
        L:=PlaneModelsFromQExpansionsForm(M, CG, MFF:giveup_time:=giveup_time);
        return L;
end intrinsic;



