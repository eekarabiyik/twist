
//Assumes aggcolsure, index and genus
AttachSpec("./spec");
AttachSpec("./ModularCurves/equations/equations.spec");

SetColumns(0);
if assigned verbose or assigned debug then
    SetVerbose("User1", 1);
end if;
if assigned debug then
    SetDebugOnError(true);
end if;
if (not assigned label) then
    printf "This script assumes that label, the label of the X_H to compute, is given as a command line paramter.\n";
    printf "Something like magma label:=7.168.3.1 GetModelLMFDB.m\n";
    quit;
end if;

if (not assigned agreeable_closure) then
    printf "This script assumes that agreeable_closure, the agreeble closure of the X_H to compute, is given as a command line paramter.\n";
    quit;
end if;

if (not assigned generators) then
    printf "This script assumes that generators, the generators of the X_H to compute, is given as a command line paramter.\n";
    quit;
end if;


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

gonality_equals_3:=[ "54C5", "16A6", "18A6", "18D6", "24D6", "27A6", "28D6", "28E6", 
"30C6", "32A6", "36C6", "36H6", "36J6", "36K6", "39A6", "45D6", "54A6", "54B6", "56D6", 
"64A6", "84A6", "108A6", "27B7", "27C7", "30D7", "42M7", "24A8", "24B8", "36H8", "36I8", 
"36J8", "36K8", "48A8", "48C8", "48E8", "72F8", "72G8", "84A8", "96A8", "108A8", "108B8", 
"144A8", "15A10", "36A10", "36C10", "42G10", "72A10", "75A10", "108A10", "108C10", "108A12"];



//Setting up the inputs to our function.
level:=Split(label,".")[1];
index:=Split(label,".")[2];
genus:=Split(label,".")[3];
G:=sub<GL2Ambient(level)|generators>;
T:=SL2Intersection(G);


//Load a minimum number of families.
FAM:=LoadFamilies("/home/eekarabiyik/Families": genus:=genus, index:=index, agreeable_label:=agreeable_closure);
gonMAT:=0;
//Call the function
psi,MAT,relmap,rel,qgon2,genus,K,famG,Gcong,MFAM,gonMAT,Tcong,oneelement,calG_parent_label:=FindModel(G,T,FAM); 




//canonical model is 0 embedded model is 8
if MFAM`genus gt 2 and not MFAM`CPname in gonality_equals_2 then model_type:=0; else model_type:=8; end if; 


//Form the curve
if psi eq [] then 
    X:=Curve(ProjectiveSpace(Rationals(),1),[]); 
else
    rank:=Rank(Parent(psi[1]));
    Pol:=PolynomialRing(Rationals(),rank);
    psi:=[Pol!psi[i]: i in [1..#psi]];
    X := Curve(ProjectiveSpace(Rationals(),rank-1), psi); 
end if;
//Write the curve
LMFDBWriteXGModel(X,model_type,label);


//j is either relative jmap or the absolute j map. Let's note that accordingly
if rel then 
    if oneelement then
        codomain:=calG_parent_label;
    else
        codomain:=famG`agreeable_label; 
    end if;
else 
    codomain:=""; 
end if;

//Make everything over Rationals.
j:=relmap;
rank:=Rank(Parent(j[1]));
Pol:=PolynomialRing(Rationals(),rank);
j:=[Pol!j[i]: i in [1..#j]];

//Gonality 2 case handled
if Type(qgon2) eq BoolElt then
    if qgon2 then gonbounds:=<2,2,2,2>; end if;
    if not qgon2 then gonbounds:=<4,4,2,2>; end if;
    LMFDBWriteGonalityBounds(gonbounds, label);
end if;

//Geometric Gonality 3
if MFAM`CPname in gonality_equals_3 then geotrigonal:=true; else geotrigonal:=false; end if;
if geotrigonal then
    gonbounds := LMFDBReadGonalityBounds(label);
    if 3 gt gonbounds[1] then gonbounds[1]:=3; end if;
    gonbounds:=<gonbounds[1],gonbounds[2],3,3>;
    LMFDBWriteGonalityBounds(gonbounds, label);
end if;













//need the gonality data started.
if model_type eq 0 then 
    L:=ComputePlaneModel(Gcong,MAT,MFAM,psi); 
    best := [];
    bestkey := <>;
    CanEqs:=DefiningEquations(X);
    for d in L do
        f:=d[1];
        proj:=d[2];
        best, bestkey, vld, tmpval, tmpred := RecordPlaneModel(<f, proj>, CanEqs, best, bestkey, "mf", label : warn_invalid:=false); //need to learn how we actually save the plane models.
    end for;
    //LMFDBWritePlaneModel(f, proj, alg, label);//What is alg? and need to choose a best one. Figure this out.
end if;//<f,proj,M>


//Writing the cusps of the model. (This will be done later again?)
cusps:=CuspOrbits(Gcong);
Cs := LMFDBReadPlaneModel(label);
if psi eq [] then X:=Curve(ProjectiveSpace(Rationals(),1),[]); else
X := Curve(Proj(Universe(psi)), psi); end if;
C := 0; // stupid magma needs this defined even if not used.
if #Cs gt 0 then
    C := Curve(Proj(Parent(Cs[1][1])), Cs[1][1]);//Universe???
end if;
ans := [* *];
cusps := [orb[1] : orb in cusps];
cyclevel:=LCM([famG`M`N,#BaseRing(G)]);
F0:=F0Twister(famG`M`F0, MAT^(-1),cyclevel);
 for i in [1..#cusps] do
	    CuspUpdateCoordinates(~cusps[i], X, F0);
end for;
for cusp in cusps do
    K := cusp`field;
    P1K := ProjectiveSpace(K, 1);
    XK := ChangeRing(X, K);
    pt := XK!Eltseq(cusp`coords);
    Append(~ans, <model_type, pt>);
    if #Cs gt 0 then
        CK := ChangeRing(C, K);
        T := ChangeRing(Universe(Cs[1][2]), K);
        CprojK := map<XK -> CK| [T!f : f in Cs[1][2]]>;
        Append(~ans, <2, pt @ CprojK>);//this is plane model?
    end if;
end for;

//Write the cusp coordinates
LMFDBWriteCuspCoords(ans, label);
//Write the j map, now that we have all the cusp info
LMFDBWriteJMap(j, cusps, codomain, model_type, label);


//Handle the hyperelliptic curves. Note: what do we want to do for genus 1 curves.
if Type(qgon2) eq BoolElt then
if qgon2 eq true then   
    if psi eq [] then X:=Curve(ProjectiveSpace(Rationals(),1),[]); else
        X := Curve(Proj(Universe(psi)), psi); end if;
    isH, H,hmap := IsHyperelliptic(X);
    if isH then
        C:=H;
        LMFDBWriteHyperellipticModel(C, DefiningEquations(hmap), label);
    else
        "What do you mean it is not hyperelliptic?";
    end if;
else
    if not assigned prec then
        prec := 30;
    end if;
    if genus lt 3 then
        label cat ":genus too small";
        //exit;
    end if;
    t0 := ReportStart(label, "conic double cover model");
    done:=false;
    repeat
        try
            done:=true;
            C := HyperellipticModelFromGroup(Gcong,famG`CanModelForHyp,gonMAT : prec0:=prec);
        catch e 
            done:=false;
            prec:=prec+10;
        end try;
    until done;
    LMFDBWriteHyperellipticModel(DefiningEquations(C), [], label);
    //The above should give the hyperelliptic model
end if;
end if;



exit;




