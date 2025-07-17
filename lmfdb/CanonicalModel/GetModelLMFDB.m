
AttachSpec("./spec");
//Assumeeverythingattached
//Need to figure out how the data is coming
//AttachSpec("equations.spec");
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













rec:=Random(curves1);


G:=rec`subgroup;
label:=rec`label;
T:=SL2Intersection(G);
FAM:=LoadFamilies("/data/modcurve/Families2": genus:=5, index:=rec`index);
psi,MAT,relmap,rel,qgon2,genus,K,famG,Gcong,MFAM,gonMAT:=FindModel(G,T,FAM); //we already know the family. so it should be more like:: FindModel(Gcong,Tcong,FAM[family_label]);

//canon is0 embedded is 8
if MFAM`genus gt 2 and not MFAM`CPname in gonality_equals_2 then model_type:=0; else model_type:=8; end if; 
//Gonality for (Qbar gonality 2 + genus>2) curves are completely determined by above code. 


if psi eq [] then X:=Curve(ProjectiveSpace(Rationals(),1),[]); else
rank:=Rank(Parent(psi[1]));
Pol:=PolynomialRing(Rationals(),rank);
psi:=[Pol!psi[i]: i in [1..#psi]];
X := Curve(ProjectiveSpace(Rationals(),rank-1), psi); end if;

LMFDBWriteXGModel(X,model_type,label);




j:=relmap;
rank:=Rank(Parent(j[1]));
Pol:=PolynomialRing(Rationals(),rank);
j:=[Pol!j[i]: i in [1..#j]];






if rel then codomain:=famG`agreeable_label; else codomain:=""; end if;

cusps:=[];


    cyclevel:=LCM([famG`M`N,#BaseRing(Gcong)]);
    F0:=F0Twister(famG`M`F0, MAT^(-1),cyclevel);
    cusps := CuspOrbits(Gcong);
        // We only need one representative of each orbit
        cusps := [orb[1] : orb in cusps];
        for i in [1..#cusps] do
	    CuspUpdateCoordinates(~cusps[i], X, F0);
        end for;




LMFDBWriteJMap(j, cusps, codomain, model_type, label);//cusps empty so far, gotta check that
//need the gonality data started.
if model_type eq 0 then 
    L:=ComputePlaneModel(Gcong,MAT,MFAM,psi); 
    best := [];
    bestkey := <>;
    CanEqs:=DefiningEquations(X);
    for d in L do
        f:=d[1];
        proj:=d[2];
        ans:=RecordPlaneModel(<f, proj>, CanEqs, best, bestkey, "mf", label : warn_invalid:=false);
    end for;
    //LMFDBWritePlaneModel(f, proj, alg, label);//What is alg? and need to choose a best one.
    //might need to use  RecordPlaneModel
end if;//<f,proj,M>
//Add gonalities
//where does the gonality bounds come from? is it all from plane models? 
//What should be the main gonality bound contributor ? plane models or canonical models? 

exit;