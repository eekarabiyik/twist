//Load  this to run the code on all curves in LMFDB
//Be careful about the paths, havent fixed them yet

ChangeDirectory("./FindingFamilies");
AttachSpec("../spec");
// the file below doesn't exist 
//FAM:=LoadFamilies(["/homes/ek693/Main/UnivEllCurve/unelcurvestuff/allfamincludingfinestuffLATEST.dat"]);
FAM := LoadFamilies(["./FamilyDataFiles/Families1new.dat","./FamilyDataFiles/Families2new.dat"]);
//It is enough to load Main/FindingFamilies/FamilyDataFiles/Families1new.dat and Main/FindingFamilies/FamilyDataFiles/Families2new.dat
//for you
//Will update these once things are optimized and clean.
load "../UnivEllCurve/univellcurvedatalmfdb/lmfdbdatafine.m";
curves:=make_data();

/*
k := 101;
G := curves[k]`subgroup;
M0 := CreateModularCurveRec(G);
H := GL2IncludeNegativeOne(G);
TY := SL2Intersection(H);
famkey,_,H := FamilyFinder(H, TY, FAM);
M := CreateModularCurveRec(H);
M := FindModelOfXG(M : G0:=FAM[famkey]`calG);
C, jmap, _, _, _, _, _ := AbsoluteJmap(M);

*/

//Here I loop over the fine curves
for k in Keys(curves) do
if k in [1..100] then continue; end if;//Do not one very low level ones for trying
G:=curves[k]`subgroup;//this is the curve
//if not curves[k]`genus ge 0 then continue; end if;
if #BaseRing(G) eq Infinity() then continue; end if;
//if GL2Index(G) eq GL2Index(GL2AgreeableClosure(G)) then continue; end if;
        
        print(k);
        time0:=Realtime();
        
        
        if GL2Order(G) eq 1 then continue; end if;
        if assigned G`SL then delete G`SL; end if;

        _,_,Gcong:=FamilyFinderFine(G,SL2Intersection(G),FAM);//THIS IS SO IMPORTANT! VERY IMPORTANT!First conjugate the fine group so it lies in our families

        H:=GL2IncludeNegativeOne(Gcong);
        M0:=CreateModularCurveRec(Gcong);//Modular curve of the fine group
        famkey,_,H:=FamilyFinder(H,SL2Intersection(H),FAM);//Find the family of the coarse group
        M:=FindModelOfXG(CreateModularCurveRec(H):G0:=FAM[famkey]`calG);//Compute the model for the course group. For the real computation this wont be needed since we will twist ratios.
        //M0`widths eq M`widths;
        //M0`widths;
        //M`widths;
        //The following function should return a list of two polynomials, num and denom for the weight 3 modular form.
        FindRatio(M,M0,2: prec0:=20);//Change prec accordingly IMPORTANT. AT LEAST HAVE THE BASE VALUES OF PREC0 SOMETHING LIKE 20
      
      
      
      
        print(Realtime(time0));
        
end for;






/*


k := 1000;
G := curves[k]`subgroup;
_, _, Gcong := FamilyFinderFine(G,SL2Intersection(G),FAM);
H := GL2IncludeNegativeOne(Gcong);
M0 := CreateModularCurveRec(Gcong);
 TY := SL2Intersection(H);
famkey,_,H := FamilyFinder(H, SL2Intersection(H), FAM);
 M := CreateModularCurveRec(H);
 M := FindModelOfXG(M : G0:=FAM[famkey]`calG);
 C, jmap, _, _, _, _, _ := AbsoluteJmap(M);
 M0`genus;
 FindRatio(M,M0,2:prec0:=20);


 for k in Keys(curves) do
if k in [1..100] then continue; end if;//Do not one very low level ones for trying

if curves[k]`genus eq 4 then print(k); break k; end if;

 end for;

 k:=1066;

 k:=171;
  G := curves[k]`subgroup;


 ffff,asdas,Gcong:=FamilyFinderFine(G,SL2Intersection(G),FAM);
  M0 := CreateModularCurveRec(Gcong);
H := GL2IncludeNegativeOne(Gcong);
 TY := SL2Intersection(H);
famkey,_,H := FamilyFinder(H, TY, FAM);
 M := CreateModularCurveRec(H);
 M := FindModelOfXG(M : G0:=FAM[famkey]`calG);
 C, jmap, _, _, _, _, _ := AbsoluteJmap(M);
 M0`genus;
 FindRatio(M,M0,2:prec0:=20);

gens:=[[1,0,0,1],[1,0,0,2],[1,1,0,1],[1,1,0,2],[1,2,0,1],[1,1,0,2]];
G:=sub<GL2Ambient(3)|gens2>;
gens2:=[[1,0,0,1],[2,0,0,1],[1,1,0,1],[2,1,0,1],[1,2,0,1],[2,2,0,1]];




[[ 5, 1, 6, 5 ],[ 7, 3, 6, 1 ],[ 7, 3, 6, 5 ]]


  G:=sub<GL2Ambient(8)|[[ 5, 1, 6, 5 ],[ 7, 3, 6, 1 ],[ 7, 3, 6, 5 ]]>;


  */