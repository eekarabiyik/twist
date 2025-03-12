//Load  this to run the code on all curves in LMFDB
//Be careful about the paths, havent fixed them yet

ChangeDirectory("/homes/ek693/Main/FindingFamilies");
AttachSpec("../spec");
FAM:=LoadFamilies(["/homes/ek693/Main/UnivEllCurve/unelcurvestuff/allfamincludingfinestuffLATEST.dat"]);
//It is enough to load Main/FindingFamilies/FamilyDataFiles/Families1new.dat and Main/FindingFamilies/FamilyDataFiles/Families2new.dat
//for you
//Will update these once things are optimized and clean.
load "/homes/ek693/Main/UnivEllCurve/univellcurvedatalmfdb/lmfdbdatafine.m";
curves:=make_data();



for k in Keys(curves) do
if k in [1..100] then continue; end if;
G:=curves[k]`subgroup;
if curves[k]`genus le 1 then continue; end if;
if #BaseRing(G) eq Infinity() then continue; end if;
//if GL2Index(G) eq GL2Index(GL2AgreeableClosure(G)) then continue; end if;
        
        print(k);
        time0:=Realtime();
        
        
        if GL2Order(G) eq 1 then continue; end if;
        if assigned G`SL then delete G`SL; end if;
        T:=SL2Intersection(G);
        H:=GL2IncludeNegativeOne(G);
        _,H:=GL2Level(H);
        M0:=CreateModularCurveRec(G);
        famkey,_,Hcong:=FamilyFinder(H,SL2Intersection(H),FAM);
        M:=FindModelOfXG(CreateModularCurveRec(Hcong):G0:=FAM[famkey]`calG);

        FindRatio(M,M0,2: prec0:=100);//Change prec accordingly
      
      
      
      
        print(Realtime(time0));
        
end for;
