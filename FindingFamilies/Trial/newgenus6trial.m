//Load  this to run the code on all curves in LMFDB
AttachSpec("../spec");
FAM:=LoadFamilies(["/homes/ek693/Main/FindingFamilies/FamilyDataFiles/Families1.dat","/homes/ek693/Main/FindingFamilies/FamilyDataFiles/Families2.dat"]);
load "Trial/lmfdbgenusupto6.m";
curves:=make_data();

//load "/homes/ek693/Main/FindingFamilies/TwistingCode/TwistingCode2.m";



for k in Keys(curves) do
G:=curves[k]`subgroup;
if #BaseRing(G) eq Infinity() then continue; end if;

       
        print(k);
        time0:=Realtime();
        
        
        if GL2Order(G) eq 1 then continue; end if;
        if assigned G`SL then delete G`SL; end if;
        T:=SL2Intersection(G);
        //AgreeableClosure(G);
        //GL2Level(AgreeableClosure(G));
        //GL2Level(GL2AgreeableClosure(G));
        //GL2AgreeableClosure(G);
        //time1:=Realtime();
        //H1:=AgreeableClosure(G);
        //print(Realtime(time1));
        //time2:=Realtime();
        //H2:=GL2AgreeableClosure(G);
        //print(Realtime(time2));
        //assert GL2Project(AgreeableClosure(G),GL2Level(AgreeableClosure(G))) eq GL2Project(GL2AgreeableClosure(G),GL2Level(GL2AgreeableClosure(G)));
        psi,MAT,jmap,gon_2:=FindModel(G,T,FAM: redcub:=true);
        print(psi);
        print(jmap);
        //print(gon_2);
        //print(Realtime(time0));
        
end for;
