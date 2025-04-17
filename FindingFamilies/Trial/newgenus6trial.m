//Load  this to run the code on all curves in LMFDB

AttachSpec("./spec");
FAM:=LoadFamilies(["./FindingFamilies/FamilyDataFiles/Families1new.dat","./FindingFamilies/FamilyDataFiles/Families2new.dat"]);
load "./FindingFamilies/Trial/lmfdbgenusupto6.m";
curves:=make_data();

//load "/homes/ek693/Main/FindingFamilies/TwistingCode/TwistingCode2.m";



for k in [100..200000] do
//if k in [190000..200000] then continue; end if;
G:=curves[k]`subgroup;
if #BaseRing(G) eq Infinity() then continue; end if;
//if GL2Index(G) eq GL2Index(GL2AgreeableClosure(G)) then continue; end if;
       
        print(k);
        time0:=Realtime();
        
        
        if GL2Order(G) eq 1 then continue; end if;
        if assigned G`SL then delete G`SL; end if;
        T:=SL2Intersection(G);
        psi,MAT,jmap,gon_2,genus,K,famkey:=FindModel(G,T,FAM);
        print(psi);
        //print(jmap);
        //print(gon_2);
        print(Realtime(time0));
        
end for;

