ChangeDirectory("/homes/ek693/Main/FindingFamilies/MainCode");
load "/homes/ek693/Main/FindingFamilies/MainCode/main.m";
load "/homes/ek693/Main/FindingFamilies/LMFDBGroups-unimportant/newgenus1.m";
curves:=make_data();



for k in Keys(curves) do
    if curves[k]`level lt 70 then
        print(k);
        time0:=Realtime();
        G:=curves[k]`subgroup;
        T:=SL(2,Integers(#BaseRing(G))) meet G;
        psi:=FamilyFinderNew(G,T);
        print(psi);
        print(Realtime(time0));
    end if;
end for;
