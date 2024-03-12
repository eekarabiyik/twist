load "/homes/ek693/Project/ComputeModel/FindingFamilies/MainCode/main.m";
load "/homes/ek693/Project/ComputeModel/FindingFamilies/LMFDBGroups/genus1.m";
curves:=make_data();
models:=AssociativeArray();

for k in Keys(curves) do
    print(k);
    time0:=Realtime();
    G:=curves[k]`subgroup;
    T:=SL(2,Integers(#BaseRing(G))) meet G;
    psi:=FindModelNew(G,T);
    //models[k]:=psi;
    print(psi);
    print(Realtime(time0));

end for;



 I:=Open("/homes/ek693/Project/ComputeModel/FindingFamilies/LMFDBGroups/genus1models.dat", "w");
    for k in Keys(models) do
        x:=models[k];
        WriteObject(I, x);
    end for;

/*
for k in Keys(curves) do
    print(k);
    time0:=Realtime();
    G:=curves[k]`subgroup;
    T:=SL(2,Integers(#BaseRing(G))) meet G;
    psi:=FamilyFinderNew(G,T);
    print(psi);
    print(Realtime(time0));

end for;
*/