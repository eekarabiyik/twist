ChangeDirectory("/homes/ek693/Project/OpenImage/main");
load "FindOpenImage.m";
load "/homes/ek693/Project/OpenImage/SZ-data/RationalFunctions.m";
load "/homes/ek693/Project/OpenImage/SZ-data/GL2Invariants.m";
load "/homes/ek693/Project/OpenImage/SZ-data/g0groups.m";
ChangeDirectory("/homes/ek693/Project/cummingspauli");
load "pre.m";
load "csg.m";
load "/homes/ek693/Project/cummingspauli/csg4-lev104.dat";
load "/homes/ek693/Project/genuslessthan4/representativesearch.m";
//load "/homes/ek693/Twisting/genuslessthan4/GroupSearchFunctions.m";




load "/homes/ek693/Project/newrepresentativesearch/familycreatecode.m";
load "/homes/ek693/Project/newrepresentativesearch/newrepresentativesearch.m";\
load "/homes/ek693/Project/ciddi/special.m";

I:=Open("/homes/ek693/Project/ComputeModel/FindingFamilies/ConstructingAgreeable/KendiFamily.dat", "r");
FAM:=AssociativeArray();
a:=1;
repeat
	b,y:=ReadObjectCheck(I);
	if b then
		FAM[a]:=y;
	end if;
    a:=a+1;
until not b;

"Making groups simple";

for k in Keys(FAM) do
    if FAM[k]`calG_level eq 1 or FAM[k]`B_level eq 1 then continue; end if;
    time0:=Realtime();
    FAM[k]`calG:=ChangeRing(FAM[k]`calG,Integers(FAM[k]`calG_level));  
    FAM[k]`B:=ChangeRing(FAM[k]`B,Integers(FAM[k]`B_level));  
    print(k);
    print(Realtime(time0));
end for;    

"Finding Representatives";
for k in Keys(FAM) do
    if FAM[k]`genus lt 3 then continue; end if;
    time0:=Realtime();
    
        T:=FindSpecialSubgroup(FAM[k]`calG,FAM[k]`B);
        if gl2DetIndex(T) eq 1 then
            FAM[k]`H:=T;
        end if;

    print(k);
    print(Realtime(time0));
end for;

"Saving to file";

 I:=Open("/homes/ek693/Project/ComputeModel/FindingFamilies/ConstructingAgreeable/KendiFamilyRep.dat", "w");
    for k in Keys(FAM) do
        x:=FAM[k];
        WriteObject(I, x);
    end for;




"Computing modular curves for representatives";
for k in Keys(FAM) do
    time0:=Realtime();
    if assigned FAM[k]`H then
        FAM[k]`M:=FindModelOfXG(CreateModularCurveRec0(FAM[k]`H),10: G0:=FAM[k]`calG);        
    end if;
    print(k);
    print(Realtime(time0));
end for;




"Saving to file";

 I:=Open("/homes/ek693/Project/ComputeModel/FindingFamilies/ConstructingAgreeable/KendiFamilyRepModel.dat", "w");
    for k in Keys(FAM) do
        x:=FAM[k];
        WriteObject(I, x);
    end for;


