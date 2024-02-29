ChangeDirectory("/homes/ek693/Project/ComputeModel/OpenImage/main");
load "FindOpenImage.m";
load "/homes/ek693/Project/ComputeModel/OpenImage/SZ-data/RationalFunctions.m";
load "/homes/ek693/Project/ComputeModel/OpenImage/SZ-data/GL2Invariants.m";
ChangeDirectory("/homes/ek693/Project/cummingspauli");
load "pre.m";
load "csg.m";
load "/homes/ek693/Project/cummingspauli/csg4-lev104.dat";
load "/homes/ek693/Project/ComputeModel/FindingFamilies/FamilyData/familycreatecodewithanarrayfosubgroup.m";

gl2Genus:=GL2Genus;



load "/homes/ek693/Project/ciddi/special.m";

I:=Open("/homes/ek693/Project/ComputeModel/FindingFamilies/ConstructingAgreeable/KendiFamilyRep.dat", "r");
FAM:=AssociativeArray();
a:=1;
repeat
	b,y:=ReadObjectCheck(I);
	if b then
		FAM[a]:=y;
	end if;
    a:=a+1;
until not b;




"Computing modular curves for representatives";
for k in Keys(FAM) do
    
    if FAM[k]`genus lt 3 then continue; end if;
    print(k);
    time0:=Realtime();
    if assigned FAM[k]`H then
        FAM[k]`M:=FindModelOfXG(CreateModularCurveRec0(FAM[k]`H),10: G0:=FAM[k]`calG);        
    end if;
    
    print(Realtime(time0));
end for;




"Saving to file";

 I:=Open("/homes/ek693/Project/ComputeModel/FindingFamilies/ConstructingAgreeable/KendiFamilyRepModel.dat", "w");
    for k in Keys(FAM) do
        x:=FAM[k];
        WriteObject(I, x);
    end for;


