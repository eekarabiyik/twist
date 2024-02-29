load "/homes/ek693/Project/FindingFamilies/MainCode/main.m";
load "/homes/ek693/Project/FindingFamilies/LMFDBGroups/genus1.m";
curves:=make_data();
numberfamily:=AssociativeArray();


/*
I:=Open("/homes/ek693/Project/FindingFamilies/davidgroupsmyway.dat", "r");
Families:=AssociativeArray();
a:=1;
repeat
	b,y:=ReadObjectCheck(I);
	if b then
		Families[a]:=y;
	end if;
    a:=a+1;
until not b;
*/


for k in Keys(curves) do
    time0:=Realtime();
    G:=sub<GL(2,Integers(curves[k]`level))|curves[k]`generators>;
    T:=SL(2,Integers(#BaseRing(G))) meet G;
    famG,t:=FamilyFinder(G,T);
    numberfamily[k]:=<famG,t>;
    print(k);
    print(Realtime(time0));

end for;



 I:=Open("/homes/ek693/Project/FindingFamilies/LMFDBGroups/genus1davidtrialfamilydata.dat", "w");
    for k in Keys(numberfamily) do
        x:=numberfamily[k];
        WriteObject(I, x);
    end for;

