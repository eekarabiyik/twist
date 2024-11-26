for k in Keys(curves) do
    G:=curves[k]`subgroup;
    T:=G meet SL(2,Integers(#BaseRing(G)));
    G_level:=gl2Level(G);
    T_level:=sl2Level(T);
    //G_level mod T_level eq 0;
    T_level mod 2 eq 0;
end for;



for k in Keys(curves) do
    print(k);
    time0:=Realtime();
    G:=curves[k]`subgroup;
    T:=SL(2,Integers(#BaseRing(G))) meet G;
    psi:=FamilyFinderNew(G,T);
    print(psi);
    print(Realtime(time0));

end for;



I:=Open("/homes/ek693/Main/FindingFamilies/ConstructingFamilies/Families1.dat", "r");
FAM:=AssociativeArray();
a:=1;
repeat
	b,y:=ReadObjectCheck(I);
	if b then
		FAM[a]:=y;
	end if;
    a:=a+1;
until not b;