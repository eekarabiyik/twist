ChangeDirectory("/homes/ek693/Main/FindingFamilies");
AttachSpec("../spec");
FAM:=LoadFamilies(["/homes/ek693/Main/FindingFamilies/ChangingRecordsFinally/Final024Level70.dat"]);

FAMMAPS:=AssociativeArray();

for k in Keys(FAM) do
    if FAM[k]`genus gt 12 then continue k; end if;
    print(k);
    FAMMAPS[k]:=FindAllModelGivenFamily([FAM[k]])[1];
end for;



I:=Open("/homes/ek693/Main/FindingFamilies/BigComputation/Genus012.dat", "w");
    for k in Keys(FAMMAPS) do
        x:=FAMMAPS[k];
        WriteObject(I, x);
    end for;
