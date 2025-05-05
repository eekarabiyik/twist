load "/homes/ek693/Main/FindingFamilies/FamilyDataFiles/SkeletonAndLabels/AggCanMagmaStyle.m";
#list;
list:=[list[k]: k in Keys(list)|list[k][4] le 70];
#list;









ChangeDirectory("/homes/ek693/Main/FindingFamilies");
AttachSpec("../spec");
FAM:=LoadFamilies(["/homes/ek693/Main/FindingFamilies/FamilyDataFiles/Families020IncludingUniv.dat","/homes/ek693/Main/FindingFamilies/FamilyDataFiles/Families2124IncludingUniv.dat"]);




FAM:=[FAM[k]: k in Keys(FAM)| FAM[k]`calG_level le 70 and FAM[k]`oneelement eq true];
#FAM;
for k in Keys(FAM) do
    print(k);
    if FAM[k]`calG_index eq 1 then FAM[k]`label:="1.1.0.a.1"; end if;
    if FAM[k]`calG_index eq 6 and FAM[k]`calG_level eq 2 then FAM[k]`label:="2.6.0.a.1"; end if;
    t:=GL2CanonicalGenerators(FAM[k]`calG);
    for j in Keys(list) do
        if t eq list[j][2] then
            "Found!";list[j][1];
            FAM[k]`label:=list[j][1];
            break j;
        end if;

    end for;
end for;    


 &and[assigned FAM[k]`label: k in Keys(FAM)];
I:=Open("/homes/ek693/Main/FindingFamilies/FamilyDataFiles/SkeletonAndLabels/LabSkelLevelLessThanEq16/file.dat", "w");
    for k in Keys(FAM) do
        x:=FAM[k];
        WriteObject(I, x);
    end for;
