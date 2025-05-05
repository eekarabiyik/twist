load "/homes/ek693/Main/FindingFamilies/FamilyDataFiles/SkeletonAndLabels/Skeleton/SkeletonNew.m";
list:=[list[k]: k in Keys(list)| list[k][5] le 24];
#list;








ChangeDirectory("/homes/ek693/Main/FindingFamilies");
AttachSpec("../spec");
FAM:=LoadFamilies(["/homes/ek693/Main/FindingFamilies/FamilyDataFiles/SkeletonAndLabels/LabSkelLevelLessThanEq70/file.dat"]);




FAM:=[FAM[k]: k in Keys(FAM)| FAM[k]`calG_level le 70 and FAM[k]`oneelement eq true];
#FAM;

for k in Keys(FAM) do
    print(k);

    for j in Keys(list) do
        if list[j][5] gt 24 then continue j; end if;
        if FAM[k]`label eq list[j][1] then
            "Found!";
            list[j][1];
            FAM[k]`parentcalG:=list[j][6];
            break j;
        end if;

    end for;
    if not assigned FAM[k]`parentcalG then FAM[k]`parentcalG:=[]; end if;

end for;    


 &and[assigned FAM[k]`label: k in Keys(FAM)];
I:=Open("/homes/ek693/Main/FindingFamilies/FamilyDataFiles/SkeletonAndLabels/Skeleton/SkeletonAdded.dat", "w");
    for k in Keys(FAM) do
        x:=FAM[k];
        WriteObject(I, x);
    end for;
