


ChangeDirectory("/homes/ek693/Main/FindingFamilies");
AttachSpec("../spec");
FAM:=LoadFamilies(["/homes/ek693/Main/FindingFamilies/FamilyDataFiles/SkeletonAndLabels/Skeleton/SkeletonAdded.dat"]);



FAM:=[FAM[k]: k in Keys(FAM)| FAM[k]`calG_level le 70 and FAM[k]`oneelement eq true];
#FAM;

for k in Keys(FAM) do
    print(k);
    FAM[k]`skeleton:=[];
    if not Type(FAM[k]`parentcalG) eq MonStgElt then continue k; end if;
    a:=exists(j){j: j in Keys(FAM)|FAM[k]`parentcalG eq FAM[j]`label};
    while a do
        Append(~FAM[k]`skeleton,FAM[j]`label);
        l:=j;
        if not Type(FAM[l]`parentcalG) eq MonStgElt then continue k; end if;
        a:=exists(j){j: j in Keys(FAM)|FAM[l]`parentcalG eq FAM[j]`label};

    end while;

end for;    


 &and[assigned FAM[k]`label: k in Keys(FAM)];
I:=Open("/homes/ek693/Main/FindingFamilies/FamilyDataFiles/SkeletonAndLabels/Skeleton/SkeletonAdded.dat", "w");
    for k in Keys(FAM) do
        x:=FAM[k];
        WriteObject(I, x);
    end for;
