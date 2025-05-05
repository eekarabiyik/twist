



ChangeDirectory("/homes/ek693/Main/FindingFamilies");
AttachSpec("../spec");
FAM:=LoadFamilies(["/homes/ek693/Main/FindingFamilies/FamilyDataFiles/SkeletonAndLabels/Skeleton/SkeletonAdded.dat"]);



FAM:=[FAM[k]: k in Keys(FAM)|FAM[k]`calG_level le 16];
#FAM;

for k in Keys(FAM) do
    print(k);
    calG:=GL2Canonicalize(FAM[k]`calG);
    FAM[k]`calG:=calG;
    FAM[k]`H:=calG;
end for;



for k in Keys(FAM) do
    if not assigned FAM[k]`calGModCurve then
        calM:=FindModelOfXG(CreateModularCurveRec(FAM[k]`calG));
        FAM[k]`calGModCurve:=calM;
    end if;
    if Type(FAM[k]`parentcalG) eq MonStgElt then
        print(k);
        exists(j){j: j in Keys(FAM)|FAM[k]`parentcalG eq FAM[j]`label};
        j;
        if assigned FAM[j]`calGModCurve then 
            "a";
            a,b:=GL2IsConjugateSubgroup(FAM[j]`calG,FAM[k]`calG);
    
            FAM[k]`parentrelmapcalG:= FindMorphism(FAM[k]`calGModCurve,FAM[j]`calGModCurve);
        else
            "b";
            FAM[j]`calGModCurve:=FindModelOfXG(CreateModularCurveRec(FAM[j]`calG));
            FAM[k]`parentrelmapcalG:= FindMorphism(FAM[k]`calGModCurve,FAM[j]`calGModCurve);
        end if;
    end if;
end for;


for k in Keys(FAM) do
   
    if Type(FAM[k]`parentcalG) eq MonStgElt then
        print(k);
        assert exists(j){j: j in Keys(FAM)|FAM[k]`parentcalG eq FAM[j]`label};
        
    end if;
end for;


for k in Keys(FAM) do
   
    assert FAM[k]`calG eq FAM[k]`H;
end for;

G:=sub<GL2Ambient(24)|[[3, 10, 4, 3],
  [11, 12, 6, 11],
  [11, 12, 12, 1],
  [20, 21, 15, 2]]>;


  H:=sub<GL2Ambient(12)| [[1, 0, 9, 1], [1, 6, 6, 1], [1, 6, 11, 5], [11, 4, 7, 1]]>;