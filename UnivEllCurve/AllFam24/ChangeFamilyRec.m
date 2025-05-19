ChangeDirectory("/homes/ek693/Main/FindingFamilies");
AttachSpec("../spec");
FAM:=LoadFamilies(["/homes/ek693/Main/FindingFamilies/FamilyDataFiles/AllFam12fine.dat","/homes/ek693/Main/FindingFamilies/FamilyDataFiles/AllFam1220fine.dat","/homes/ek693/Main/FindingFamilies/FamilyDataFiles/AllFam2024Genus20Missing.dat"]);
//FAM:=[FAM[k]: k in Keys(FAM)| FAM[k]`genus le 6 and FAM[k]`fine eq true];
FAM1:=AssociativeArray();
for k in Keys(FAM) do
    if FAM[k]`genus gt 20 then continue; end if;
    print(k);
    FAM1[k]:= CreateFamilyUnivRec(FAM[k]`calG, FAM[k]`B, FAM[k]`commutator_sub, FAM[k]`W, FAM[k]`CPname);
    if assigned FAM[k]`fine then FAM1[k]`fine:=FAM[k]`fine; end if;
    if assigned FAM[k]`calG_level then FAM1[k]`calG_level:=FAM[k]`calG_level; end if;
    if assigned FAM[k]`B_level then FAM1[k]`B_level:=FAM[k]`B_level; end if;
    if assigned FAM[k]`genus then FAM1[k]`genus:=FAM[k]`genus; end if;
    if assigned FAM[k]`sl2level then FAM1[k]`sl2level:=FAM[k]`sl2level; end if;
    if assigned FAM[k]`level then FAM1[k]`level:=FAM[k]`level; end if;
    if assigned FAM[k]`k then FAM1[k]`k:=FAM[k]`k; end if;
    if assigned FAM[k]`prec then FAM1[k]`prec:=FAM[k]`prec; end if;
    if assigned FAM[k]`commutator_index then FAM1[k]`commutator_index:=FAM[k]`commutator_index; end if;
    if assigned FAM[k]`maxprec then FAM1[k]`maxprec:=FAM[k]`maxprec; end if;
    if assigned FAM[k]`model_type then FAM1[k]`model_type:=FAM[k]`model_type; end if;
    if assigned FAM[k]`maxd then FAM1[k]`maxd:=FAM[k]`maxd; end if;
    if assigned FAM[k]`mind then FAM1[k]`mind:=FAM[k]`mind; end if;
    if assigned FAM[k]`calG_gens then FAM1[k]`calG_gens:=FAM[k]`calG_gens; end if;
    if assigned FAM[k]`B_gens then FAM1[k]`B_gens:=FAM[k]`B_gens; end if;
    if assigned FAM[k]`subgroupsofH then FAM1[k]`subgroupsofH:=FAM[k]`subgroupsofH; end if;
    if assigned FAM[k]`jmap then FAM1[k]`jmap:=FAM[k]`jmap; end if;
    if assigned FAM[k]`M then FAM1[k]`M:=FAM[k]`M; end if;
    if assigned FAM[k]`calGModCurve then FAM1[k]`calGModCurve:=FAM[k]`calGModCurve; end if;
    if assigned FAM[k]`AOfMF then FAM1[k]`AOfMF:=FAM[k]`AOfMF; end if;
    if assigned FAM[k]`quomap then FAM1[k]`quomap:=FAM[k]`quomap; end if;
    if assigned FAM[k]`quogroup then FAM1[k]`quogroup:=FAM[k]`quogroup; end if;
    if assigned FAM[k]`dataforquotient then FAM1[k]`dataforquotient:=FAM[k]`dataforquotient; end if;
    if assigned FAM[k]`conjugacyofB then FAM1[k]`conjugacyofB:=FAM[k]`conjugacyofB; end if;
    if assigned FAM[k]`AOfMFCanModel then FAM1[k]`AOfMFCanModel:=FAM[k]`AOfMFCanModel; end if;
    if assigned FAM[k]`CanModelForHyp then FAM1[k]`CanModelForHyp:=FAM[k]`CanModelForHyp; end if;
    if assigned FAM[k]`H then FAM1[k]`H:=FAM[k]`H; end if;
    if assigned FAM[k]`H then FAM1[k]`index:=GL2Index(FAM[k]`H); end if;//Wrong!!!
    if assigned FAM[k]`H then FAM1[k]`numberofcusps:=GL2CuspCount(FAM[k]`H); end if;
    if assigned FAM[k]`H and assigned FAM[k]`fine and FAM[k]`fine eq false and #BaseRing(FAM[k]`H) eq #BaseRing(FAM[k]`calG) and FAM[k]`calG eq FAM[k]`H then
        FAM1[k]`oneelement:=true;
    end if;
    FAM1[k]`calG_index:=GL2Index(FAM[k]`calG);

end for;



I:=Open("/homes/ek693/Main/FindingFamilies/Trial/DealingWithLabels/ChangeFamilyRecNew.dat", "w");
    for k in Keys(FAM1) do
        x:=FAM1[k];
        WriteObject(I, x);
    end for;
