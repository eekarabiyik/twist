
AttachSpec("./spec");
load "./FindingFamilies/CanonicalGenerators/UpdateFinal/LMFDBupto7cangens.m"; //bu her sey
FAM:=LoadFamilies(["./FindingFamilies/FamilyDataFiles/Genus1canon.dat"]);

RecFormat := recformat<level,index,genus,generators,subgroup,label,canonical_generators,aggclosure>;

function create_record(row)
    out := rec<RecFormat|level:=row[5],index:=row[4],genus:=row[6],generators:=row[2],label:=row[1],aggclosure:=row[7],canonical_generators:=row[3]>;
    subgroup := out`level eq 1 select sub<GL(2,Integers())|> else sub<GL(2,Integers(out`level))|out`generators>;
    out`subgroup := subgroup;
    return out;
end function;

function make_data()
    return [create_record(row) : row in list];
end function;

curves1:=make_data();
/*
for k in Keys(curves) do
    curves[curves[k][7]];
end for;
*/



curves:=AssociativeArray();

for k in curves1 do
    curves[k`label]:=k;
end for;





for rec in curves do
    if rec`genus eq 1 then
    G:=rec`subgroup;
    T:=SL2Intersection(G);
    parentcan:=curves[rec`aggclosure]`canonical_generators;
    //u:=FamilyFinderWithCusps(G,T,FAM);
    //u;
    psi,MAT,relmap:=FindModel(G,T,FAM,parentcan);
    psi;
    relmap;
    end if;
end for;