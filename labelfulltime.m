AttachSpec("./spec");
I:=Open("/homes/ek693/Main/FindingFamilies/FamilyDataFiles/SkeletonAndLabels/AssigningLabels/a24.txt","r");

content:=Read(I);
protolist:=Split(content);


listo:=[];
for i in [1..#protolist] do
    inner:=Split(protolist[i],":")[3][[2..#Split(protolist[i],":")[3]-1]];
    list_of_strings := [ StripWhiteSpace(x) : x in Split(inner, ",") ]; 
    listo:=listo cat [<Split(protolist[i],":")[1], eval Split(protolist[i],":")[2], list_of_strings>];
end for;

//keys calgens
list:=AssociativeArray();

for i in [1..#listo] do
    i;
    list[listo[i][2]]:=listo[i];
end for;

FAM:=LoadFamilies(["/homes/ek693/Main/KrakenComputations/12done/12alldone.dat"]);


//match labels and calgens
for k in Keys(FAM) do
    k;
    if FAM[k]`calG_level lt 481 then
        FAM[k]`label:=list[FAM[k]`calG_cangen][1];
    end if;
end for;



//keys labels
list:=AssociativeArray();

for i in [1..#listo] do
    i;
    list[listo[i][1]]:=listo[i];
end for;







//Add parents
for k in Keys(FAM) do
    k;
    if assigned FAM[k]`label then
        if not list[FAM[k]`label][3] eq [] and list[FAM[k]`label][3][1] in Keys(list) then
            FAM[k]`parentcalG:=list[FAM[k]`label][3][1];
        end if;
    end if;
end for;




//Check which ones do not have agreeable parents. flag them

for k in Keys(FAM) do
    if assigned FAM[k]`label then
        if not assigned FAM[k]`parentcalG then
            for l in [1..#list[FAM[k]`label][3]] do
                if list[FAM[k]`label][3][l] in Keys(list) then FAM[k]`parentcalG:=list[FAM[k]`label][3][l]; break l; end if;
            end for;
        end if;
    end if;

end for;



