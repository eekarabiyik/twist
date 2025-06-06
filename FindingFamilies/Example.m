AttachSpec("../spec");
//We load Families. They are in pieces so I can upload them to the Github.
FAM := LoadFamilies(["FamilyDataFiles/Families1.dat", "FamilyDataFiles/Families2.dat"]);

G:=sub<GL(2,Integers(312))|[[ 251, 99, 170, 283 ],[ 272, 115, 103, 13 ],[ 288, 233, 247, 224 ],[ 231, 118, 275, 89 ],[ 290, 59, 153, 163 ]]>;
assert GL2ContainsNegativeOne(G);
assert GL2DeterminantIndex(G) eq 1;
T:=SL2Intersection(G);
T`SL:=true;
psi,Mat,jmap,hyper,g:=FindModel(G,T,FAM);
print(psi);
print(Mat);
print(jmap);
print(hyper);
print(g);




