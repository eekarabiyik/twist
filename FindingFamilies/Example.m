//Example File:

//Make sure to adjust current directory.
AttachSpec("./spec");
//Assuming the correct path of the folder:
FAM:=LoadFamiliesGenusIndex("./Families": genus:=5,index:=192);

//The group and its SL2 intersection
G:=sub<GL2Ambient(944)|[[119,0,0,119],[9,8,936,937],[69,244,0,5],[1,0,8,1],[55,769,10,33],[41,813,0,15],[1,8,0,1]]>;
T:=SL2Intersection(G);


//FAM[k] is the family record that contains G
//fam is the same thing as FAM[k]
//Gcong and Tcong are appropriate conjugates of G and T so they lie in our precomputed families
//calG is the agreeable closure of G. Gcong lies in calG
k,fam,Gcong,calG,Tcong:=FamilyFinderWithCusps(G,T,FAM);

//fam`H is the representative in the family fam. fam`M is the modular curve corresponding to fam`H.
//Let's call it H for short


//psi is a set of polynomials defining X_G
//MAT is the H90 matrix used to twist the representative curve. It is useful for many computations
//rel is a boolean. If it is true, then the relative j-map X_G --> X_calG is given by relmap.
//If rel is false, then relmap is the absolute j-map X_G-->PP_Q^1
//qgon2 gives information about the Q-gonality of X_G
//X_G and X_H are isomorphic over the field K
//famG is the family that contains G. Same as FAM[k] and fam above
//Gcong, same as above
//MFAM: famG`M
//gonMAT H90 matrix used for Q gonality 2 computations. Might not be assigned!
psi,MAT,relmap,rel,qgon2,genus,K,famG,Gcong,MFAM,gonMAT:=FindModel(G,T,FAM);

psi;
MAT;
relmap;
rel;
qgon2;

//The following loads all families up to genus 12   
FAM:=LoadFamiliesGenusIndex("./Families");

//There are 48819 mny of them
#FAM;