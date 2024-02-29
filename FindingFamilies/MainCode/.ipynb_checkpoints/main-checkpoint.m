ChangeDirectory("/homes/ek693/Project/ComputeModel/OpenImage/main");
load "FindOpenImage.m";
load "/homes/ek693/Project/ComputeModel/OpenImage/SZ-data/RationalFunctions.m";
load "/homes/ek693/Project/ComputeModel/OpenImage/SZ-data/GL2Invariants.m";
//load "/homes/ek693/Project/OpenImage/SZ-data/g0groups.m";
//ChangeDirectory("/homes/ek693/Project/cummingspauli");
//load "pre.m";
//load "csg.m";
//load "/homes/ek693/Project/cummingspauli/csg4-lev104.dat";
//load "/homes/ek693/Twisting/genuslessthan4/GroupSearchFunctions.m";


// given subgroups H1,H2 of G, returns true if H1 is conjugate in G to a subgroup of H2
function IsConjugateToSubgroup(G,H1,H2)
    if not IsDivisibleBy(#H2,#H1) then return false; end if;
    if H1 subset H2 then return true; end if;   // handle easy cases quickly
    n:=#H2 div #H1;
    return #[H:H in Subgroups(H2:IndexEqual:=n)|IsConjugate(G,H`subgroup,H1)] ne 0;
end function;



load "/homes/ek693/Project/ComputeModel/FindingFamilies/FamilyData/familycreatecodewithanarrayfosubgroup.m";


I:=Open("/homes/ek693/Project/davidtrial/KendiAggrepresentativesubgroupswithrepres.dat", "r");
FAM:=AssociativeArray();
a:=1;
repeat
	b,y:=ReadObjectCheck(I);
	if b then
		FAM[a]:=y;
	end if;
    a:=a+1;
until not b;


/*

I:=Open("/homes/ek693/Project/davidtrial/trialgenuschecked.dat", "r");
FAM:=AssociativeArray();
a:=1;
repeat
	b,y:=ReadObjectCheck(I);
	if b then
		FAM[a]:=y;
	end if;
    a:=a+1;
until not b;
*/

load "/homes/ek693/Project/ComputeModel/FindingFamilies/TwistingCode/H90.m";
load "/homes/ek693/Project/ComputeModel/FindingFamilies/FamilyFinder/aggclosurecreator.m";
load "/homes/ek693/Project/ComputeModel/FindingFamilies/TwistingCode/GroupToCocycle.m";
load "/homes/ek693/Project/ComputeModel/FindingFamilies/TwistingCode/TwistingCode.m";











function FindModelNew(G,T)   
    //Input: G is a subgroup of GL2(Zhat). It is given by a subgroup of GL2(Z/NZ) where N is a multiple of the level of G.
    //       T is G intersection SL2(Z/NZ)
    //Output: homogeneous polynomials in Q[x_1,..x_n] defining the curve X_G mentioned above. n is depends on the model of the family representative that is twist of G,
    
    //We first start with finding the family in our database that contains G. 
    print("Finding the family...");
    k,famG,Gcong,calGlift,Tcong:=FamilyFinderNew(G,T);
    N:=#BaseRing(G);
    printf "thhe family key in the databese is %o",k;
    if not assigned famG`M then
        print("No modular curve record found in the family. Computing it...");
        M:=FindModelOfXG(CreateModularCurveRec0(famG`H),10 : G0:=famG`calG);
        printf "Computed";
    else
        M:=famG`M;
    end if;
    //Now we conjugate G so that it lies in fam_G`calG.
    
    G:=Gcong;
    T:=Tcong;//I hope this is okay.
    //Computing the cocycle related to H and G. See the paper for details.
    printf "Computing the cocycle";
    xi,K:=GroupToCocycle(famG`calG,famG`H,G,T,M);
    //Now the twist
    printf "Twisting the curve...";
    psi:=Twist(M,xi,K, famG`calG);

    return psi;
end function; 

//It workssssssssssssssssssssssssssssssssssssss!!!!!
