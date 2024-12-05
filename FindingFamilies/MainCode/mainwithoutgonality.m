//This is a rudimantary version of the Twisting Code. The j-map is now included.
//The final polynomials are ugly in the sense that there are many unnecessary cubic relations.
//However it is very fast and uses the last version of GL2 magma intrinsics. This will be updated soon. 
AttachSpec("../../DrewMagma/magma.spec");

//from SZ
//given subgroups H1,H2 of G, returns true if H1 is conjugate in G to a subgroup of H2
function IsConjugateToSubgroup(G,H1,H2)
    if not IsDivisibleBy(#H2,#H1) then return false; end if;
    if H1 subset H2 then return true; end if;   // handle easy cases quickly
    n:=#H2 div #H1;
    return #[H:H in Subgroups(H2:IndexEqual:=n)|IsConjugate(G,H`subgroup,H1)] ne 0;
end function;

I:=Open("../FamilyDataFiles/Families1.dat", "r");
FAM:=AssociativeArray();
a:=1;
repeat
	b,y:=ReadObjectCheck(I);
	if b then
		FAM[a]:=y;
	end if;
    a:=a+1;
until not b;


I:=Open("../FamilyDataFiles/Families2.dat", "r");
repeat
	b,y:=ReadObjectCheck(I);
	if b then
		FAM[a]:=y;
	end if;
    a:=a+1;
until not b;

//Thansk to David Roe.
function lift_hom(f, M)
    R := BaseRing(Domain(f));
    GM := GL2Lift(Domain(f), M);
    return hom<GM -> Codomain(f) | [<GM.i, ChangeRing(GM.i, R) @ f> : i in [1..Ngens(GM)]] >;
end function;



load "../FamilyData/FamilyRecWithEverything.m";
load "../TwistingCode/H90.m";//H90 matrix function
load "../FamilyFinder/FamilyFinder.m";//Function for Finding the family
load "../TwistingCode/Newco2.m";//Cocycle Cretor
load "../TwistingCode/TwistingCode.m";//Twisting code












function FindModelNew(G,T: redcub:=false)   
    //Input: G is a subgroup of GL2(Zhat). It is given by a subgroup of GL2(Z/NZ) where N is a multiple of the level of G.
    //       T is G intersection SL2(Z/NZ)
    //Output: psi: homogeneous polynomials in Q[x_1,..x_n] defining the curve X_G mentioned above. n is depends on the model of the family representative that is twist of G,
    //        MAT: H90 matrix that defines the twist
    //        jmap: rational map to the j line given by a numeratror and denumerator
    
    //We first start with finding the family in our database that contains G. 
    print("Finding the family...");
    famkey,famG,Gcong,calGlift,Tcong:=FamilyFinderNew(G,T);
    N:=#BaseRing(G);
    printf "The family key in the database is %o\n",famkey;
    AOfMF:=AssociativeArray();
    for i in Keys(famG`AOfMF) do
        AOfMF[i]:=Transpose(famG`AOfMF[i]);
    end for;
    Tcong`SL:=true;
    //Computing the cocycle related to H and G. See the paper for details. (Paper is not out yet so look at the file)
    printf "Computing the cocycle\n";
    xi,K:=GroupToCocycleNew(famG`calG,famG`H,Gcong,Tcong,AOfMF);
    //Now the twist
    printf "Twisting the curve...\n";
    psi,MAT:=TwistCurve(famG`M,xi,K, famG`calG: redcub:=redcub);
	//Now we compute the jmap. Need to do Galois descent to have rational coefficents. So a little messy
    printf "Computing the jmap...\n";
    mapss := FAM[famkey]`jmap;
    s := NumberOfRows(MAT);
    Pol<[x]> := PolynomialRing(K,s); 
    PP := ProjectiveSpace(Rationals(),s-1);    
    num := Pol!mapss[1]^MAT;
    denum := Pol!mapss[2]^MAT;
    d:=Degree(num);
    mond:=MonomialsOfDegree(Pol,d);
    numcoef:=[MonomialCoefficient(num,m): m in mond];
    denumcoef:=[MonomialCoefficient(denum,m): m in mond]; 
    UUd := VectorSpace(K,#mond);
    GAL,iota,sigma:=AutomorphismGroup(K);
    B:=Basis(K);
    //For numerator
    for b in B do
        newnumcoef:=Matrix(K,#mond,1,[0: i in [1..#mond]]);
        v:=[numcoef[i]*b:i in [1..#numcoef]];
        newnumcoef:=&+[ Matrix(K,#mond,1,[sigma(g)(v[i]): i in [1..#mond]]) : g in GAL] / #GAL; 
        if not newnumcoef eq Matrix(K,#mond,1,[0: i in [1..#mond]]) then
            newnumcoef:=UUd!Transpose(newnumcoef);
            break b;
        end if;
    end for;
    newnum:=0;
    for i in [1..#mond] do
        newnum:=newnum+newnumcoef[i]*mond[i];
    end for;

//For denumenator
      
    for b in B do
        newdenumcoef:=Matrix(K,#mond,1,[0: i in [1..#mond]]);
        v:=[denumcoef[i]*b:i in [1..#denumcoef]];
        newdenumcoef:=&+[ Matrix(K,#mond,1,[sigma(g)(v[i]): i in [1..#mond]]) : g in GAL] / #GAL; 
        if not newdenumcoef eq Matrix(K,#mond,1,[0: i in [1..#mond]]) then
            newdenumcoef:=UUd!Transpose(newdenumcoef);
            break b;
        end if;
    end for;
        //Get the polynomials back.
        newnum:=0;
        for i in [1..#mond] do
            newnum:=newnum+newnumcoef[i]*mond[i];
        end for;
        newdenum:=0;
        for i in [1..#mond] do
            newdenum:=newdenum+newdenumcoef[i]*mond[i];
        end for;
             



    return psi,MAT,[newnum,newdenum];
end function; 
