ChangeDirectory("/homes/ek693/Project/ComputeModel/OpenImage/main");
load "FindOpenImage.m";
load "/homes/ek693/Project/ComputeModel/OpenImage/SZ-data/RationalFunctions.m";
load "/homes/ek693/Project/ComputeModel/OpenImage/SZ-data/GL2Invariants.m";
ChangeDirectory("/homes/ek693/Project/cummingspauli");
load "pre.m";
load "csg.m";
load "/homes/ek693/Project/cummingspauli/csg4-lev104.dat";
load "/homes/ek693/Project/ComputeModel/FindingFamilies/FamilyData/familycreatecodewithanarrayfosubgroup.m";

function gl2DetIndex(H)
    M,pi:=MultiplicativeGroup(BaseRing(H));
    return Index(M,sub<M|[Inverse(pi)(Determinant(h)):h in Generators(H)]>);
end function;

function ContainsScalars(G)
    // For a subgroup of GL(2,Z/N) with N>1, return true if G contains all the scalar matrices and false otherwise.
    N:=#BaseRing(G);
    GL2:=GL(2,Integers(N));
    U,iota:=UnitGroup(Integers(N));
    return &and [ (GL2![iota(U.i),0,0,iota(U.i)]) in G : i in [1..Ngens(U)] ];
end function;



// Given a subgroup H of SL(2,Z/nZ), returns a (possibly empty) list of subgroups G of GL(2,Z/nZ) of level n
// for which gl2DetIndex(G)=1 and GL2ContainsCC(G)=true and G meet SL(2,Z/nZ) eq H
function gl2QImagesFromSL2eray(H)
    GL2:=GL(2,BaseRing(H));
    SL2:=SL(2,BaseRing(H));
    assert H subset SL2;
    N:=Normalizer(GL2,H);
    Q,pi:=quo<N|H>;
    // we are interested only in subgroups of Q that are isomorphic to the multiplicative group of Z/nZ
    m:=#MultiplicativeGroup(BaseRing(H));
    S:=[Inverse(pi)(K`subgroup) : K in Subgroups(Q)];
    return [G: G in S | gl2DetIndex(G) eq 1 and ContainsScalars(G) and #(SL(2,BaseRing(G)) meet G)/#H eq 1];
end function;

gl2Genus:=GL2Genus;


//Given the Cummings-Pauli data, we compute all the possible calG's arising from the congruence subgroups in CP database. 
//L is the list from CP database. X empty array. What genus we will compute up to depends on what is loaded.
X:=AssociativeArray();
a:=1;
for k in Keys(L) do
    if L[k]`level eq 1 then
        N0:=2;
        SL2:=SL(2,Integers(N0));
        matgens:=[[1,1,0,1],[1,0,1,1]];
    else
        N0:=L[k]`level;
        matgens:=L[k]`matgens;
        SL2:=SL(2,Integers(N0));
    end if;
    
    H:=sub<SL2|matgens>;
  
    N1:=2*LCM([12,N0]);
    

    R:=[ <k, gl2QImagesFromSL2eray(sl2Lift(H,N1))>]; 

    X[k]:=<R[1][2],k>;// first thing is groups, second coordinate is the key in CP
    print(a);
    a:=a+1;
    
end for;





//Then we put all these into one list. 



"Putting them all into a list...";
CC:=AssociativeArray();
a:=0;
for k in Keys(X) do
    if X[k][1] eq [] then continue;
    else
        for i in [1..#X[k][1]] do
            CC[a+i]:=<X[k][1][i],X[k][2]>; //second coordinate in the tuple is its key in CP. First coordinate is groups themselves arising from the cong subgroup
        end for;
        a:=a+#X[k][1];
    end if;
    print(k);
end for;







//Now finding the comm subgroups
//Different name for arrays need to be careful

"Computing the commutator subgroups of our groups...";
COMM:=AssociativeArray();
a:=0;
time0:=Realtime();
for k in Keys(CC) do
            M,gens,i_M:=FindCommutatorSubgroup(CC[k][1]);
            COMM[k]:=<CC[k][1],CC[k][2],M,gens,i_M>; //First coord are group calG arising from the groups search. second coord is the key in CP database
    print(k);
    print(Realtime(time0));
end for;







//This finds the families


//This is a function to find the families by finding the groups in [calG,calG]/B.


function gl2QImagesForFamiliiesEray(GGG,H)
    N1:=#BaseRing(GGG);
    N2:=#BaseRing(H);
    N:=LCM([N1,N2]);
    GGG:=sl2Lift(GGG,N);
    H:=sl2Lift(H,N);
    assert H subset GGG;
    Q,pi:=quo<GGG|H>;
    S:=[Inverse(pi)(K`subgroup) : K in Subgroups(Q)];
    return [T: T in S];
end function;

"Finding all the families";

FAM1:=AssociativeArray();
time0:=Realtime();
for k in Keys(COMM) do
    if L[COMM[k][2]]`level eq 1 then
        N0:=2;
        SL2:=SL(2,Integers(N0));
        matgens:=[[1,1,0,1],[1,0,1,1]];
        R:=[ <k, gl2QImagesForFamiliiesEray(sub<SL(2,Integers(2))|matgens>,sub<SL(2,Integers(COMM[k][3]))|COMM[k][4]>)>];
    else
        R:=[ <k, gl2QImagesForFamiliiesEray(sub<SL(2,Integers(L[COMM[k][2]]`level))|L[COMM[k][2]]`matgens>,sub<SL(2,Integers(COMM[k][3]))|COMM[k][4]>)>];
    end if;
       
       
           
            FAM1[k]:=<R,COMM[k][1],COMM[k][2]>; //second coordinate is group and third coordinate is key. Frist coordinate are the list above.
    print(k);
    print(Realtime()-time0);
end for;

c:=0;
for k in Keys(FAM1) do
    c:=c+#FAM1[k][1][1][2];
end for;






"Creating family rec for all new families";


//Here for all the families we check for the genus of the family. If it is bigger than for we put it into aan array.
BS:=AssociativeArray();
time3:=Realtime();
a:=1;
for k in Keys(FAM1) do
    if FAM1[k][1][1][2] eq [] then continue;
    else
        for i in [1..#FAM1[k][1][1][2]] do
            g:=gl2Genus(FAM1[k][1][1][2][i]);
            if g gt 1 then continue; 
            else 
                BS[a]:=CreateFamilyRecSubgroup(FAM1[k][2],FAM1[k][1][1][2][i]); //first coordinate is B, second is calG, third one is calG's key in CP
                a:=a+1;
            end if;
        end for;
    end if;
    print(k);
end for;




 I:=Open("/homes/ek693/Project/ComputeModel/FindingFamilies/ConstructingAgreeable/KendiFamily.dat", "w");
    for k in Keys(BS) do
        x:=BS[k];
        WriteObject(I, x);
    end for;




//Various representativefinder functions. I am not sure if I will use them





//The following is the function for finding the representatives in a correct way. Need to make it better tho.

function RepresentativeFinderMaximal(B,calG)
    time0:=Realtime();
    N1:=#BaseRing(B);
    N2:=#BaseRing(calG);
    N:=LCM([N1,N2]);
    calG:=gl2Lift(calG,N);
    B:=sl2Lift(B,N);
    assert B subset calG;

    ToDo:={calG};  // groups we still need to address
    Done:={};      // groups already handled

    REP:=[];
    repeat
        
        for a in ToDo do
            G:=a;
            ToDo:=ToDo diff {a};
            Done:=Done join {a};
            M:=#BaseRing(a);
            P:=PrimeDivisors(M);
            T:=[];
            for i in [1..#P] do
                G:=a;
                T[i]:=M*P[i];
                G:=gl2Lift(G,T[i]);
                B3:=sl2Lift(B,T[i]);
                max:= MaximalSubgroups(G);
                for H in max do
                    if B3 subset H`subgroup and gl2DetIndex(H`subgroup) eq 1  then
                        ToDo:=ToDo join {H`subgroup};
                        if B3 eq H`subgroup meet SL(2,Integers(T[i])) then
                            Append(~REP,H`subgroup);
                            return H`subgroup;
                        end if;
                    end if;
                end for;
            end for;
        end for;
        ToDo:=ToDo diff Done;  
    until ToDo eq {} or REP ne [];
    return REP;
end function;

// checkingeverything.m is where I use the above code to check all the families that are not in 
