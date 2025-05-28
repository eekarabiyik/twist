//Initial work for getting plane models from subrepresentations. Except finding actual plane models, it works=. I.e. It finds the subrepresentations if it exists and finds the modular forms that spand the subrepresentation.
//Need to ask how checking for the validity of plane models works.

ChangeDirectory("/homes/ek693/Main/FindingFamilies");
AttachSpec("../spec");
FAM:=LoadFamilies(["/homes/ek693/Main/FindingFamilies/FamilyDataFiles/Families1new.dat","/homes/ek693/Main/FindingFamilies/FamilyDataFiles/Families2new.dat"]);

gonality_equals_2:=[ "8B3", "10B3", "12C3", "12D3", "12E3", "12F3", "12G3", "12H3", "12K3",
"12L3", "14A3", "14C3", "14F3", "15F3", "15G3", "16B3", "16C3", "16D3", "16E3", "16F3",
"16I3", "16J3", "16M3", "16S3", "18A3", "18C3", "18F3", "18G3", "20C3", "20F3", "20G3",
"20H3", "20I3", "20J3", "20M3", "20O3", "21A3", "21B3", "21D3", "24A3", "24B3", "24C3",
"24G3", "24I3", "24K3", "24L3", "24M3", "24S3", "24U3", "24V3", "24W3", "28C3", "28E3",
"30B3", "30G3", "30J3", "30K3", "30L3", "32B3", "32C3", "32D3", "32H3", "32K3", "32M3",
"33C3", "34B3", "35A3", "36E3", "36F3", "36G3", "39A3", "40D3", "40E3", "40F3", "40I3",
"41A3", "42E3", "48C3", "48E3", "48F3", "48H3", "48I3", "48J3", "48M3", "50A3", "54A3",
"60C3", "60D3", "64A3", "96A3", "18B4", "25A4", "25D4", "32B4", "36C4", "42A4", "44B4",
"47A4", "48C4", "50A4", "50D4", "10A5", "14C5", "16G5", "18A5", "24A5", "24D5", "26A5",
"30C5", "30F5", "36A5", "36B5", "36H5", "40A5", "42A5", "44B5", "45A5", "45C5", "46A5",
"48A5", "48E5", "48F5", "48G5", "48H5", "50A5", "50D5", "50F5", "52B5", "54A5", "57A5",
"58A5", "59A5", "60A5", "96A5", "48A6", "71A6", "32E7", "48N7", "56B7", "64D7", "82B7",
"96A7", "93A8", "50A9", "50D9", "96B9", "48B11", "72A11", "96B11"];



function RandomGL3ZFast(small_coeff_bound)
    // Generates a random unimodular matrix by constructing an upper-triangular matrix
    // with ±1 on diagonal and small integer coefficients elsewhere
    
    // Diagonal entries (must be ±1)
    d1 := Random([-1,1]);
    d2 := Random([-1,1]);
    d3 := Random([-1,1]);
    
    // Upper triangular entries
    u12 := Random(-small_coeff_bound, small_coeff_bound);
    u13 := Random(-small_coeff_bound, small_coeff_bound);
    u23 := Random(-small_coeff_bound, small_coeff_bound);
    
    // Form the upper triangular matrix
    M := Matrix(3, 3, [Rationals()!d1, u12, u13,
                       0, d2, u23,
                       0,  0, d3]);
    
    return M, M^-1;
end function;

function RandomGLnQ(n, coeff_bound)
    // Generates a random n x n invertible matrix over Q with small integer numerators/denominators
    // coeff_bound: bound on absolute value of numerators and denominators
    // Returns M and M^-1
    
    repeat
        // Generate random numerators and denominators
        numerators := [Random(-coeff_bound, coeff_bound) : i in [1..n^2]];
        denominators := [Random(1, coeff_bound) : i in [1..n^2]];  // denominators are positive
        
        // Construct the matrix with entries numerators[i]/denominators[i]
        M := Matrix(n, n, [numerators[i]/denominators[i] : i in [1..n^2]]);
        
        // Check if M is invertible (nonzero determinant)
        if Determinant(M) ne 0 then
            return M, M^-1;
        end if;
    until false;
end function;



    wawa:=[k: k in Keys(FAM)|assigned FAM[k]`H and FAM[k]`fine eq false and FAM[k]`genus eq 5 and not FAM[k]`M`CPname in gonality_equals_2 and GL2Index(FAM[k]`H)/GL2Index(FAM[k]`calG) gt 4];
    //k:=15591;
    //k:=12214;

for k in wawa do
    assert assigned FAM[k]`fine;
  

        G:=FAM[k]`H;
        calG:=FAM[k]`calG;
        //if #BaseRing(G) eq 2 and #BaseRing(G) eq #BaseRing(calG) and G eq calG then continue; end if; //The family consisting of only the j line.
        //printf "Making the model\n";
        M:=CreateModularCurveRec(G);
        //printf "Computing the model\n";
        M:=FindModelOfXG(M: G0:=calG);
        FAM[k]`M:=M;
        //if not GL2Level(calG) eq 1 then 
        MG:=CreateModularCurveRec(calG);
        MG:=FindModelOfXG(MG);
        FAM[k]`calGModCurve:=MG;
        // end if;
        //"Computing AutOfMF";
        H:=G;
        calG:=GL2Lift(calG,LCM([#BaseRing(calG),#BaseRing(H)]));
        M:=IncreaseModularFormPrecision(M,[Maximum(M`prec[i]+2,((M`prec_sturm[i]-1) * (M`sl2level div M`widths[i]))+5) : i in [1..M`vinf]]);
        for i in [1..Ngens(calG)] do
            FAM[k]`AOfMF[i]:=Transpose(AutomorphismOfModularForms(M,M`F0,calG.i: OverQ:=true));
        end for;    



calG:=GL2Lift(calG,#BaseRing(G));
DD,DDmap:=quo<calG|G>;

//Abelianize for charactar table
DDAbel,abelmap:=AbelianGroup(quo<calG|G>);
table:=CharacterTable(DDAbel);
matrixo:=[];
//character:=(table[1]+table[2]+table[3]);



//while L eq [] do
//basechange:= RandomGLnQ(M`genus,10);
//MF:=F0Twister(M`F0,basechange);



MF:=M`F0;


//Writing the character in terms of magma
class:=Classes(DDAbel);
R:=CharacterRing(DDAbel);
modformchar:=[];
for i in [1..#class] do
    cl:=class[i];
    g:=cl[3];
    //for char in table do
    //end for;
    matg:=g @@ abelmap;
    a:=matg @@ DDmap;
    Y:=AutomorphismOfModularForms(M,MF,a : OverQ:=true, k:=0);
    tr:=Trace(Y);
    Append(~modformchar,tr);
    //coef:=character(-g);
    matrixo[i]:=Y;
end for;
ourchar:=R!modformchar;



//This is the number of characters that show up in the decomposition
decompositionarray:=[];
double:=[[x,y]: x,y in Keys(table)|not x eq y and x lt y];
triple:=[[x,y,z]: x,y,z in Keys(table)|(not x eq y and not x eq z and not y eq z) and (x lt y and y lt z)];
//The table order so we can get the characters later.
//for k in Keys(table) join {-1} do
    //if k eq -1 then decompositionarray[k]:=0;
    //decompositionarray[k]:=InnerProduct(table[k],ourchar);
//end for;



for k in [1..#table] do
    decompositionarray[k]:=Integers()!InnerProduct(table[k],ourchar);
end for;


[decompositionarray[k]: k in [1..#decompositionarray]];



c:=[];

/*
var1:=exists(c1){c: c in Keys(table)|(decompositionarray[c] mod 3) eq 0 and not decompositionarray[c] eq 0};
if not var1 then c1:=[]; end if;
if var1 then
    c:=[c1];
end if;
*/



c2list:=[c: c in double| not decompositionarray[c[1]] eq 0 and ((decompositionarray[c[1]]+decompositionarray[c[2]]) mod 3) eq 0 and &and[&+[table[c[i]][k] : i in [1,2]] in Rationals() eq true:k in [1..#table[c[1]]]]];
if c2list eq [] then
clist:=[c: c in triple| not decompositionarray[c[1]] eq 0 and ((decompositionarray[c[1]]+decompositionarray[c[2]]+decompositionarray[c[3]]) mod 3) eq 0 and &and[&+[table[c[i]][k] : i in [1,2,3]] in Rationals() eq true:k in [1..#table[c[1]]]]];
else
clist:=c2list;
end if;
for c in clist do

projector1:=&+[((&+[(table[c[i]]): i in [1..#c]])(-class[j][3]))*matrixo[j]: j in [1..#class]];
projector:=EchelonForm(projector1);
RemoveZeroRows(~projector);

    while Nrows(projector) gt 3 do
        RemoveRow(~projector,4);
    end while;



MFdoom:=[];
for v in Rows(projector) do
    w:=v;
    MFdoom:=MFdoom cat [[&+[v[i]*MF[i][c]:  i in [1..M`genus] ]:c in [1..#M`cusps]]];
end for;




L:=[];


L:=PlaneModelsFromQExpansionsThree(M,MFdoom,projector);
if not L eq [] then
FAM[k]`quomap:=AssociativeArray();
 M:=IncreaseModularFormPrecision(M,[Maximum(M`prec[i]+2,((M`prec_sturm[i]-1) * (M`sl2level div M`widths[i]))+5) : i in [1..M`vinf]]);
        for i in [1..Ngens(calG)] do
            i;
            A:=Transpose(AutomorphismOfModularForms(M,MF,calG.i));
            A2:=ZeroMatrix(Rationals(), #MF,#MF);
            for j in [1..#MF] do
                for o in [1..#MF] do
                    A2[j][o]:=Rationals()!A[j][o];
                end for;
            end for;
            FAM[k]`quomap[i]:=A2;//This works except cyclotomic
        end for;    
        break;
end if;
end for;
//end while;

L;

end for;
