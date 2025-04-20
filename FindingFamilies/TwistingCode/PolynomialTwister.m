
intrinsic PolynomialTwister(L::SeqEnum, MAT, K) -> SeqEnum
{
   Input: L: A list of polynomials
            MAT: H90 matrix defined over a field K
            K: The field
   Output: psi: L^MAT + Galois descent
}
   GAL,iota,sigma:=AutomorphismGroup(K);
        B:=Basis(K);
        s:=NumberOfRows(MAT);
        Pol<[x]>:=PolynomialRing(K,s);
        "LLL";
        L;
   


        Lnew:=[];
        for pol2 in L do

                pol:=Pol!pol2^MAT;;
                d:=Degree(pol);
                mond:=MonomialsOfDegree(Pol,d);
                polcoef:=[MonomialCoefficient(pol,m): m in mond];
                UUd := VectorSpace(K,#mond);
                for b in B do
                        newpolcoef:=Matrix(K,#mond,1,[0: i in [1..#mond]]);
                        v:=[polcoef[i]*b:i in [1..#polcoef]];
                        newpolcoef:=&+[ Matrix(K,#mond,1,[sigma(g)(v[i]): i in [1..#mond]]) : g in GAL] / #GAL;
                        if not newpolcoef eq Matrix(K,#mond,1,[0: i in [1..#mond]]) then
                                newpolcoef:=UUd!Transpose(newpolcoef);
                                break b;
                        end if;
                end for;
                newpol:=0;
                for i in [1..#mond] do
                        newpol:=newpol+newpolcoef[i]*mond[i];
                end for;
                Lnew:=Lnew cat [newpol]; 
        end for;

return Lnew;
end intrinsic;


//I guess for LLL I will get the Z-coeff,  get the matrix from the coefficients, apply LLL, get a new matrix that transforms it and apply it to do j map again.
