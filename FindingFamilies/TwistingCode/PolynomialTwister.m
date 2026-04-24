
intrinsic PolynomialTwister(L::SeqEnum, MAT, K) -> SeqEnum
{
   Input: L: A list of polynomials
            MAT: H90 matrix defined over a field K
            K: The field
   Output: psi: L^MAT + Galois descent
}
        prim:=K.1;
        GAL,iota,sigma:=AutomorphismGroup(K);
        B:=Basis(K);
        s:=NumberOfRows(MAT);
        Pol<[x]>:=PolynomialRing(K,s);

        Itw:=[];
        for pol2 in L do
                Append(~Itw,Pol!pol2^MAT);
        end for;
        d:=Degree(L[1]);
        mond:=MonomialsOfDegree(Pol,d);

        coefd:=[];
        for f in Itw do
                Append(~coefd,[MonomialCoefficient(f,m): m in mond]);
        end for;
        nonzerocoefs:=[];
        for j in [1..#coefd] do
                _:=exists(i){i: i in [1..#coefd[j]]|not coefd[j][i] eq 0};
                a:=coefd[j][i];
                nonzerocoefs:=nonzerocoefs cat [a];
        end for;
        tused:=1;
        Lnew:=[];
        goinggood:=true;
        for pol2 in L do

                pol:=Pol!pol2^MAT;;
                d:=Degree(pol);
                mond:=MonomialsOfDegree(Pol,d);
                polcoef:=[MonomialCoefficient(pol,m): m in mond];
                UUd := VectorSpace(K,#mond);
                v:=[K!0: i in [1..#polcoef]];
                newpolcoef:=Matrix(K,#mond,1,[0: i in [1..#mond]]);
                a:=AssociativeArray();
                for b in B do
                        
                        vv:=[polcoef[i]*b:i in [1..#polcoef]];
                        for i in [1..#polcoef] do
                            a[i]:=v[i]+vv[i];
                        end for;
                end for;
                for i in [1..#polcoef] do
                    v[i]:=a[i];
                end for;
                newpolcoef:=&+[ Matrix(K,#mond,1,[sigma(g)(v[i]): i in [1..#mond]]) : g in GAL] / #GAL;
                if not newpolcoef eq Matrix(K,#mond,1,[0: i in [1..#mond]]) then
                        newpolcoef:=UUd!Transpose(newpolcoef);
                        newpol:=0;
                        for i in [1..#mond] do
                                newpol:=newpol+newpolcoef[i]*mond[i];
                        end for;
                        Lnew:=Lnew cat [newpol]; 
                else
                        printf "Allzerooccurred!\n";
                        goinggood:=false;
                    //assert exists(j){j: j in [1..#nonzerocoefs]| Trace(nonzerocoefs[j]) eq 0};
                    t:=prim;
                    l:=1;
                        repeat
                                nonzerocoefs:=[nonzerocoefs[i]*t: i in [1..#nonzerocoefs]];
                                tused:=t;
                                t:=t+1; 
                                l:=l+1;
                                if l eq 50 then t:=t*prim; end if;
                        until not &*[Trace(nonzerocoefs[i]): i in [1..#nonzerocoefs]] eq 0; 
                        break pol2;
                end if;


                
        end for;

        if not goinggood then
                        Lnew:=[];
                Itw:=[tused*Itw[i]: i in [1..#Itw]];
                for pol in Itw do

                        d:=Degree(pol);
                        mond:=MonomialsOfDegree(Pol,d);
                        polcoef:=[MonomialCoefficient(pol,m): m in mond];
                        UUd := VectorSpace(K,#mond);
                        v:=[K!0: i in [1..#polcoef]];
                        newpolcoef:=Matrix(K,#mond,1,[0: i in [1..#mond]]);
                        a:=AssociativeArray();
                        for b in B do
                                
                                vv:=[polcoef[i]*b:i in [1..#polcoef]];
                                for i in [1..#polcoef] do
                                        a[i]:=v[i]+vv[i];
                                end for;
                        end for;
                        for i in [1..#polcoef] do
                        v[i]:=a[i];
                        end for;
                        newpolcoef:=&+[ Matrix(K,#mond,1,[sigma(g)(v[i]): i in [1..#mond]]) : g in GAL] / #GAL;
                        if not newpolcoef eq Matrix(K,#mond,1,[0: i in [1..#mond]]) then
                                newpolcoef:=UUd!Transpose(newpolcoef);
                                newpol:=0;
                                for i in [1..#mond] do
                                        newpol:=newpol+newpolcoef[i]*mond[i];
                                end for;
                                Lnew:=Lnew cat [newpol]; 
                        else
                                assert 1 eq 2;
                        end if;


                
                end for;


        end if;

return Lnew;
end intrinsic;

