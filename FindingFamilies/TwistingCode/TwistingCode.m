function Twist(M,xi,K, calG)   
//BIG PROBLEM! calG cannot be the whole thing.
 // Input: M: a modular curve in the sense of Zywina. For now we assume that the curve is given by its canonical model. It might be thought as X_G, where G is a group we are considering. We will think about the other cases.
// xi: Gal(K/Q)-> GL(M`genus,K) 1-cocycle. This is a cocycle that extends from the Aut(M) (usually via AutomorphismOfModularForms function of Zywina).    
// It factors through the field K.
// calG: calG is the group which contains G as a normal group and F(calG,G) is the family that G lies in.
// Output: a sequence "psi" of homogeneous polynomials in Q[x_1,..,x_g], defining the twisted curve.
// Final goal is to output this curve as a modular curve a la Z.
//For now we are working over Q.
//Assuming H90 and Z's FindOpenImage are loaded.
I:=M`psi;
// I guess I can just make this FindModel instead of FindCanonicalModel. Note I did and it should work especially considering I've added G0.
g:=M`genus;
GAL,iota,sigma:=AutomorphismGroup(K);
s:=#M`F0;

MAT:=Transpose(H90(s,K,Rationals(),GAL,sigma,xi));
Pol<[x]>:=PolynomialRing(K,s); 
PP:=ProjectiveSpace(K,s-1);  
Itw:=[];
for i in [1..#I] do
   Append(~Itw,Pol!I[i]^MAT);  
end for;


//Get the coefficent vectors of polynomials in I2tw to do Galois descent. Will this always work? I am assuming that all the polynomials in I are homogeneous of degree 2. Okay at worst they will up to deg 4 thanks to davids atkinlehner paper.
mon2:=MonomialsOfDegree(Pol,2);
mon3:=MonomialsOfDegree(Pol,3);
mon4:=MonomialsOfDegree(Pol,4);
mon:=mon2 join mon3 join mon4;
//If the genus is high this might be computationally unfeasiable as there will be a lot of such monomials. However this is linear algebra so I am not sure if it will actually be a problem. We will see.

coef:=[];
for f in Itw do 
   Append(~coef,[MonomialCoefficient(f,m): m in mon]);
end for; 


coeff:=[];






for j in [1..#coef] do //This is so that the trace map is never zero. However I am not sure if I am sure to get the correct dimension. over Q[x]?
    coeff[j]:=[];
    for k in [1..#coef[j]] do
        if coef[j][k] ne 0 then
            x:=coef[j][k];
            break k;
        end if;
    end for;
    for k in [1..#coef[j]] do
        coeff[j][k]:=coef[j][k]/x;
    end for;

end for;





//Starting Galois descent now
   U := VectorSpace(K,#mon);
    V:=sub<U| coeff>; 

    
     

S:={}; 





 
//Assuming V is Galois invariant
    i:=1; 
    while i lt #coeff+1 do 

 

        v:=coeff[i]; 
        tr:=&+[ Matrix(K,#mon,1,[sigma(g)(v[i]): i in [1..#mon]]) : g in GAL] / #GAL; 
        tr:=V!Transpose(tr); 
        if Dimension(sub<V|S join {tr}>) gt Dimension(sub<V|S>) then 
          S:=S join {tr}; 

        end if; 
        i:=i+1; 
    end while; 

I2G:=[];


for v in S do 
   f:=0;
   for i in [1..#mon] do
   f:=f+v[i]*mon[i];
   end for;
   Append(~I2G,f);   
end for; 

return I2G;



end function; 