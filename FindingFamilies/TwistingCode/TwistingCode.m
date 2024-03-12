function Twist(M,xi,K, calG)   
// Input: M: a modular curve in the sense of Zywina. 
// xi: Gal(K/Q)-> GL(M`genus,K) 1-cocycle. This is a cocycle that extends from the Aut(M) (usually via AutomorphismOfModularForms function of Zywina).    
// It factors through the field K.
// calG: calG is the group which contains G as a normal group and F(calG,G) is the family that G lies in.
// Output: a sequence "psi" of homogeneous polynomials in Q[x_1,..,x_#M`F0], defining the twisted curve.
//For now we are working over Q.
//Assuming H90 and Z's FindOpenImage are loaded.
I:=M`psi;
g:=M`genus;
GAL,iota,sigma:=AutomorphismGroup(K);
s:=#M`F0;
//Transpose matrix because of Galois action used.   
MAT:=Transpose(H90(s,K,Rationals(),GAL,sigma,xi));
Pol<[x]>:=PolynomialRing(K,s); 
PP:=ProjectiveSpace(K,s-1);  
//Applying the matrix to the polynomials already computed
Itw:=[];
for i in [1..#I] do
   Append(~Itw,Pol!I[i]^MAT);  
end for;


//Get the coefficent vectors of polynomials in I2tw to do Galois descent. 
mon2:=MonomialsOfDegree(Pol,2);
mon3:=MonomialsOfDegree(Pol,3);
mon4:=MonomialsOfDegree(Pol,4);
mon:=mon2 join mon3 join mon4;

coef:=[];
for f in Itw do 
   Append(~coef,[MonomialCoefficient(f,m): m in mon]);
end for; 

//We will scale the coordinate vectors a little to be able to do Galois Descent
coeff:=[];






for j in [1..#coef] do //This is so that the trace map is never zero.
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




/*
Note to David Roe/LMFDB
The matrix we get from the H90 code has coefficients in the number field we use. Resulting polynomals/Ideal are actually defined
over Rationals, but we need to do a Galois descent to get polynomials over Rationals.
When we act on the map to the j-line via 

*/










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