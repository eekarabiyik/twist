intrinsic TwistCurve(psi, xi/*::HomGrp*/, K::Fld : redcub:=false) -> SeqEnum[RngMPolElt], AlgMatElt, RngIntElt,Any
{
    Input:
      - M: a modular curve in the sense of Zywina.
      - xi: Gal(K/Q)-> GL(M`genus,K) 1-cocycle. This is a cocycle that extends from the Aut(M) (usually via AutomorphismOfModularForms function of Zywina).
      - K: the number field through which K factors
      - redcube: if this is true simplified cubics are produced. It is suggested that this is almost always set to true.
    Output:
      - a sequence "psi" of homogeneous polynomials in Q[x_1,..,x_#M`F0], defining the twisted curve.
      - the H90 matrix used
      - the size of the H90 matrix, which is the same as #M`F0
}
    I:=psi;
    //g:=M`genus;
    GAL,iota,sigma:=AutomorphismGroup(K);
    s:= Nrows(Id(Codomain(xi)));
    //Transpose matrix because of Galois action used.
    MAT:=Transpose(H90(s,K,Rationals(),GAL,sigma,xi)); 
    //MAT1:=H90(s,K,Rationals(),GAL,sigma,xi);
    //MAT:=MAT1^(-1);
    Pol<[x]>:=PolynomialRing(K,s);
    PP:=ProjectiveSpace(K,s-1);
    //Applying the matrix to the polynomials already computed
    Itw:=[];
    for i in [1..#I] do
        Append(~Itw,Pol!I[i]^MAT);
    end for;
    unrefined:=Itw;

    //Get the coefficent vectors of polynomials in Itw to do Galois descent.
    mon2:=MonomialsOfDegree(Pol,2);
    mon3:=MonomialsOfDegree(Pol,3);
    mon4:=MonomialsOfDegree(Pol,4);
    mon:=mon2 join mon3 join mon4;


    coef2:=[];
    for f in Itw do
        Append(~coef2,[MonomialCoefficient(f,m): m in mon2]);
    end for;

    coef3:=[];
    for f in Itw do
        Append(~coef3,[MonomialCoefficient(f,m): m in mon3]);
    end for;


    coef4:=[];
    for f in Itw do
        Append(~coef4,[MonomialCoefficient(f,m): m in mon4]);
    end for;


    //We now do Galois descent separately for quadrics, cubics and quartics.


    UU2 := VectorSpace(K,#mon2);
    VV2:=sub<UU2| coef2>;
    // use this dimension

    I2G:=[];
    B:=Basis(K);
    if Dimension(VV2) ne 0 then
        coeff2:=[];
        i:=1;
        for j in [1..#coef2] do //This is so that the trace map is never zero. However I am not sure if I am sure to get the correct dimension. over Q[x]?
            for b in B do
                coeff2[i]:=[];
                for k in [1..#coef2[j]] do
                    coeff2[i]:= coeff2[i] cat [coef2[j][k]*b];
                end for;
                i:=i+1;
            end for;
        end for;

        //Starting Galois descent now
        U2 := VectorSpace(K,#mon2);
        V2:=sub<U2| coeff2>;
        S2:={};
        i:=1;
        while i lt #coeff2+1 do
            v:=coeff2[i];
            tr:=&+[ Matrix(K,#mon2,1,[sigma(g)(v[i]): i in [1..#mon2]]) : g in GAL] / #GAL;
            tr:=V2!Transpose(tr);
            if Dimension(sub<V2|S2 join {tr}>) gt Dimension(sub<V2|S2>) then
                S2:=S2 join {tr};
                if Dimension(sub<V2|S2>) eq #coeff2 then i:=#coeff2+1; end if;
            end if;
            i:=i+1;
        end while;

        I2G:=[];
        for v in S2 do
            f:=0;
            for i in [1..#mon2] do
                f:=f+v[i]*mon2[i];
            end for;
            Append(~I2G,f);
        end for;
    end if;

    //Now for cubics.
    UU3 := VectorSpace(K,#mon3);
    VV3:=sub<UU3| coef3>;
    // use this dimension
    I3G:=[];
    if Dimension(VV3) ne 0 then
        coeff3:=[];
        i:=1;
        for j in [1..#coef3] do //This is so that the trace map is never zero. However I am not sure if I am sure to get the correct dimension. over Q[x]?
            for b in B do
                coeff3[i]:=[];
                for k in [1..#coef3[j]] do
                    coeff3[i]:= coeff3[i] cat [coef3[j][k]*b];
                end for;
                i:=i+1;
            end for;
        end for;

        //Starting Galois descent now
        U3 := VectorSpace(K,#mon3);
        V3:=sub<U3| coeff3>;
        S3:={};
        i:=1;
        while i lt #coeff3+1 do
            v:=coeff3[i];
            tr:=&+[ Matrix(K,#mon3,1,[sigma(g)(v[i]): i in [1..#mon3]]) : g in GAL] / #GAL;
            tr:=V3!Transpose(tr);
            if Dimension(sub<V3|S3 join {tr}>) gt Dimension(sub<V3|S3>) then
                S3:=S3 join {tr};
                if Dimension(sub<V3|S3>) eq #coeff3 then i:=#coeff3+1;; end if;
            end if;
            i:=i+1;
        end while;
        I3G:=[];
        for v in S3 do
            f:=0;
            for i in [1..#mon3] do
                f:=f+v[i]*mon3[i];
            end for;
            Append(~I3G,f);
        end for;
    end if;

    //Quartics:
    UU4 := VectorSpace(K,#mon4);
    VV4:=sub<UU4| coef4>;
    I4G:=[];
    if Dimension(VV4) ne 0 then
        coeff4:=[];
        i:=1;
        for j in [1..#coef4] do //This is so that the trace map is never zero. However I am not sure if I am sure to get the correct dimension. over Q[x]?
            for b in B do
                coeff4[i]:=[];
                for k in [1..#coef4[j]] do
                    coeff4[i]:= coeff4[i] cat [coef4[j][k]*b];
                end for;
                i:=i+1;
            end for;
        end for;
        //Starting Galois descent now
        U4 := VectorSpace(K,#mon4);
        V4:=sub<U4| coeff4>;
        S4:={};
        i:=1;
        while i lt #coeff4+1 do
            v:=coeff4[i];
            tr:=&+[ Matrix(K,#mon4,1,[sigma(g)(v[i]): i in [1..#mon4]]) : g in GAL] / #GAL;
            tr:=V4!Transpose(tr);
            if Dimension(sub<V4|S4 join {tr}>) gt Dimension(sub<V4|S4>) then
                S4:=S4 join {tr};
                if Dimension(sub<V4|S4>) eq #coeff4 then i:=#coeff4+1; end if;
            end if;
            i:=i+1;
        end while;

        I4G:=[];
        for v in S4 do
            f:=0;
            for i in [1..#mon4] do
                f:=f+v[i]*mon4[i];
            end for;
            Append(~I4G,f);
        end for;
    end if;

    if redcub then
        if Dimension(VV2) ne 0 and Dimension(VV3) ne 0 then
            V:=VectorSpace(Rationals(),#mon3);
            W:=sub<V| [V![MonomialCoefficient(x[i]*f,m): m in mon3] : i in [1..s], f in I2G]>;
            V3:=sub<V| [V![MonomialCoefficient(f,m): m in mon3] : f in I3G]>;
            J:=[];
            i:=1;
            while Dimension(W) lt Dimension(V3) do
                v:=V![MonomialCoefficient(I3G[i],m): m in mon3];
                if v notin W then
                    W:=sub<V|Generators(W) join {v}>;
                    J:=J cat [I3G[i]];
                end if;
                i:=i+1;
            end while;
            I3G := J;
        end if;
    end if;

    return I2G cat I3G cat I4G, MAT,s,unrefined;
end intrinsic;



intrinsic mat3map(A) -> Any
{}
    a:=A[1][1]; b:=A[1][2]; c:=A[2][1]; d:=A[2][2];
    return (1/(a*d-b*c))*Matrix(BaseRing(A),3,3,[a^2,2*a*b,b^2,a*c,a*d+b*c,b*d,c^2,2*c*d,d^2]);
end intrinsic;


intrinsic TwistCurveGenus0(psi, xi/*::HomGrp*/, K::Fld : redcub:=false) -> SeqEnum[RngMPolElt], AlgMatElt, RngIntElt
{
    Input:
      - M: a modular curve in the sense of Zywina.
      - xi: Gal(K/Q)-> GL(M`genus,K) 1-cocycle. This is a cocycle that extends from the Aut(M) (usually via AutomorphismOfModularForms function of Zywina).
      - K: the number field through which K factors
      - redcube: if this is true simplified cubics are produced. It is suggested that this is almost always set to true.
    Output:
      - a sequence "psi" of homogeneous polynomials in Q[x_1,..,x_#M`F0], defining the twisted curve.
      - the H90 matrix used
      - the size of the H90 matrix, which is the same as #M`F0
}
    I:=psi;
    //g:=M`genus;
    GAL,iota,sigma:=AutomorphismGroup(K);
    s:= Nrows(Id(Codomain(xi)));
    //Transpose matrix because of Galois action used.
    //MAT:=Transpose(H90(s,K,Rationals(),GAL,sigma,xi)); 
    MAT1:=H90(s,K,Rationals(),GAL,sigma,xi);
    MAT:=MAT1^(-1);
    Pol<[x]>:=PolynomialRing(K,s);
    PP:=ProjectiveSpace(K,s-1);
    //Applying the matrix to the polynomials already computed
    Itw:=[];
    for i in [1..#I] do
        Append(~Itw,Pol!I[i]^MAT);
    end for;


    //Get the coefficent vectors of polynomials in Itw to do Galois descent.
    mon2:=MonomialsOfDegree(Pol,2);
    mon3:=MonomialsOfDegree(Pol,3);
    mon4:=MonomialsOfDegree(Pol,4);
    mon:=mon2 join mon3 join mon4;


    coef2:=[];
    for f in Itw do
        Append(~coef2,[MonomialCoefficient(f,m): m in mon2]);
    end for;

    coef3:=[];
    for f in Itw do
        Append(~coef3,[MonomialCoefficient(f,m): m in mon3]);
    end for;


    coef4:=[];
    for f in Itw do
        Append(~coef4,[MonomialCoefficient(f,m): m in mon4]);
    end for;


    //We now do Galois descent separately for quadrics, cubics and quartics.


    UU2 := VectorSpace(K,#mon2);
    VV2:=sub<UU2| coef2>;
    // use this dimension

    I2G:=[];
    B:=Basis(K);
    if Dimension(VV2) ne 0 then
        coeff2:=[];
        i:=1;
        for j in [1..#coef2] do //This is so that the trace map is never zero. However I am not sure if I am sure to get the correct dimension. over Q[x]?
            for b in B do
                coeff2[i]:=[];
                for k in [1..#coef2[j]] do
                    coeff2[i]:= coeff2[i] cat [coef2[j][k]*b];
                end for;
                i:=i+1;
            end for;
        end for;

        //Starting Galois descent now
        U2 := VectorSpace(K,#mon2);
        V2:=sub<U2| coeff2>;
        S2:={};
        i:=1;
        while i lt #coeff2+1 do
            v:=coeff2[i];
            tr:=&+[ Matrix(K,#mon2,1,[sigma(g)(v[i]): i in [1..#mon2]]) : g in GAL] / #GAL;
            tr:=V2!Transpose(tr);
            if Dimension(sub<V2|S2 join {tr}>) gt Dimension(sub<V2|S2>) then
                S2:=S2 join {tr};
                if Dimension(sub<V2|S2>) eq #coeff2 then i:=#coeff2+1; end if;
            end if;
            i:=i+1;
        end while;

        I2G:=[];
        for v in S2 do
            f:=0;
            for i in [1..#mon2] do
                f:=f+v[i]*mon2[i];
            end for;
            Append(~I2G,f);
        end for;
    end if;

    //Now for cubics.
    UU3 := VectorSpace(K,#mon3);
    VV3:=sub<UU3| coef3>;
    // use this dimension
    I3G:=[];
    if Dimension(VV3) ne 0 then
        coeff3:=[];
        i:=1;
        for j in [1..#coef3] do //This is so that the trace map is never zero. However I am not sure if I am sure to get the correct dimension. over Q[x]?
            for b in B do
                coeff3[i]:=[];
                for k in [1..#coef3[j]] do
                    coeff3[i]:= coeff3[i] cat [coef3[j][k]*b];
                end for;
                i:=i+1;
            end for;
        end for;

        //Starting Galois descent now
        U3 := VectorSpace(K,#mon3);
        V3:=sub<U3| coeff3>;
        S3:={};
        i:=1;
        while i lt #coeff3+1 do
            v:=coeff3[i];
            tr:=&+[ Matrix(K,#mon3,1,[sigma(g)(v[i]): i in [1..#mon3]]) : g in GAL] / #GAL;
            tr:=V3!Transpose(tr);
            if Dimension(sub<V3|S3 join {tr}>) gt Dimension(sub<V3|S3>) then
                S3:=S3 join {tr};
                if Dimension(sub<V3|S3>) eq #coeff3 then i:=#coeff3+1;; end if;
            end if;
            i:=i+1;
        end while;
        I3G:=[];
        for v in S3 do
            f:=0;
            for i in [1..#mon3] do
                f:=f+v[i]*mon3[i];
            end for;
            Append(~I3G,f);
        end for;
    end if;

    //Quartics:
    UU4 := VectorSpace(K,#mon4);
    VV4:=sub<UU4| coef4>;
    I4G:=[];
    if Dimension(VV4) ne 0 then
        coeff4:=[];
        i:=1;
        for j in [1..#coef4] do //This is so that the trace map is never zero. However I am not sure if I am sure to get the correct dimension. over Q[x]?
            for b in B do
                coeff4[i]:=[];
                for k in [1..#coef4[j]] do
                    coeff4[i]:= coeff4[i] cat [coef4[j][k]*b];
                end for;
                i:=i+1;
            end for;
        end for;
        //Starting Galois descent now
        U4 := VectorSpace(K,#mon4);
        V4:=sub<U4| coeff4>;
        S4:={};
        i:=1;
        while i lt #coeff4+1 do
            v:=coeff4[i];
            tr:=&+[ Matrix(K,#mon4,1,[sigma(g)(v[i]): i in [1..#mon4]]) : g in GAL] / #GAL;
            tr:=V4!Transpose(tr);
            if Dimension(sub<V4|S4 join {tr}>) gt Dimension(sub<V4|S4>) then
                S4:=S4 join {tr};
                if Dimension(sub<V4|S4>) eq #coeff4 then i:=#coeff4+1; end if;
            end if;
            i:=i+1;
        end while;

        I4G:=[];
        for v in S4 do
            f:=0;
            for i in [1..#mon4] do
                f:=f+v[i]*mon4[i];
            end for;
            Append(~I4G,f);
        end for;
    end if;

    if redcub then
        if Dimension(VV2) ne 0 and Dimension(VV3) ne 0 then
            V:=VectorSpace(Rationals(),#mon3);
            W:=sub<V| [V![MonomialCoefficient(x[i]*f,m): m in mon3] : i in [1..s], f in I2G]>;
            V3:=sub<V| [V![MonomialCoefficient(f,m): m in mon3] : f in I3G]>;
            J:=[];
            i:=1;
            while Dimension(W) lt Dimension(V3) do
                v:=V![MonomialCoefficient(I3G[i],m): m in mon3];
                if v notin W then
                    W:=sub<V|Generators(W) join {v}>;
                    J:=J cat [I3G[i]];
                end if;
                i:=i+1;
            end while;
            I3G := J;
        end if;
    end if;

    return I2G cat I3G cat I4G, MAT,s;
end intrinsic;
