import "findjmap.m" : fieldfind;




declare type CspDat;

declare attributes CspDat: cusp, field, ind, coords;

intrinsic CuspData(cusp::SetCspElt, field::Fld, ind::RngIntElt) -> CspDat
{.}
    c := New(CspDat);
    c`cusp := cusp;
    c`field := field;
    c`ind := ind;
    return c;
end intrinsic;

intrinsic CuspData(cusp::SetCspElt, field::Fld,
		   ind::RngIntElt, coords::Pt) -> CspDat
{.}
    c := New(CspDat);
    c`cusp := cusp;
    c`field := field;
    c`ind := ind;
    c`coords := coords;
    return c;
end intrinsic;

intrinsic Print(c::CspDat, level::MonStgElt)
{.}
    if level eq "Magma" then
	if assigned c`coords then
	    printf "CuspData(%m,%m,%m,%m)", c`cusp, c`field, c`ind, c`coords;
	else
	    printf "CuspData(%m,%m,%m)", c`cusp, c`field, c`ind;
	end if;
	return;
    end if;
    printf "Cusp %o defined over %o", c`cusp, c`field;
    if assigned c`coords then
	printf " with coordinates %o", c`coords;
    end if;
    return;
end intrinsic;

//David has already?
intrinsic CuspOrbits(Gcong) -> SeqEnum[SeqEnum[CspDat]]
{.}
	N:=#BaseRing(Gcong);
    if N eq 1 then
       return [[CuspData(Cusp(1,0), Rationals(), 1)]];
    end if;
    // Step 1 - Determine Galois orbits of cusps and choose one representative from each

  // Computes the action of (Z/NZ)^* on the cusps of X_G.  This corresponds to the action of Gal(Q(zeta_N)/Q) on the cusps.
  vprint User1: "Determining Galois action on cusps.";
  M := CreateModularCurveRec(Gcong);
  gp:=Gcong;
  G := gp;
  G0 := gp;
  GL2 := GL(2,Integers(N));
  SL2 := SL(2,Integers(N));
  U,pi:=UnitGroup(Integers(N));
  im_U := [];
  stabs := [{Integers(N) | } : c in M`cusps];
  for i in [1..Ngens(U)] do
      u := U.i;
      d:=Integers(N)!pi(u);
      b:=GL2![1,0,0,d];
      flag:=exists(g){g: g in G | Determinant(g) eq d};
      error if not flag, "Group G should have full determinant.";
      sigma:=[FindCuspPair(M,SL2!(g^(-1)*GL2!M`cusps[i]*b))[1]: i in [1..#M`cusps]];
      // s:=s join {sigma};
      Append(~im_U, sigma);
      /*
      for i in [1..#M`cusps] do
      if sigma[i] eq i then
          Include(~stabs[i], d);
      end if;
      end for;
      */
  end for;

  s := Set(im_U);
  // Let H and H0 be the intersection of G and G0, respectively, with SL(2,Z/N).  We now computes the action of H0/H on the cusps of X_G.
  H0:=G0 meet SL(2,Integers(N));
  Q,iotaQ:=quo<H0|SL2Intersection(M`G)>;
  for g_ in Generators(Q) do
      g:= g_ @@ iotaQ;
      sigma:=[FindCuspPair(M,SL2!(g^(-1)*SL2!M`cusps[i]))[1]: i in [1..#M`cusps]];
      s:=s join {sigma};
  end for;

  S:=sub<SymmetricGroup(#M`cusps)|s>;
  AS, phi := AbelianGroup(S);
  h := hom< U -> AS | [phi(S!x) : x in im_U]>;
  ind:=[[i:i in O]: O in Orbits(S)];  // orbits of cusps under the actions of G0 and Gal_Q.

  M_lifts := [[LiftMatrix(SL2!M`cusps[i], 1) : i in orb] : orb in ind];
  acs := [[[m_lift[1,1], m_lift[2,1] mod (N*m_lift[1,1]) ] : m_lift in orb]
          : orb in M_lifts];
  cusps := [[Cusp((ac[2] eq 0) select ac[1] else ac[1] mod (N*ac[2]), ac[2])
             : ac in orb] : orb in acs];
  // stabs := [stabs[orb[1]] : orb in ind];
  stabs := [[[pi(x)] : x in phi(Stabilizer(S, orb[1])) @@ h] : orb in ind];
  K := CyclotomicField(N);
  fields := [* *];
  R<x> := PolynomialRing(Rationals());
  for i in [1..#stabs] do
      KK, prim := fieldfind(sub<GL(1, Integers(N)) | [[d] : d in stabs[i]]>, K);
      vprint User1: Sprintf("For cusp %o, field of definition is %o.", cusps[i][1], R!DefiningPolynomial(KK));
      Embed(KK,K,prim);
      if Degree(KK) gt 1 then
	  AssignNames(~KK, [Sprintf("a_%o", i)]);
      end if;
      Append(~fields, KK);
  end for;
  cusps := [[CuspData(cusps[i][j], fields[i], ind[i][j]) :
	     j in [1..#cusps[i]] ] : i in [1..#cusps]];
  vprint User1: Sprintf("Galois orbits of cusps are: %o.", {* #ind[j] : j in [1..#ind]*});
  // printf "Orbits are: %o", cusps;

  return cusps;
end intrinsic;

intrinsic CuspUpdateCoordinates(~cusp::CspDat, X::Crv, F::SeqEnum[SeqEnum])
{.}
   cuspInd := cusp`ind;
   K := cusp`field;
   v := Minimum([Valuation(f[cuspInd]) : f in F]);
   pt := [Coefficient(f[cuspInd], v) : f in F];
   pt_X := ChangeRing(X, Universe(pt))!pt;

   assert K subset Parent(pt_X[1]);

   pt_X := ChangeRing(X, K)!Eltseq(pt_X);
   cusp`coords := pt_X;
   return;
end intrinsic;

intrinsic FindCuspPair(M::Rec, A::GrpMatElt) -> SeqEnum, RngIntElt
{}
    /* Consider a modular curve M=X_G given by a subgroup G of GL_2(Z/NZ).
       Let H be the intersection of G with SL(2,Z/NZ).

       Input:   a matrix A in SL(2,Z/NZ).
       Output:  a pair of integers [i,j] and an e in {1,-1} such that A and e*cusps[i]*[1,1;0,1]^j lie in the same coset H\SL(2,Z/NZ),
                    where cusps[i] is the fixed matrix describing the i-th cusp of M.   When G contains -I, we always return e=1.
    */

    // We search by brute force
    N:=M`N;  SL2:=SL(2,Integers(N));  H:=M`G;  cusps:=M`cusps; cusps:=[SL2!a: a in cusps];
    B:=SL2![1,1,0,1];  A:=SL2!A;
    j:=0;
    repeat
        for i in [1..#cusps] do
            if cusps[i]*B^j*A^(-1) in H then
                return [i,j],1;
            elif -cusps[i]*B^j*A^(-1) in H then
                return [i,j],-1;
            end if;
        end for;
        j:=j+1;
    until false;
end intrinsic;


intrinsic LiftMatrix(A::GrpMatElt, n::RngIntElt) -> GrpMatElt
{
    Input: 
        A: matrix in GL(2,Z/NZ) with N>1,
        n: an integer that is congruent to det(A) modulo N.
    Output:
        A matrix B in M(2,Z) with det(B)=n whose reduction modulo N is A.
 }
    N:=#BaseRing(Parent(A));
    a:=Integers()!A[1,1]; b:=Integers()!A[1,2];
    c:=Integers()!A[2,1]; d:=Integers()!A[2,2];
   
    // The matrix [a,b;c,d] is congruent to A modulo N.
    // We now alter our choices so that a and c are relatively prime.
    if a eq 0 then a:=N; end if;
    if c eq 0 then c:=N; end if;
    if GCD(a,c) ne 1 then
        M:=&*[p: p in PrimeDivisors(a) | GCD(p,N) eq 1];
        ZM:=Integers(M);
        t:=Integers()!( (1-c)*(ZM!N)^(-1));
        c:=c+N*t;
        assert GCD(a,c) eq 1;
    end if;
  
    g:= (n-(a*d-b*c)) div N;  
    _,x0,y0:=Xgcd(a,c);
    x:=g*x0; y:=g*y0;  
    B:=Matrix([[a,b-N*y],[c,d+N*x]]);

    assert GL(2,Integers(N))!B eq A and Determinant(B) eq n;  // check!
    return B;
end intrinsic;




