//This is a rudimantary version of the Twisting Code. The j-map is included, as well as a boolean for being QQ-gonality 2
//The final polynomials are ugly in the sense that there are many unnecessary cubic relations.
//However it is very fast and uses the last version of GL2 magma intrinsics. This will be updated soon. 

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


//Fix this 
intrinsic FindModel(G::GrpMat, T::GrpMat, FAM::SeqEnum: redcub:=true, test_hyperelliptic:=true,already_conjugated:=false,onefamily:=false, use_agg_label:=false, use_family_label:=false, agreeable_label:="", family_label:="", use_parent_can:=false, parentcan:=[]) -> SeqEnum[RngMPolElt], AlgMatElt, SeqEnum, BoolElt, RngIntElt,Any
{
    Input:
    - G is a subgroup of GL2(Zhat). It is given by a subgroup of GL2(Z/NZ) where N is a multiple of the level of G.
    - T is the intersection of G with SL2(Z/NZ)

    Keywords:
    - redcub, whether to reduce the cubics (passed on to TwistCurve)
    - test_hyperelliptic, test if X_G is hyperelliptic over Q

    Output:
    - psi: homogeneous polynomials in Q[x_1,..x_n] defining the curve X_G mentioned above.
      n depends on the model of the family representative used to twist G from.
    - MAT: H90 matrix describing the twist from the family representative to G.
    - a sequence of length 2 giving the numerator and denominator of the absolute j-map
    - a boolean, whether X_G is hyperelliptic over Q (only returned if test_hyperelliptic is true)
    - the genus of X_G
}

    //We first start with finding the family in our database that contains G.
    print("Finding the family...");
    //famkey,famG,Gcong,calGlift,Tcong:=FamilyFinderWithCusps(G,T,FAM);
    if already_conjugated and onefamily then
        Gcong:=G; Tcong:=T; famG:=FAM[1]; 
    elif use_agg_label then 
        famkey,famG,Gcong,calGlift,Tcong:=FamilyFinderCanon(G,T,FAM,parentcan:agreeable_label:=agreeable_label, use_agg_label:=use_agg_label);
    elif use_family_label then
        famkey,famG,Gcong,calGlift,Tcong:=FamilyFinderCanon(G,T,FAM,parentcan:family_label:=family_label, use_family_label:=use_family_label);
    elif use_parent_can then 
        famkey,famG,Gcong,calGlift,Tcong:=FamilyFinderCanon(G,T,FAM,parentcan);
    else
        famkey,famG,Gcong,calGlift,Tcong:=FamilyFinderWithCusps(G,T,FAM);
    end if;
    printf "The family key in the database is %o\n",famkey;
    AOfMF:=AssociativeArray();
    for i in Keys(famG`AOfMF) do
        AOfMF[i]:=Transpose(famG`AOfMF[i]);
    end for;
    Tcong`SL:=true;
    if famG`extra1 then
        printf "Computing the cocycle\n";
        xi,K:=GroupToCocycleProj(famG`calG,famG`H,Gcong,Tcong,AOfMF);
        xinew:=map<Domain(xi)->GL(3,K)| [<t,mat3map(xi(t))>: t in Domain(xi)]>;
        Pol<[x]>:=PolynomialRing(Rationals(),3);
        PP:=ProjectiveSpace(Rationals(),2);
        pis:=[Pol!(x[2]^2-x[1]*x[3])];
        printf "Twisting the curve...\n";
        psi,MAT:=TwistCurveGenus0(pis,xinew,K: redcub:=redcub);
                printf "Computing the jmap...\n";
        if assigned famG`RelativeJMap then
			rel:=true;
            L:=famG`RelativeJMap;
        else 
			rel:=false;
            L:=famG`jmap;
        end if;
        newL:=[];
        for ji in L do
            newL:= newL cat [Evaluate(ji,[x[2],x[3]])];
        end for;
        relmap:= PolynomialTwister(newL, MAT, K);
    else
        printf "Computing the cocycle\n";
        xi,K:=GroupToCocycleProj(famG`calG,famG`H,Gcong,Tcong,AOfMF);//This will be the main one from now on. much much faster!
        //Now the twist
        printf "Twisting the curve...\n";
        psi,MAT:=TwistCurve(famG`M`psi,xi,K: redcub:=redcub);
        //Now we compute the jmap. Need to do Galois descent to have rational coefficents. So a little messy
        printf "Computing the jmap...\n";
        //Computing the jmap. The jmap of the representative is precomputed.
        if assigned famG`RelativeJMap then
			rel:=true;
            L:=famG`RelativeJMap;
        else 
			rel:=false;
            L:=famG`jmap;
        end if;
        relmap:= PolynomialTwister(L, MAT, K);
    end if;
    //Computing the cocycle related to H and G. See the paper for details. (Paper is not out yet so look at the file)



   
    if not test_hyperelliptic then
        return psi,MAT,relmap,rel,/*famG`JmapcalG,*/    _,famG`genus,K,famG,Gcong,famG`M,_;
    end if;
   



    printf "Computing QQ-gonality...\n";
    //Following computes if the curve is hyperelliptic
    if famG`M`CPname in gonality_equals_2 then
        assert assigned famG`CanModelForHyp;
        gonmodel:=famG`CanModelForHyp;
        gonAOfMF:=AssociativeArray();
        for i in Keys(famG`AOfMFCanModel) do
            gonAOfMF[i]:=Transpose(famG`AOfMFCanModel[i]);
        end for;
        xi,K:=GroupToCocycleProj(famG`calG,famG`H,Gcong,Tcong,gonAOfMF);
        gonpsi,gonMAT:=TwistCurve(gonmodel`psi,xi,K);
        Pol<x>:=Parent(gonpsi[1]);
        PP:=ProjectiveSpace(Rationals(),#VariableWeights(Pol)-1);
        C:=Curve(PP,gonpsi);
        C,mapo:=Conic(C);
        T:=HasRationalPoint(C);
        return psi,MAT,relmap,rel,/*famG`JmapcalG,*/ T,famG`genus,K,famG,Gcong,famG`M,gonMAT;
    end if;



    return psi,MAT,relmap,rel,/*famG`JmapcalG,*/"not_hyperelliptic",famG`genus,K,famG,Gcong,famG`M,_;
end intrinsic;




intrinsic ComputePlaneModel(G::GrpMat, MAT,MFAM::Rec,psi::SeqEnum: giveup_time:=720)->Any
{}
    assert MFAM`genus gt 3 and not MFAM`CPname in gonality_equals_2;
        MFAM`H`SL:=true;
        cyclevel:=LCM([MFAM`N,#BaseRing(G)]);
        cyctop<o>:=CyclotomicField(cyclevel);
        cycG:=CyclotomicField(#BaseRing(G));
        M:=CreateModularCurveRec(G);
        MFF:=F0Twister(MFAM`F0, MAT^(-1),cyclevel);//Need galois descent coef by coef?
        if psi eq [] then s:=1; else s:=Rank(Parent(psi[1]))-1; end if;
        PP:=ProjectiveSpace(Rationals(),s);
        CG:=Curve(PP,psi);
        L:=PlaneModelsFromQExpansionsForm(M, CG, MFF:giveup_time:=giveup_time);
        return L;
end intrinsic;











function get_uvars(rank)
    uvars := Eltseq("XYZWTUVRSABCDEFGHIKLMNOPQJ");
    if (#uvars lt rank) then
        uvars := [Sprintf("X%o", i) : i in [1..rank]];
    end if;
    return uvars[1..rank];
end function;

function get_lvars(rank)
    lvars := Eltseq("xyzwtuvrsabcdefghiklmnopqj");
    if (#lvars lt rank) then
        lvars := [Sprintf("x%o", i) : i in [1..rank]];
    end if;
    return lvars[1..rank];
end function;







function fieldfind(G, K)
  N := Characteristic(BaseRing(G));
  z := K.1;
  nprim := N;
  if (N mod 4 eq 2) then
    z := z^2;
    nprim := (N div 2);
  end if;
  if (N mod 4 eq 0) then
    nprim := (N div 2);
  end if;
  prim := &+[ z^(k*(Integers()!g[1][1])) : k in Divisors(nprim), g in G];
  es := Eltseq(prim);
  es2 := [ Integers()!es[i] : i in [1..#es]];
  g := GCD(es2);
  if (g ne 0) then
    prim := prim/g;
  end if;
  minpoly := MinimalPolynomial(prim);
  assert Degree(minpoly) eq (EulerPhi(N)/#G);
  return NumberField(minpoly), prim;
end function;


intrinsic AssignCanonicalNames(~R::Rng : upper:=false)
{Assign names in a standard order; R should be either a multivariate polynomial ring or a function field}
    if Type(R) eq FldFun then
        rank := 1;
    else
        rank := Rank(R);
    end if;
    if upper then
        AssignNames(~R, get_uvars(rank));
    else
        AssignNames(~R, get_lvars(rank));
    end if;
end intrinsic;








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





























































//Okay!
function toConic(X)
	// Testing function to convert a rational normal curve to a conic.
	// It is far too slow to run in projective spaces of dimension > 6.
	// Input: A rational normal curve.
	// Output: An isomorphic plane conic.

	assert IsCurve(X);
	D := CanonicalDivisor(X);
	phi := DivisorMap(-D);
	con := Conic(Image(phi));
	return con;
end function;

function PadList(L, n)
	return L cat [0 : i in [#L+1..n]];
end function;

function AbsEltseqPad(elt , prec)
	if Type(AbsolutePrecision(elt)) eq Infty then
		_<t> := Parent(elt);
		print elt;
		elt +:= O(t^prec);
		assert Type(AbsolutePrecision(elt)) ne Infty;
	end if;
	coeffs := AbsEltseq(elt);
	if #coeffs gt prec then
		return coeffs[1..prec];
	else
		return coeffs cat [0 : _ in [#coeffs + 1 .. prec]];
	end if;
end function;


function MatrixAbsEltseq(list)
	prec := Min([AbsolutePrecision(elt) : elt in list]);
	return Matrix([AbsEltseqPad(f, prec) : f in list]);
end function;

function tCheck(BT, t)
	// this checks the Poonen property
	i := #BT;
	b := BT[i];
	while i gt 1 do
		i -:= 1;
		b /:= t;
		assert IsWeaklyZero(BT[i] - b);
	end while;
	return true;
end function;

function Poonenate(BT, t)
	// Create a Poonen basis
	K := BaseRing(Parent(t));
	newBT := BT;
	i := #BT;
	b := BT[i];
	M := IdentityMatrix(K, i);
	while i gt 1 do
		i -:= 1;
		b /:= t;
		N := MatrixAbsEltseq(Append(BT, b));
		K := Kernel(N);
		assert Dimension(K) eq 1;
		v := Basis(K)[1];
		for j in [1..#BT] do
			M[i][j] := v[j];
		end for;
		newBT[i] := b;
	end while;
	assert tCheck(newBT, t);
	return newBT, M;
end function;


function FindPolynomial(Mons, qExps)
	// Given a list of monomials M in #qExps variables, find the unique linear combination that vanishes.
	_<qN> := Parent(qExps[1]);
	Vals := [Evaluate(f, qExps) : f in Mons];
	d := Min([AbsolutePrecision(f) : f in Vals]);
	v := Min([Degree(LeadingTerm(f)) : f in Vals] cat [0]);
	M := Matrix([PadList(AbsEltseq(qN^(-v)*f + O(qN^(d-v))), d-v)[[1..d-v]] : f in Vals]);
	K := Kernel(M);
	assert Dimension(K) eq 1;
	B := Basis(K)[1];
	R := BaseRing(Parent(Mons[1]));
	return &+[(R!B[i])*Mons[i] : i in [1..#Mons]];
end function;

//WHAT IS THE INPUT??? MODUALR FORM???
//intrinsic HyperellipticModel(SeqEnum[RngSerPowElt]) -> Crv 
function HyperellipticModel(B)
	prec := Min([AbsolutePrecision(elt) : elt in B ]);
	g := #B;
	_<qN> := Parent(B[1]);
	K := BaseRing(Parent(B[1]));

	// Compute a triangular basis and check that it satisfies the Poonen property.
	_, T := EchelonForm(MatrixAbsEltseq(B));
	BT := [&+[T[j][i]*B[i] : i in [1..g]] : j in [1..g]];
	t := BT[g] / BT[g-1];
	BT, T2 := Poonenate(BT, t);
	T := T2*T;
	T_inv := T^(-1);

	// Construct the pull back of the canonical divisor on the conic to the P1 over K.
	P1 := Curve(ProjectiveSpace(K, 1));
	FF<t1> := FunctionField(P1);
	f0 := &+[T_inv[1][i]*t1^(i-1) : i in [1..g]];
	f1 := &+[T_inv[2][i]*t1^(i-1) : i in [1..g]];
	f := f0 / f1;
	CanDiv := Divisor(Differential(f));
	RR := Basis(-CanDiv);
	//den := FF!&*[Denominator(elt) : elt in RR];
	//RR := [den*elt : elt in RR];
	PreImagR := PreimageRing(Parent(Numerator(RR[1])));
	RK<y> := PolynomialRing(K);
	nu := hom< PreImagR -> RK | [y] >;

	function ApplyGalois(f, rho)
		f := nu(f);
		return RK![rho(c) : c in Coefficients(f)];
	end function;

	// Compute a rational basis for the Riemann-Roch space
	Coeffs := [ [K.1^a, 0, 0] : a in [0..Degree(K)-1]] cat [ [0, K.1^a, 0] : a in [0..Degree(K)-1]] cat [ [0, 0, K.1^a] : a in [0..Degree(K)-1]];
	A := [ Parent(1/qN) | 0 : i in [1..#Coeffs]];
	for foobar->rho in Automorphisms(K) do
		g0 := &+[rho(T[g-1][i])*B[i] : i in [1..g]];
		g1 := &+[rho(T[g][i])*B[i] : i in [1..g]];
		rhot := g1 / g0;
		//print foobar, [Evaluate(ApplyGalois(Numerator(rj), rho), rhot) / Evaluate(ApplyGalois(Denominator(rj), rho), rhot) : j->rj in RR];
		for i in [1..#Coeffs] do
			A[i] +:= &+[ rho(Coeffs[i][j]) * Evaluate(ApplyGalois(Numerator(rj), rho), rhot) / Evaluate(ApplyGalois(Denominator(rj), rho), rhot) : j->rj in RR ];
		end for;
	end for;
	//print [Degree(LeadingTerm(elt)) : elt in A | not IsWeaklyZero(elt)];
	order := Min([0] cat [Degree(LeadingTerm(elt)) : elt in A | not IsWeaklyZero(elt)]);
	Aorig := A;
	A := [Parent(B[1]) ! Parent(B[1])!(qN^-order * elt) : elt in Aorig];
	MA := MatrixAbsEltseq(A);
	//print [PivotColumn(E, j) : j->_ in Rows(E)] where E :=EchelonForm(MA);
	assert Rank(MA) eq 3;
	A := [A[PivotColumn(otherT, i)] : i in [1..3]] where otherT := EchelonForm(Transpose(MA)); // extracting pivot rows
	assert Rank(MatrixAbsEltseq(A)) eq 3;


	// Use linear algebra to find the conic defined by these traces.
	P2 := ProjectivePlane(Rationals());
	R3<a,b,c> := CoordinateRing(P2);
	M3 := MonomialsOfDegree(R3, 2);
	q := FindPolynomial(M3, A);

	// Simplify the conic and keep track of the q-expansions used to define this conic.
	C := Curve(P2, q);
	_, D := IsConic(C);
	MC, phi_min := MinimalModel(D);
	eq_phi_min := DefiningEquations(Inverse(phi_min));
	foo := [0,0]; // hacky way to pad the output of coefficients
	Amin := [ A[1]*K!(Coefficients(E, a) cat foo)[2] + A[2]*K!(Coefficients(E, b) cat foo)[2] + A[3]*K!(Coefficients(E, c) cat foo)[2] : E in eq_phi_min ];
	assert IsWeaklyZero(Evaluate(Equation(MC), Amin));
	//print "Conic over Q:", Equation(MC);

	// Find rational function expressing b/a in terms of t
	R3<x3, y3, z3> := PolynomialRing(K, 3);
	R2<xK, yK> := PolynomialRing(K, 2);
	Rf<zK> := PolynomialRing(K);
	Pols := [1, yK, yK^2, xK, xK*yK, xK*yK^2];
	Pol_bt := FindPolynomial(Pols, [Amin[2]/Amin[1], t]);
	Pol_ct := FindPolynomial(Pols, [Amin[3]/Amin[1], t]);
	aa_t := LCM(Evaluate(Coefficients(Pol_bt, xK)[2], [0, zK]), Evaluate(Coefficients(Pol_ct, xK)[2], [0, zK]));
	ba_t := - aa_t*Evaluate(Coefficients(Pol_bt, xK)[1], [0, zK]) / Evaluate(Coefficients(Pol_bt, xK)[2], [0, zK]);
	ca_t := - aa_t*Evaluate(Coefficients(Pol_ct, xK)[1], [0, zK]) / Evaluate(Coefficients(Pol_ct, xK)[2], [0, zK]);
	// Constructing a polynomial h vanishing on the zeros of g.
	// FIXME: we are assuming that the conic has a c^2 term
	assert #Coefficients(DefiningEquation(MC), 3) eq 3;

	// If MC has rational point, find a new_t to be a P1 parameter for that curve.
	if HasRationalPoint(MC) then
		Pt := RationalPoint(MC);
		if (Pt[3]*ba_t - Pt[2]*ca_t ne 0) and (Pt[3]*aa_t - Pt[1]*ca_t ne 0) then
			pt := (Pt[3]*aa_t - Pt[1]*ca_t) / (Pt[3]*ba_t - Pt[2]*ca_t);
		elif (Pt[2]*aa_t - Pt[1]*ba_t ne 0) and (Pt[2]*ca_t - Pt[3]*ba_t ne 0) then
			pt := (Pt[2]*ca_t - Pt[3]*ba_t) / (Pt[2]*aa_t - Pt[1]*ba_t);
		elif (Pt[1]*ca_t - Pt[3]*aa_t ne 0) and (Pt[1]*ba_t - Pt[2]*aa_t ne 0) then
			pt := (Pt[1]*ba_t - Pt[2]*aa_t) / (Pt[1]*ca_t - Pt[3]*aa_t);
		else
			assert(false);
		end if;
		assert(Degree(Denominator(pt)) le 1);
		assert(Degree(Numerator(pt)) le 1);
		d,c := Explode(Eltseq(Denominator(pt)) cat [0]);
		b,a := Explode(Eltseq(Numerator(pt)) cat [0]);
		pt_inv := (d*zK - b) / (-c*zK + a);
		print "Warning: conic has rational point, implementation not verified!";
	end if;

	// Compute a hyperelliptic equation for the curve over P1 over K.
	dt := Derivative(t);
	v := qN * dt / BT[1];
	Pols := [yK^2] cat [xK^i : i in [0..2*g+2]];
	H_eq := FindPolynomial(Pols, [t, v]);
	H_eq /:=Coefficients(H_eq, yK)[1+2];
	assert Coefficients(H_eq, yK)[1+2] eq 1;
	f := -Evaluate(H_eq, [xK, 0]);
	if HasRationalPoint(D) then
		f2 := Evaluate(f, [pt_inv, 0]);
		if Denominator(f2) eq 1 then
			f2 := Numerator(f2);
		else
			factf2 := Factorisation(Denominator(f2));
			assert(#factf2 eq 1 and Degree(factf2[1][1]) eq 1);
			f2 := Numerator(f2) * factf2[1][1]^(factf2[1][2] mod 2);
		end if;
		f2 /:= LeadingCoefficient(f2);
		// Find the right constant c to scale h with
		q_t := Evaluate(pt, t);
		dq_t := Derivative(q_t);
		q_f2 := Evaluate(f2, q_t);
		elt := LeadingCoefficient(q_f2);
		// First scale f2 such that the leading q-expansion coefficient is 1, so we can take square roots.
		f2prime := f2/elt;
		q_f2prime := q_f2/elt;
		sqrt_q_f2prime := Sqrt(q_f2prime);
		M3_elts := [a : a in B] cat [qN*dq_t*1/sqrt_q_f2prime];
		M3_minprec := Min([AbsolutePrecision(x) : x in M3_elts]);
		M3 := Matrix([PadList(AbsEltseq(x), M3_minprec)[[1..M3_minprec]] : x in M3_elts]);
		kernel_basis := Basis(Kernel(M3));
		//print #kernel_basis;
		assert #kernel_basis eq 1;
		v := kernel_basis[1];
		assert v[g + 1] ne 0;
		// After having found a K-multiple that lies in the regular rational differentials, scale h back to correct.
		f2_correct := f2prime / v[g + 1]^2;
		assert(not(false in {c in Rationals() : c in Coefficients(f2_correct)}));
		f2_correct := ChangeRing(f2_correct, Rationals());
		//print "f2-polynomial:", f2_correct;
		
		// Construct the curve
		P2<y0, y1, z0> := WeightedProjectiveSpace(Rationals(), [1,1,g+1]);
		doubleCover := Homogenization(Evaluate(f2_correct, y1), y0, 2*g+2) - z0^2;
		doubleCover *:= LCM([Denominator(elt) : elt in Coefficients(doubleCover)]);
		XQQ := Curve(P2, [doubleCover]);
		return XQQ;
	else
	
		//print "Hyperelliptic polynomial over K:", f;

		// Find a hyperelliptic relation for the geometric curve over the conic.
		Qf := quo< Rf | Evaluate(f, [zK, 0]) >;
		Mons2 := [x3^i*y3^j*z3^(g+1-i-j) : i in [0..g+1], j in [0..1] | i+j le g + 1];
		//print ba_t, ca_t;
		if Degree(f) eq 2*g + 2 then
			Matrix2 := Matrix([ PadList(Eltseq(Evaluate(m, [Qf!aa_t, Qf!ba_t, Qf!ca_t])), 2*g+2) : m in Mons2]);
		else
			assert Degree(f) eq 2*g + 1;
			aa_LC := Coefficient(aa_t, 2);
			ba_LC := Coefficient(Numerator(ba_t), 2);
			ca_LC := Coefficient(Numerator(ca_t), 2);
			//Matrix2 := Matrix([ PadList(Eltseq(Evaluate(m, [Qf!aa_t, Qf!ba_t, Qf!ca_t])), 2*g + 2) cat [Evaluate(m, [ba_LC*ca_LC, aa_LC*ca_LC, aa_LC*ba_LC])] : m in Mons2]);
			Matrix2 := Matrix([ PadList(Eltseq(Evaluate(m, [Qf!aa_t, Qf!ba_t, Qf!ca_t])), 2*g + 2) cat [Evaluate(m, [aa_LC, ba_LC, ca_LC])] : m in Mons2]);
		end if;
		K2 := Kernel(Matrix2);
		assert(Dimension(K2) eq 1);
		B2 := Basis(K2)[1];
		h := &+[ B2[i]*Mons2[i] : i in [1..#Mons2]];
		h := Evaluate(h, [1, xK, yK]);
		assert {c in Rationals() : c in Coefficients(h)} eq {true};

		// Find the right constant c to scale h with
		q_b_over_a := Amin[2] / Amin[1];
		dq_b_over_a := Derivative(q_b_over_a);
		q_h := Evaluate(h, [Amin[2]/Amin[1], Amin[3]/Amin[1]]);
		elt := LeadingCoefficient(q_h);
		// First scale h such that the leading q-expansion coefficient is 1, so we can take square roots.
		hprime := h/elt;
		q_hprime := q_h/elt;
		sqrt_q_hprime := Sqrt(q_hprime);
		M3_elts := [a : a in B] cat [qN*dq_b_over_a*1/sqrt_q_hprime];
		M3_minprec := Min([AbsolutePrecision(x) : x in M3_elts]);
		M3 := Matrix([PadList(AbsEltseq(x), M3_minprec)[[1..M3_minprec]] : x in M3_elts]);
		kernel_basis := Basis(Kernel(M3));
		//print #kernel_basis;
		assert #kernel_basis eq 1;
		v := kernel_basis[1];
		assert v[g + 1] ne 0;
		// After having found a K-multiple that lies in the regular rational differentials, scale h back to correct.
		h_correct := hprime / v[g + 1]^2;
		//print "h-polynomial:", h_correct;
		
		// Construct the curve
		P3<y0, y1, y2, z0> := WeightedProjectiveSpace(Rationals(), [2,2,2,g+1]);
		conicEq := Evaluate(DefiningEquation(MC), [y0, y1, y2]);
		conicEq *:= LCM([Denominator(elt) : elt in Coefficients(conicEq)]);
		doubleCover := Homogenization(Evaluate(h_correct, [y1, y2]), y0, g+1) - z0^2;
		doubleCover *:= LCM([Denominator(elt) : elt in Coefficients(doubleCover)]);
		XQQ := Curve(P3, [conicEq, doubleCover]);
		return XQQ;
	end if;	
end function;

function SimplifyGeometricHyperellipticCurve(foo)
	//_<X, Y, Z, W> := Parent(DefiningEquations(foo)[2]);
	a := [1..#Coefficients(DefiningEquations(foo)[2]) - 1];
	N := GCD([Numerator(c) : c in Coefficients(DefiningEquations(foo)[2])[a]]);
	D := LCM([Denominator(c) : c in Coefficients(DefiningEquations(foo)[2])[a]]);
	_, sqrtN := SquarefreeFactorisation(N);
	sqfrD, sqrtD := SquareFreeFactorisation(D);
	P3<X, Y, Z, W> := WeightedProjectiveSpace(Rationals(), [2, 2, 2, Degree(DefiningEquations(foo)[2])]);
	eq1 := Evaluate(DefiningEquations(foo)[1], [X, Y, Z, W]);
	eq2 := sqrtD^2*sqfrD^2/sqrtN^2*Evaluate(DefiningEquations(foo)[2], [X, Y, Z, W*sqrtN/sqrtD/sqfrD]);
	bar := Curve(P3, [eq1, eq2]);
	return bar;
end function;



//changing this
//Input is the canonical model of the hyperelliptuc curve?
//gonMAT, whic is the MAT for canonical model of hyperelliptic curve
function HyperellipticModelFromLabel(G,canM,gonMAT : i:=1, prec0:=0)
	cyclevel:=LCM([canM`N,#BaseRing(G)]);
        //cyctop<o>:=CyclotomicField(cyclevel);
        cycG:=CyclotomicField(#BaseRing(G));
        M:=CreateModularCurveRec(G);
        fs:=F0Twister(canM`F0, gonMAT^(-1),cyclevel);
		bool:=false;
	if not bool then
		B := [elt[i] : elt in fs];
		C := HyperellipticModel(B);
	else
		return false;
	end if;
	if Dimension(Ambient(C)) eq 3 then
		C := SimplifyGeometricHyperellipticCurve(C);
	end if;
	isH, H := IsHyperelliptic(C);
	if isH then
		H := ReducedMinimalWeierstrassModel(H);
		P2<X,Y,Z> := CoordinateRing(Ambient(H));
		return H;
	end if;
	return C;
end function;
