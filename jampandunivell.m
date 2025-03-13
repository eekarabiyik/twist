//Needs Zywinas Code.
//AttachSpec("../modcurves.spec");
 intrinsic MissingMonomials(I, maxd) -> SeqEnum
{Finds the monomials of degree 2..maxd that are not contained in the monomial ideal I.
 Returns a sequence M so that the missing monomials of degree d can be accessed by M[d].  Note that M[1] = [], regardless of I.}
    R := I^0;
    Md := [mon : mon in MonomialsOfDegree(R, 2) | not (mon in I)];
    M := [[], Md];
    r := Rank(R);
    for d in [3..maxd] do
        nmon := Binomial(r+d-1, d);
        if nmon gt r * #M[#M] then
            Md := {mon * R.i : mon in M[#M], i in [1..r]};
        else
            Md := MonomialsOfDegree(R, d);
        end if;
        Append(~M, [mon : mon in Md | not mon in I]);
    end for;
    return M;
end intrinsic;

function nicefy(M)
  M0, T := EchelonForm(M);
  // Rows of T give current basis.
  ee := Eltseq(M0);
  denom := LCM([ Denominator(ee[i]) : i in [1..#ee]]);
  vprint User1: Sprintf("Nicefying %ox%o matrix.",NumberOfRows(M),NumberOfColumns(M));
  M2 := Matrix(Integers(),NumberOfRows(M),NumberOfColumns(M),[ denom*ee[i] : i in [1..#ee]]);
  vprint User1: "Computing saturation.";
  //SetVerbose("Saturation",2);
  AA := Saturation(M2);
  vprint User1: "Done.";
  chk, mult := IsConsistent(ChangeRing(M2,Rationals()),ChangeRing(AA,Rationals()));
  curbat := denom*mult*T;
  vprint User1: "Calling LLL.";
  newlatbasismat, change := LLL(AA : Proof := false);
  vprint User1: "Done.";
  finalbat := ChangeRing(change,Rationals())*curbat;
  return finalbat;
end function;

// This function takes a subgroup of GL(1,Integers(N)) and an instance of Q(zeta_N)
// and returns a simple representation of the corresponding subfield of
// Q(zeta_N), as well as a primitive element for the extension.

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





intrinsic AbsoluteJmap(M::Rec) -> Crv, SeqEnum[RngMPolElt], RngIntElt, SeqEnum, Rec, RngIntElt, RngIntElt
{
    This is an adjusted version of LMFDB's AbsoluteJmap. It works for Zywina's new code.
    To do: Elliptic curve case, i.e. when the modular curve X_G has genus 1.
    To do: Relative jmaps. Case by case. Remember that the relative jmaps between to canonical models are easy to deal with.
    To do: How I handle precision.
}
  

    M`H`SL:=true;
    N := M`N;
    lcmneeded:=LCM([Integers()!(M`sl2level/M`widths[c]): c in [1..#M`cusps]]);
    potentialprec:=Ceiling(Maximum([(M`prec[i]*M`sl2level)/M`widths[i]: i in [1..#M`cusps]]));
    newishprec:= potentialprec;
    if not IsDivisibleBy(potentialprec,lcmneeded) then
        remainder:= potentialprec mod lcmneeded;
        newishprec:= potentialprec + lcmneeded - remainder;
    end if;
    prec:=newishprec;
      if potentialprec lt prec then
        M := IncreaseModularFormPrecision(M,prec);
      end if;
    SetSeed(0);

    maxd := 0;
    mind := 0;
    maxprec := 0;
    // Compute the degree of the line bundle used
    if (M`mult ne [ 1 : i in [1..M`vinf]]) or (M`k ne 2) then
        model_type := 8; // geometrically hyperelliptic
        k := M`k;
        degL:= ((k*(2*M`genus-2)) div 2 + Floor(k/4)*M`v2 + Floor(k/3)*M`v3 + (k div 2)*#M`cusps) - (&+M`mult);
        old_degL := 0;
        while (old_degL ne degL) do
	    old_degL := degL;
	    maxd := Floor((M`index + M`genus - 1)/degL) + 1;
	    mind := maxd - 1;
	
	    maxprec := Floor(N*(M`k*maxd/12 + 1)) + 1;
	    if (maxprec gt prec) then
	             if not IsDivisibleBy(maxprec,lcmneeded) then
                    remainder:= maxprec mod lcmneeded;
                    maxprec:= maxprec + lcmneeded - remainder;
                end if;
                SetSeed(0);
	        M := IncreaseModularFormPrecision(M,maxprec);
	   
	        k := M`k;
	        degL:= ((k*(2*M`genus-2)) div 2 + Floor(k/4)*M`v2 + Floor(k/3)*M`v3 + (k div 2)*#M`cusps) - (&+M`mult);
	    end if;
        end while;
    else

        model_type := 0; // canonical model
        maxd := Floor((M`index)/(2*M`genus-2) + 3/2);
        if ((maxd-1) ge (M`index)/(2*M`genus-2)) and ((maxd-1) le ((M`index)/(2*M`genus-2) + 1/2)) then
	    mind := maxd-1;
	     else
	    mind := maxd;
	
        end if;
        maxprec := Floor(N*(1 + maxd/6)+1);
        if (maxprec gt prec) then
	        if not IsDivisibleBy(maxprec,lcmneeded) then
                    remainder:= maxprec mod lcmneeded;
                    maxprec:= maxprec + lcmneeded - remainder;
            end if;
            SetSeed(0);
	     M := IncreaseModularFormPrecision(M,maxprec);
	  
        end if;
    end if;

  C := Curve(ProjectiveSpace(Rationals(), #M`F0 - 1), M`psi);
  GL2 := GL2Ambient(M`N);
  SL2 := SL2Ambient(M`N);
  N:=M`N;
  G:=M`G;
  U,pi:=UnitGroup(Integers(M`N));

  chosencusps:=[M`cusp_orbits[j][1]: j in [1..#M`cusp_orbits]];
  chosenmult := [ M`mult[c] : c in chosencusps];

  modforms0 := [ [ M`F0[i][c] : c in chosencusps] : i in [1..#M`F0]];
  /*
  modforms00:=[];
  for j in [1..#M`F0] do
    K:=Parent(Coefficient(modforms0[1][1],0));
    PP<qN>:=LaurentSeriesRing(K);
    cc:=[];
    for c in chosencusps do
    t:=Evaluate(M`F0[j][c],qN^(M`N/M`widths[c]));
    cc:=cc cat [t];
    end for;
    modforms00:=modforms00 cat [cc];
  end for;
  modforms0:=modforms00;
*/
  // Step 2 - Rewrite modular coefficients as elements of smaller subfield
  //ERAY: We are actually not doing that. For high levels it hurts more. Will make this nicer.

  vprint User1: "Rewriting Fourier expansions over smaller fields.";
  GL2Galois := sub<GL2 | [[1,0,0,pi(u)] : u in Generators(U)]>;
  z := Parent(Coefficient(modforms0[1][1],0)).1;
  R<x> := PolynomialRing(Rationals());
  fourierlist := <>;
  totalprec := 0;
  for c in [1..#chosencusps] do
      galoiscusp0 := GL2Galois meet Conjugate(G,GL2!M`cusps[chosencusps[c]]);
      // The subfield of Q(zeta_N) corresponding to galoiscusp is the field of definition of the Fourier coeffs.
      galoiscusp := Sort([g[2][2] : g in galoiscusp0]);
      KK:=Parent(z);
      prim:=z;
      vprint User1: Sprintf("For cusp %o, Fourier coefficient field is %o.", c, R!DefiningPolynomial(KK));
      PP<qw> := LaurentSeriesRing(KK);
      Embed(KK,Parent(z),prim);
      totalprec := totalprec + M`prec[chosencusps[c]]*Degree(KK);
      curfour := <>;
      for i in [1..#modforms0] do
	  newfourier := &+[ KK!Coefficient(modforms0[i][c],l)*qw^l : l in [0..AbsolutePrecision(modforms0[i][c])-1]] + BigO(qw^AbsolutePrecision(modforms0[i][c]));
	  Append(~curfour,newfourier);
      end for;
      Append(~fourierlist,curfour);
  end for;
  modforms := << fourierlist[j][i] : j in [1..#chosencusps]> : i in [1..#modforms0]>;



  // Build log-canonicalish ring

  polyring<[x]> := PolynomialRing(Rationals(),#modforms,"grevlex");
  vars := [ polyring.i : i in [1..#modforms]];
  gens := [ Evaluate(M`psi[j],vars) : j in [1..#M`psi]];

  I := ideal<polyring | gens>;
  G := GroebnerBasis(I);

  LMs := [ LeadingMonomial(G[i]) : i in [1..#G]];
  initideal := ideal<polyring | LMs>;

  // canring is a list of pairs.
  // The first thing in a pair is list of lists of Fourier expansions
  // of the degree d generators of the canonical ring.
  // The second thing in a pair is list of degree d monomials representing the
  // elements.

  canring := <<modforms,vars>>;

  // Let's choose monomials that will *always* work!


  multcount := 0;
  doneper := -1;
  missing_monomials := MissingMonomials(initideal, maxd);
  total := &+[ #mons : mons in missing_monomials];
  for d in [2..maxd] do
      bas := missing_monomials[d];
      newfourier := <>;
      newvars := [];
      for curmon in bas do
	  // We have to be able to write curmon as a product of a degree (d-1)
	  // monomial not in initideal, and a degree 1 element.
	  // If we couldn't, then curmon would be in initideal
	  ind := Index([ IsDivisibleBy(curmon,canring[d-1][2][k]) : k in [1..#canring[d-1][2]]],true);
	  chk, q := IsDivisibleBy(curmon,canring[d-1][2][ind]);
	  ind2 := Index(vars,q);
	  multcount := multcount + 1;
	  if Floor(100*multcount/total) gt doneper then
	      doneper := Floor(100*multcount/total);
	  end if;
	  newprd := < modforms[ind2][i]*canring[d-1][1][ind][i] : i in [1..#chosencusps]>;
	  Append(~newfourier,newprd);
	  Append(~newvars,curmon);
      end for;
      Append(~canring,<newfourier,newvars>);
  end for;


  jin:=[];
  for c in chosencusps do
  w:=M`widths[c];
  FFFF<qw> := LaurentSeriesRing(Rationals());
  j := (1728*Eisenstein(4,qw : Precision := Ceiling((M`prec[c]+2*w)/w))^3)/(Eisenstein(4,qw : Precision := Ceiling((M`prec[c]+2*w)/w))^3 - Eisenstein(6,qw : Precision := Ceiling((M`prec[c]+2*w)/w))^2);
  j := Evaluate(j,qw^w);
  jin:=jin cat [j];
  end for;

  func := jin;
  done := false;
  

  curd := mind;
  jmat := ZeroMatrix(Rationals(),0,totalprec);
  for i in [1..#canring[curd][1]] do
      vecseq := [];
      for jj in [1..#chosencusps] do
	  pp := (func[jj]*canring[curd][1][i][jj]);
	  vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [-M`widths[chosencusps[jj]]..-M`widths[chosencusps[jj]]+M`prec[chosencusps[jj]]-1]]);
      end for;
      jmat := VerticalJoin(jmat,Matrix(Rationals(),1,totalprec,vecseq));
  end for;

  for i in [1..#canring[curd][1]] do
      vecseq := [];
      for jj in [1..#chosencusps] do
	  pp := -canring[curd][1][i][jj];
	  vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [-M`widths[chosencusps[jj]]..-M`widths[chosencusps[jj]]+M`prec[chosencusps[jj]]-1]]);
      end for;
      jmat := VerticalJoin(jmat,Matrix(Rationals(),1,totalprec,vecseq));
  end for;
  NN := NullSpace(jmat);
  dimdim := Dimension(NN);
  if dimdim ge 1 then
      done := true;
  end if;

  if (done eq false) then
      curd := maxd;
      jmat := ZeroMatrix(Rationals(),0,totalprec);
      for i in [1..#canring[curd][1]] do
	  vecseq := [];
	  for jj in [1..#chosencusps] do
	      pp := (func[jj]*canring[curd][1][i][jj]);
	      vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [-M`widths[chosencusps[jj]]..-M`widths[chosencusps[jj]]+M`prec[chosencusps[jj]]-1]]);
	  end for;
	  jmat := VerticalJoin(jmat,Matrix(Rationals(),1,totalprec,vecseq));
      end for;

      for i in [1..#canring[curd][1]] do
	  vecseq := [];
	  for jj in [1..#chosencusps] do
	      pp := -canring[curd][1][i][jj];
vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [-M`widths[chosencusps[jj]]..-M`widths[chosencusps[jj]]+M`prec[chosencusps[jj]]-1]]);
	  end for;
	  jmat := VerticalJoin(jmat,Matrix(Rationals(),1,totalprec,vecseq));
      end for;
      NN := NullSpace(jmat);
  end if;

  // Now actually write down the map to the j-line

  canringdim := #canring[curd][1];
  nullmat := Matrix(Basis(NN));
  changemat := nicefy(nullmat);
  v := (changemat*nullmat)[1];
  denom := &+[ (polyring!v[i])*canring[curd][2][i] : i in [1..canringdim]];
  num := &+[ (polyring!v[i+canringdim])*canring[curd][2][i] : i in [1..canringdim]];
  weakzero := [ &+[ v[i]*canring[curd][1][i][j] : i in [1..canringdim]]*func[j] - &+[ v[i+canringdim]*canring[curd][1][i][j] : i in [1..canringdim]] : j in [1..#chosencusps]];
  assert &and [ IsWeaklyZero(weakzero[i]) : i in [1..#chosencusps]];

  jmap := map<C -> ProjectiveSpace(Rationals(),1) | [num,denom]>;
  return C, [num, denom], model_type, M`F0, M,mind,maxd,maxprec;
 end intrinsic;







intrinsic ComputeModelwithPrec(M::Rec, calG::GrpMat) -> Rec, RngIntElt, RngIntElt, RngIntElt, RngIntElt, BoolElt
{Compute model and modular forms of M}
    M:=FindModelOfXG(M : G0:=calG);
    M`H`SL:=true;
    N := M`N;
    lcmneeded:=LCM([Integers()!(M`sl2level/M`widths[c]): c in [1..#M`cusps]]);
    potentialprec:=Ceiling(Maximum([(M`prec[i]*M`sl2level)/M`widths[i]: i in [1..#M`cusps]]));
    newishprec:= potentialprec;
    if not IsDivisibleBy(potentialprec,lcmneeded) then
        remainder:= potentialprec mod lcmneeded;
        newishprec:= potentialprec + lcmneeded - remainder;
    end if;
    prec:=newishprec;
      if potentialprec lt prec then
        M := IncreaseModularFormPrecision(M,prec);
      end if;
    SetSeed(0);
    geomhyper:=false;
    maxd := 0;
    mind := 0;
    maxprec := 0;
    degL:=-10;
    // Compute the degree of the line bundle used
    if (M`mult ne [ 1 : i in [1..M`vinf]]) or (M`k ne 2) then
        geomyhper:=true;
        model_type := 8; // geometrically hyperelliptic
        k := M`k;
        degL:= ((k*(2*M`genus-2)) div 2 + Floor(k/4)*M`v2 + Floor(k/3)*M`v3 + (k div 2)*#M`cusps) - (&+M`mult);
        old_degL := 0;
        while (old_degL ne degL) do
	    old_degL := degL;
	    maxd := Floor((M`index + M`genus - 1)/degL) + 1;
	    mind := maxd - 1;
	
	    maxprec := Floor(N*(M`k*maxd/12 + 1)) + 1;
	    if (maxprec gt prec) then
	             if not IsDivisibleBy(maxprec,lcmneeded) then
                    remainder:= maxprec mod lcmneeded;
                    maxprec:= maxprec + lcmneeded - remainder;
                end if;
                SetSeed(0);
	        M := IncreaseModularFormPrecision(M,maxprec);
	   
	        k := M`k;
	        degL:= ((k*(2*M`genus-2)) div 2 + Floor(k/4)*M`v2 + Floor(k/3)*M`v3 + (k div 2)*#M`cusps) - (&+M`mult);
	    end if;
        end while;
    else
        geomhyper:=false;
        model_type := 0; // canonical model
        maxd := Floor((M`index)/(2*M`genus-2) + 3/2);
        if ((maxd-1) ge (M`index)/(2*M`genus-2)) and ((maxd-1) le ((M`index)/(2*M`genus-2) + 1/2)) then
	    mind := maxd-1;
	     else
	    mind := maxd;
	
        end if;
        maxprec := Floor(N*(1 + maxd/6)+1);
        if (maxprec gt prec) then
	        if not IsDivisibleBy(maxprec,lcmneeded) then
                    remainder:= maxprec mod lcmneeded;
                    maxprec:= maxprec + lcmneeded - remainder;
            end if;
            SetSeed(0);
	     M := IncreaseModularFormPrecision(M,maxprec);
	  
        end if;
    end if;
  return M, maxd, mind, maxprec, degL, geomhyper;
end intrinsic;

intrinsic CuspsOrbits(M::Rec) -> SeqEnum[RngIntElt]
{Inputs: N::RngIntElt, cusps 
Computes the action of (Z/NZ)^* on the cusps of X_G.  This corresponds to the action of Gal(Q(zeta_N)/Q) on the cusps.}
  return  [M`cusp_orbits[j][1]: j in [1..#M`cusp_orbits]];
end intrinsic;

intrinsic OldNewConverterF0(M::Rec, modforms0::SeqEnum, chosencusps::SeqEnum[RngIntElt]) -> SeqEnum
{}
  modforms00:=[];
  for j in [1..#M`F0] do
    K:=Parent(Coefficient(modforms0[1][1],0));
    PP<qN>:=LaurentSeriesRing(K);
    cc:=[];
    for c in chosencusps do
    t:=Evaluate(M`F0[j][c],qN^(M`N/M`widths[c]));
    cc:=cc cat [t];
    end for;
    modforms00:=modforms00 cat [cc];
  end for;
    return modforms00;
  end intrinsic;


  intrinsic OldNewConverterF(M::Rec, modforms0::SeqEnum, chosencusps::SeqEnum[RngIntElt]) -> SeqEnum
{}
  modforms00:=[];
  for j in [1..#M`F] do
    K:=Parent(Coefficient(modforms0[1][1],0));
    PP<qN>:=LaurentSeriesRing(K);
    cc:=[];
    for c in chosencusps do
    t:=Evaluate(M`F[j][c],qN^(M`N/M`widths[c]));
    cc:=cc cat [t];
    end for;
    modforms00:=modforms00 cat [cc];
  end for;
    return modforms00;
  end intrinsic;




intrinsic RewriteFourierExpansion(M::Rec, chosencusps::SeqEnum[RngIntElt], maxprec::RngIntElt, modforms0::SeqEnum) -> SeqEnum, RngIntElt, Tup
{Rewriting Fourier expansions over smaller fields}
  //modforms0 := [ [ M`F0[i][c] : c in chosencusps] : i in [1..#M`F0]];
  N := M`N;
  G:=M`G;
  GL2 := GL(2,Integers(N));  
  U,pi:=UnitGroup(Integers(N));
  GL2Galois := sub<GL2 | [[1,0,0,pi(u)] : u in Generators(U)]>;
  z := Parent(Coefficient(modforms0[1][1],0)).1;
  R<x> := PolynomialRing(Rationals());
  fourierlist := <>;
  totalprec := 0;
  KKlist := <>;
  for c in [1..#chosencusps] do
      galoiscusp0 := GL2Galois meet Conjugate(G,GL2!M`cusps[chosencusps[c]]);
      // The subfield of Q(zeta_N) corresponding to galoiscusp is the field of definition of the Fourier coeffs.
      galoiscusp := Sort([g[2][2] : g in galoiscusp0]);
      KK:=Parent(z);
      prim:=z;
      vprint User1: Sprintf("For cusp %o, Fourier coefficient field is %o.", c, R!DefiningPolynomial(KK));
      PP<qw> := LaurentSeriesRing(KK);
      Embed(KK,Parent(z),prim);
      Append(~KKlist,<KK,prim>);
      totalprec := totalprec + M`prec[chosencusps[c]]*Degree(KK);
      curfour := <>;
      for i in [1..#modforms0] do
	      newfourier := &+[ KK!Coefficient(modforms0[i][c],l)*qw^l : l in [0..AbsolutePrecision(modforms0[i][c])-1]] + BigO(qw^AbsolutePrecision(modforms0[i][c])); 
        Append(~curfour,newfourier);
      end for;
      Append(~fourierlist,curfour);
  end for;
  modforms := << fourierlist[j][i] : j in [1..#chosencusps]> : i in [1..#modforms0]>;
  return modforms, totalprec, KKlist;
end intrinsic;







intrinsic CanonicalRing(polyring::RngMPol, M::Rec, chosencusps::SeqEnum[RngIntElt], modforms::Tup, maxd::RngIntElt) -> Tup, SeqEnum
{Compute the (log)-canonical ring of M}
  //polyring<[x]> := PolynomialRing(Rationals(),#modforms,"grevlex"); //To give an idea as to what the polyring should be.
  Ffield := FieldOfFractions(polyring);
  vars := [ polyring.i : i in [1..#modforms]];
  gens := [ Evaluate(M`psi[j],vars) : j in [1..#M`psi]];// so there is a model needed for this gut.
  ttemp := Cputime();
  printf "Computing Grobner basis for ideal.\n";
  I := ideal<polyring | gens>;
  G := GroebnerBasis(I);
  gbtime := Cputime(ttemp);
  printf "Grobner basis time was %o.\n",gbtime;
  LMs := [ LeadingMonomial(G[i]) : i in [1..#G]];
  initideal := ideal<polyring | LMs>;

  // canring is a list of pairs.
  // The first thing in a pair is list of lists of Fourier expansions
  // of the degree d generators of the canonical ring.
  // The second thing in a pair is list of degree d monomials representing the
  // elements.

  
  canring := <<modforms,vars>>;

  // Let's choose monomials that will *always* work!


  multcount := 0;
  doneper := -1;
  missing_monomials := MissingMonomials(initideal, maxd);
  total := &+[ #mons : mons in missing_monomials];
  for d in [2..maxd] do
      bas := missing_monomials[d];
      newfourier := <>;
      newvars := [];
      for curmon in bas do
	  // We have to be able to write curmon as a product of a degree (d-1)
	  // monomial not in initideal, and a degree 1 element.
	  // If we couldn't, then curmon would be in initideal
	  ind := Index([ IsDivisibleBy(curmon,canring[d-1][2][k]) : k in [1..#canring[d-1][2]]],true);
	  chk, q := IsDivisibleBy(curmon,canring[d-1][2][ind]);
	  ind2 := Index(vars,q);
	  multcount := multcount + 1;
	  if Floor(100*multcount/total) gt doneper then
	      doneper := Floor(100*multcount/total);
	  end if;
	  newprd := < modforms[ind2][i]*canring[d-1][1][ind][i] : i in [1..#chosencusps]>;
	  Append(~newfourier,newprd);
	  Append(~newvars,curmon);
      end for;
      Append(~canring,<newfourier,newvars>);
  end for;
  return canring, vars;
end intrinsic;

intrinsic jMap(polyring::RngMPol, M::Rec, chosencusps::SeqEnum[RngIntElt], canring::Tup, modforms::Tup, prec::SeqEnum[RngIntElt]) -> RngMPolElt, RngMPolElt, Crv
{Compute the j-map as an element of the function field of M}
  totalprec := prec[1]; maxprec := prec[2]; maxd := prec[3]; mind := prec[4];
  
  jin:=[];
  for c in chosencusps do
  w:=M`widths[c];
  FFFF<qw> := LaurentSeriesRing(Rationals());
  j := (1728*Eisenstein(4,qw : Precision := Ceiling((M`prec[c]+2*w)/w))^3)/(Eisenstein(4,qw : Precision := Ceiling((M`prec[c]+2*w)/w))^3 - Eisenstein(6,qw : Precision := Ceiling((M`prec[c]+2*w)/w))^2);
  j := Evaluate(j,qw^w);
  jin:=jin cat [j];
  end for;

  func := jin;
  done := false;
  

  curd := mind;
  jmat := ZeroMatrix(Rationals(),0,totalprec);
  for i in [1..#canring[curd][1]] do
      vecseq := [];
      for jj in [1..#chosencusps] do
	  pp := (func[jj]*canring[curd][1][i][jj]);
	  vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [-M`widths[chosencusps[jj]]..-M`widths[chosencusps[jj]]+M`prec[chosencusps[jj]]-1]]);
      end for;
      jmat := VerticalJoin(jmat,Matrix(Rationals(),1,totalprec,vecseq));
  end for;

  for i in [1..#canring[curd][1]] do
      vecseq := [];
      for jj in [1..#chosencusps] do
	  pp := -canring[curd][1][i][jj];
	  vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [-M`widths[chosencusps[jj]]..-M`widths[chosencusps[jj]]+M`prec[chosencusps[jj]]-1]]);
      end for;
      jmat := VerticalJoin(jmat,Matrix(Rationals(),1,totalprec,vecseq));
  end for;
  NN := NullSpace(jmat);
  dimdim := Dimension(NN);
  if dimdim ge 1 then
      done := true;
  end if;

  if (done eq false) then
      curd := maxd;
      jmat := ZeroMatrix(Rationals(),0,totalprec);
      for i in [1..#canring[curd][1]] do
	  vecseq := [];
	  for jj in [1..#chosencusps] do
	      pp := (func[jj]*canring[curd][1][i][jj]);
	      vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [-M`widths[chosencusps[jj]]..-M`widths[chosencusps[jj]]+M`prec[chosencusps[jj]]-1]]);
	  end for;
	  jmat := VerticalJoin(jmat,Matrix(Rationals(),1,totalprec,vecseq));
      end for;

      for i in [1..#canring[curd][1]] do
	  vecseq := [];
	  for jj in [1..#chosencusps] do
	      pp := -canring[curd][1][i][jj];
vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [-M`widths[chosencusps[jj]]..-M`widths[chosencusps[jj]]+M`prec[chosencusps[jj]]-1]]);
	  end for;
	  jmat := VerticalJoin(jmat,Matrix(Rationals(),1,totalprec,vecseq));
      end for;
      NN := NullSpace(jmat);
  end if;

  // Now actually write down the map to the j-line

  canringdim := #canring[curd][1];
  nullmat := Matrix(Basis(NN));
  changemat := nicefy(nullmat);
  v := (changemat*nullmat)[1];
  denom := &+[ (polyring!v[i])*canring[curd][2][i] : i in [1..canringdim]];
  num := &+[ (polyring!v[i+canringdim])*canring[curd][2][i] : i in [1..canringdim]];
  weakzero := [ &+[ v[i]*canring[curd][1][i][j] : i in [1..canringdim]]*func[j] - &+[ v[i+canringdim]*canring[curd][1][i][j] : i in [1..canringdim]] : j in [1..#chosencusps]];
  assert &and [ IsWeaklyZero(weakzero[i]) : i in [1..#chosencusps]];

  C := Curve(ProjectiveSpace(Rationals(),#modforms-1),M`psi);
  return num, denom, C;
end intrinsic;


intrinsic RatioFromWeight3Form(M::Rec, M2::Rec, arg::List) ->
 RngMPolElt, RngMPolElt
{Compute f^2/E_6 as an element of the function of M, where f is a weight 3 modular form for the fine curve
M2 is the fine modular curve, M is the coarse one.
arg::[polyring::RngMPol, geomhyper::BoolElt, KKlist::Tup, canring::Tup,
 chosencusps::SeqEnum[RngIntElt], degL::RngIntElt, irregcusps::BooCanonical, totalprec::RngIntElt, maxprec::RngIntElt]}

  polyring := arg[1]; geomhyper := arg[2]; KKlist := arg[3]; canring := arg[4]; chosencusps := arg[5]; degL := arg[6];
  irregcusps := arg[7]; totalprec := arg[8]; maxprec := arg[9];
  N := M`N;
  //print(N);
  N2 := M2`N;
  //print(N2);
  GL2 := GL(2,Integers(N));
  U,pi:=UnitGroup(Integers(N));
  newmaxprec := (maxprec-1)*Ceiling((N2/N))+1;//NEED LCM NEEDED
  if irregcusps then
    newmaxprec := (maxprec-1)*Ceiling((2*N2/N))+1;//NEED LCM NEEDED
  end if;
  //M2 := FindModularForms(3,M2,(maxprec-1)*Ceiling((N2/N))+1);
  M2 := IncreaseModularFormPrecision(FindModularForms(3, M2),newmaxprec);//G0 THING MIGHT BE A PROBLEM here TRY DAVIDS CORRESPONDING PART
  modforms0 := [ [ M2`F[i][c] : c in [1..#M2`cusps]] : i in [1..#M2`F]];
  

    E6list:=[];
    for c in [1..#M2`cusps] do
  w:=M2`widths[c];
  FFFF<qw> := LaurentSeriesRing(Rationals());
  E6 := Eisenstein(6,qw : Precision := Ceiling((M2`prec[c]+2*w)/w));
  E6 := Evaluate(E6,qw^w);
  E6list:=E6list cat [E6];

  end for;

  modforms3 := [ modforms0[1][c]^2 : c in [1..#M2`cusps]]; // weight 6

  f:=ConvertModularFormExpansions(M, M2, [modforms3],[1,0,0,1])[1];
  modforms3_new := [f[t]/E6list[t]: t in [1..#M2`cusps]];
  printf "Rewriting Fourier expansions over smaller fields.\n";
  GL2Galois := sub<GL2 | [[1,0,0,pi(u)] : u in Generators(U)]>;
  z := Parent(Coefficient(modforms3_new[1],0)).1;
  R<x> := PolynomialRing(Rationals());
  fourierlist := <>;
  // Only make a list of the Fourier expansions of (M2`F[1][i]^2/E6)
  totalprec := 0;
  for c in [1..#chosencusps] do
    galoiscusp0 := GL2Galois meet Conjugate(M`G,GL2!M`cusps[chosencusps[c]]);
    // The subfield of Q(zeta_N) corresponding to galoiscusp is the field of definition of the Fourier coeffs.
    galoiscusp := Sort([g[2][2] : g in galoiscusp0]);
    //printf "For cusp %o, Galois group is %o.\n",c,galoiscusp;
    KK := KKlist[c][1];
    //print(KK);
    //print(Parent(z));
    prim := KKlist[c][2];
    //print(prim);
    //print(PrimitiveElement(KK));
    //print(PrimitiveElement(Parent(z)));
    PP<qw> := LaurentSeriesRing(KK);
    if Degree(KK) eq 1 then KK:=Rationals(); prim:=1; end if;
    Embed(KK,Parent(z),prim);
    totalprec := totalprec + M2`prec[chosencusps[c]]*Degree(KK);
    //print(totalprec);
    newfourier := &+[ KK!Coefficient(modforms3_new[chosencusps[c]],l)*qw^l : l in [0..AbsolutePrecision(modforms3_new[chosencusps[c]])-1]] + BigO(qw^AbsolutePrecision(modforms3_new[chosencusps[c]]));
    Append(~fourierlist,newfourier);
  end for;
  modf := fourierlist;

  // Now represent modf as a ratio of elements in the log-canonicalish ring.
  // A modular form of weight k has (k/12)*Index(subgroup) many zeros in H/subgroup.
  // This means that the ratio of two holomorphic modular forms of weight 6
  // is a modular function of degree <= (1/2)*index.
  
  curd := 0;
  if geomhyper then
    curd := Floor(((M`index/2) + M`genus - 1)/degL) + 1;;
  else  
    curd := Floor((M`index)/(4*M`genus-4) + 3/2);
  end if;
  dimdim:=0;
  
  while dimdim lt 1 do
  
  fmat := ZeroMatrix(Rationals(),0,totalprec);
  //print(fmat);
  for i in [1..#canring[curd][1]] do
    vecseq := [];
    for jj in [1..#chosencusps] do
      pp := (modf[jj]*canring[curd][1][i][jj]);
      //print(maxprec);
      //print(AbsolutePrecision(modf[jj]));
      vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [0..M2`prec[chosencusps[jj]]-1]]);
      //print(vecseq);
    end for;
    fmat := VerticalJoin(fmat,Matrix(Rationals(),1,totalprec,vecseq));
  end for;

  for i in [1..#canring[curd][1]] do
    vecseq := [];
    for jj in [1..#chosencusps] do
      pp := -canring[curd][1][i][jj];
      //print(maxprec);
      //print(pp);
      //print(AbsolutePrecision(pp));
      vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [0..M2`prec[chosencusps[jj]]-1]]);
      //print(vecseq);
    end for;
    fmat := VerticalJoin(fmat,Matrix(Rationals(),1,totalprec,vecseq));
  end for;
  NN := NullSpace(fmat);
  dimdim := Dimension(NN);
  printf "For d = %o, dimension of null space is %o.\n",curd,dimdim;
  if not dimdim ge 1 then curd:=curd+1; end if;
  end while;

  canringdim := #canring[curd][1];
  nullmat := Matrix(Basis(NN));
  changemat := nicefy(nullmat);
  v := (changemat*nullmat)[1];
  fdenom := &+[ (polyring!v[i])*canring[curd][2][i] : i in [1..canringdim]];
  fnum := &+[ (polyring!v[i+canringdim])*canring[curd][2][i] : i in [1..canringdim]];
  weakzero := [ &+[ v[i]*canring[curd][1][i][j] : i in [1..canringdim]]*modf[j] - &+[ v[i+canringdim]*canring[curd][1][i][j] : i in [1..canringdim]] : j in [1..#chosencusps]];
  assert &and [ IsWeaklyZero(weakzero[i]) : i in [1..#chosencusps]];
  return fnum, fdenom,M2;
end intrinsic; 





intrinsic Jmap(M::Rec, calG::GrpMat) -> Tup
{}
    M`H`SL:=true;
    M, maxd, mind, maxprec, degL, geomhyper:=ComputeModelwithPrec(M,calG);
    M`H`SL:=true;
    chosencusps:=CuspsOrbits(M);
    GL2 := GL2Ambient(M`N);
    SL2 := SL2Ambient(M`N);
    N:=M`N;
    G:=M`G;
    U,pi:=UnitGroup(Integers(M`N));
    chosenmult := [ M`mult[c] : c in chosencusps];
    modforms := [ [ M`F0[i][c] : c in chosencusps] : i in [1..#M`F0]];
    modforms, totalprec, KKlist:=RewriteFourierExpansion(M, chosencusps, maxprec,modforms);
    polyring<[x]> := PolynomialRing(Rationals(),#modforms,"grevlex");
    canring, vars:=CanonicalRing(polyring, M, chosencusps, modforms, maxd);
    num, denom, C:=jMap(polyring, M, chosencusps, canring, modforms, [totalprec,maxprec,maxd,mind]);
    return <num,denom,C,polyring, geomhyper, KKlist, canring , chosencusps, degL, totalprec , maxprec,M>;
end intrinsic;




//func element given by a seq of expansions at the cusps.
//want to write it as a ratio

intrinsic FindRatio(M,M0, tryingdegs : homogeneous:=true, prec0:=0, prec_delta:=10, Id:=[* *], mon1:=[* *],mon:=[* *],AA:=[* *])-> SeqEnum
    {
        Warning: this function is still very experimental!

        Input: 
                Modular curves M and M0 corresponding to open subgroups G and G0 of 
                GL(2,Zhat), respectively.  Assume that G0:=[\pm I G]

                We assume that model of X_G0 is already computed
        Output: With respect to their model, we give two homomogenous polynomials 
                that corresponds to f^2/E6 where f is a modular form of weight three and E6 is the normal E6.

        Suppose that the parameter "homogenous" is set to false and the model of X_G or X_G0 is not canonical. Then a tuple of 
        the form [1,F_1,...,F_n] is returned with F_i in the function field of X_G. 
        Clearing denominators will give a tuple of homogenous polynomials as above.   The 
        function works by computing these F_i first and this express may me nicer for many purposes.

        The parameters "prec0" and "prec_delta" are for initial precision and how much to increase it when more is needed;
        these should be left alone at first.
        The parameters "Id" and "mon1" should be left alone; they are for keeping computations when we apply the function
        recursively.
    }

    M0:=FindModularForms(3,M0);
    prec:=Minimum([ (M`sl2level div M`widths[i])*M`prec[i] : i in [1..M`vinf]]) ;
    prec:=Maximum(prec,prec0);
    M0:=IncreaseModularFormPrecision(M0,prec);
    assert assigned M`psi and assigned M`model_degree and assigned M`F0;
     E6list:=[];
    for c in [1..#M0`cusps] do
        w:=M0`widths[c];
        FFFF<qw> := LaurentSeriesRing(Rationals());
        E6 := Eisenstein(6,qw : Precision := Ceiling((M0`prec[c]+2*w)/w));
        E6 := Evaluate(E6,qw^w);
        E6list:=E6list cat [E6];
    end for;
        "E6";
        E6list;
        modforms3 := [ M0`F[1][c]^2 : c in [1..#M0`cusps]]; // weight 6

        f:=ConvertModularFormExpansions(M, M0, [modforms3],[1,0,0,1])[1];
        "f is";
        f;
        modforms3_new := [f[t]/E6list[t]: t in [1..#M`cusps]];
        toc:=modforms3_new;
        "toc is";
        toc;

    // We will look for a morphism defined over K_G.   For many of the computations,
    // it will be useful to work modulo a well chosen prime Q.
    //TODO: choice??  ensure no issues
    OO:=RingOfIntegers(M`KG);
    disc:=Integers()!Discriminant(M`KG);
    q:=2;
    repeat
        q:=NextPrime(q);
    until M`N mod q ne 0 and disc mod q ne 0;    
    Q:=Factorization(ideal<OO|[q]>)[1][1];
    FF_Q,iota:=ResidueClassField(Q);

    // We increase the precision
    prec:=Minimum([ (M`sl2level div M`widths[i])*M`prec[i] : i in [1..M`vinf]]) ;
    prec:=Maximum(prec,prec0);
    M:=IncreaseModularFormPrecision(M,prec);

    // Modular forms describing model of M0 converted to M
    printf "prec is %o\n",prec;

    //deg_h:=M0`model_degree * (M`index div M0`index);
    deg_toc:=M`model_degree * tryingdegs;
    // Consider the quotient of two modular forms in the sequence h;
    // then "deg_h" bounds the total number of zeros and poles as a rational function on M

    n:=#M`F0 div M`KG_degree;
    K:=M`KG;
    Pol_K<[y]>:=PolynomialRing(K,n); 

    // ideal of Pol_K given by our model of M
    // I_gen:=[Pol_K!p: p in M`psi];
    // Now work over finite field instead!

    Pol_FF<[x]>:=PolynomialRing(FF_Q,n);
    I_gen:=[Pol_FF!pol :pol in M`psi];
 
  
        //For now, we compute the Hilbert series when we do not have a canonical model.
        //TODO: check running time
        I:=ideal<Pol_FF|I_gen>;
        Rs<t>:=PowerSeriesRing(Rationals());
        HS:=HilbertSeries(Submodule(I));


    /*  
        Idea:
            Let f_1,..,f_r be the basis of modular forms that give rise to the model of M.
            Let h_1,..,h_s be the basis of modular forms that give rise to the model of M0.
            For i=2,..s, we consider h_i/h_1 which gives a rational functions on M.  We will have
                    h_i/h_1 = F_1(f_1,..,f_r)/F_2(f_1,..,f_r)
            where F_1,F_2 are homomogenous polynomials of the same degree d.
            We start with d=0 and increase d until we find such a relation!

            Observations:
                We need only look at F_1 and F_2 in the space of homogenous polynomials of 
                degree d modulo the space of degree d relations of M.

                We can look at the q-expansion of the cusps for the expression:
                    h_i*F_2(f_1,..,f_r) - h_1*F_1(f_1,..,f_r);
                since these are cusp forms, enough vanishing will prove that it is 0. 
    */



    d:=0;
    
    //Id  :=[* *];
    //mon1:=[* *];

    //mon :=[* *];
    //AA:=[* *];

    /*
        Consider the ideal I in Pol_K corresponding to the model of the curve M.
        For each integer m, we have the graded component I_m of degree m.

        We compute a sequence "Id" so that Id[m] is a basis of I_m over M`KG.
        We compute a sequence "mon1" so that mon1[m] is a basis of (Pol_K)_m/I_m.
    */

    M_F0:=[M`F0[i]: i in [1..#M`F0 div M`KG_degree]];
    assert #M_F0 * M`KG_degree eq #M`F0;

    morphism:=[];  //Keep track of F_1/F_2 


    
        done:=false;

        while not done do
            d:=d+1;
            printf "increased d to %o\n",d;

                dQ:=Integers()!Coefficient(Rs!Evaluate(HS,t+O(t^(d+1))),d);
                // dimension of homogeneous relations of degree d 

            //Find the next Id (if needed)
            if #Id eq d-1 then
                mon:= mon cat [* MonomialsOfWeightedDegree(Pol_FF,d) *];
                assert #mon eq d;
                //A:=[ Vector([MonomialCoefficient(p,m) : m in mon[d]]) : p in I_gen | Degree(p) eq d];  

                B:=[ [MonomialCoefficient(p,m) : m in mon[d]] : p in I_gen | Degree(p) eq d];  

                if d gt 1 and dQ ne 0 then
                    B:=B cat [[MonomialCoefficient(x[i]*p,m) : m in mon[d]] :  i in [1..n], p in Id[d-1]];
                    B:=Matrix(B);
                    C:=EchelonForm(Transpose(B));
                    //assert Rank(C) eq dQ;  TODO: CHECK?!
                    pivots:=[ Minimum([j: j in [1..Ncols(C)] | C[i,j] ne 0]) :  i in [1..dQ]];
                    B:=[B[i]: i in pivots]; // chose rows of B that span a space of the same dimension

                end if;

                assert #B eq dQ;
                AA:=AA cat [* B *];
                Id:=Id cat [* [ Pol_FF!(&+[w[i]*mon[d][i]: i in [1..#mon[d]]]) : w in B] *];
            end if;
            
            if #mon1 lt d then //ERAY WHAT IS GOING ON HERE
                if d*M`model_degree ge deg_toc then

                    // Find a basis mon1[d] of (Pol_K)_d/I_d. 
                    V:=KSpace(FF_Q,#mon[d]);
                    W:=sub<V|AA[d]>;
                    mon_:=[];
                    for p in mon[d] do
                        v:=Vector([MonomialCoefficient(p,m) : m in mon[d]]);
                        if v notin W then
                            W:=W + sub<V|[v]>;
                            mon_:=mon_ cat [p];
                        end if;
                        if Dimension(W) eq Dimension(V) then
                            break p; 
                        end if;
                    end for;
                    assert Dimension(W) eq Dimension(V);
                    exponents_mon_:=[Exponents(m): m in mon_];
                    mon1:= mon1 cat [* [&*[y[i]^a[i]: i in [1..n]] : a in exponents_mon_] *];
                else
                    mon1:=mon1 cat [* [] *];
                end if;
            end if;         


            if d*M`model_degree ge deg_toc then
                
                B:=[];
                J:=Sort([O[1]:O in M`cusp_orbits]); 
                for j in J do
                    beta:=[Evaluate(m,[f[j]: f in M_F0]) : m in mon1[d]];
                    beta:=&cat[ [b*f: b in M`KG_integral_basis_cyclotomic] : f in beta];

                    s:=[E6list[j]*b : b in beta] cat [-f[j]*b : b in beta];
                    e:=Minimum([AbsolutePrecision(f): f in s]);
                    B:=B cat [ [ Coefficient(f,i)[k]: f in s] : i in [0..e-1], k in [1..EulerPhi(M`N)] ];  
                    //could use coefficients over smaller field here
                end for;
            

                B:=Matrix(B);
                B:=ChangeRing(Denominator(B)*B,Integers());

                C:=Matrix(Basis(NullspaceOfTranspose(B)));
                C:=LLL(C : Proof:=false);
                S:=[ [&+[v[M`KG_degree*(i-1)+j] * M`KG_integral_basis[j]*mon1[d][i]: i in [1..#mon1[d]], j in [1..M`KG_degree]],
                      &+[v[M`KG_degree*(i-1)+j + #mon1[d]*M`KG_degree] * M`KG_integral_basis[j]*mon1[d][i]: i in [1..#mon1[d]], j in [1..M`KG_degree]]] : v in Rows(C)];
                      
                if #S ge 1 then
                    // number of poles is at most  
                    upper_bound_on_number_of_poles:= d*M`model_degree + deg_toc;
                    "sda";
                    upper_bound_on_number_of_poles;
                    a:=S[1];
                    "wht is this";
                    S;
                    "first term";
                    print(a);
                    zeros:=0;
                    for j in J do
                        den:=Evaluate(a[2],[f[j]: f in M_F0]);
                        if IsWeaklyZero(den) then 
                            continue j; 
                        end if;
                        num:=Evaluate(a[1],[f[j]: f in M_F0]);
                        //h[r][j]*den - h[1][j]*num;
                        v:=Valuation(num/den  - toc[j])-1; 
                        if v ge 1 then 
                            orbit_size:= #M`cusp_orbits[M`cusp_to_orbit[j]];
                            zeros:=zeros+ v * orbit_size;
                        end if;                    
                    end for;
                    "zeros";
                    zeros;
                    if zeros le upper_bound_on_number_of_poles then
                        // Not enough info to provable find morphism.
                        // We increase precision and try again
                        "bidaha";
                        return FindRatio(M,M0,tryingdegs :homogeneous:=homogeneous, prec0:=prec+prec_delta, prec_delta:=prec_delta, Id:=Id, mon1:=mon1,mon:=mon,AA:=AA);
                    end if;

                    done:=true;
                end if;
            end if;
        end while;

        a:=S[1];
        morphism:=morphism cat [a];
        print(morphism);

    
    if not homogeneous then
        return [a[1]/a[2]: a in morphism];
    end if;

    morphism:= [&*([1] cat [morphism[j][2]: j in [1..#morphism]]) : i in [1..#morphism]]
    cat [ morphism[i][1]* &*([1] cat [morphism[j][2]: j in [1..#morphism] | j ne i]) : i in [1..#morphism]];

    Pol_K<[x]>:=PolynomialRing(K,n); 
    morphism:=[Pol_K!f: f in morphism];

    return morphism;
end intrinsic;