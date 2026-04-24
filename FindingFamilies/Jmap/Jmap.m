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
      if potentialprec le prec then
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
	    if (maxprec ge prec) then
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
        if (maxprec ge prec) then
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

intrinsic CuspData(cusp::SetCspElt, field,
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
  gp := Gcong;
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

intrinsic CuspUpdateCoordinates(~cusp::CspDat, X::Crv, F::SeqEnum[SeqEnum]: extra:=false)
{.}
   cuspInd := cusp`ind;
   K := cusp`field;
   v := Minimum([Valuation(f[cuspInd]) : f in F]);
   pt := [Coefficient(f[cuspInd], v) : f in F];
   pt_X := ChangeRing(X, Universe(pt))!pt;

   assert K subset Parent(pt_X[1]);
   if extra then 
        pt_X := ChangeRing(X, Parent(pt_X[1]))!Eltseq(pt_X);
        //cusp`field:=Parent(pt_X[1]);
   else
        pt_X := ChangeRing(X, K)!Eltseq(pt_X);
   end if;
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




