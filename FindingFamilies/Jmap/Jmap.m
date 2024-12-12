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
      PP<qN> := LaurentSeriesRing(KK);
      Embed(KK,Parent(z),prim);
      totalprec := totalprec + maxprec*Degree(KK);
      curfour := <>;
      for i in [1..#modforms0] do
	  newfourier := &+[ KK!Coefficient(modforms0[i][c],l)*qN^l : l in [0..AbsolutePrecision(modforms0[i][c])-1]] + BigO(qN^AbsolutePrecision(modforms0[i][c]));
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


  FFFF<qN> := LaurentSeriesRing(Rationals());
  j := (1728*Eisenstein(4,qN : Precision := Ceiling((maxprec+2*N)/N))^3)/(Eisenstein(4,qN : Precision := Ceiling((maxprec+2*N)/N))^3 - Eisenstein(6,qN : Precision := Ceiling((maxprec+2*N)/N))^2);
  j := Evaluate(j,qN^N);

  func := j;
  done := false;
  

  curd := mind;
  jmat := ZeroMatrix(Rationals(),0,totalprec);
  for i in [1..#canring[curd][1]] do
      vecseq := [];
      for jj in [1..#chosencusps] do
	  pp := (func*canring[curd][1][i][jj]);
	  vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [-N..-N+maxprec-1]]);
      end for;
      jmat := VerticalJoin(jmat,Matrix(Rationals(),1,totalprec,vecseq));
  end for;

  for i in [1..#canring[curd][1]] do
      vecseq := [];
      for jj in [1..#chosencusps] do
	  pp := -canring[curd][1][i][jj];
	  vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [-N..-N+maxprec-1]]);
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
	      pp := (func*canring[curd][1][i][jj]);
	      vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [-N..-N+maxprec-1]]);
	  end for;
	  jmat := VerticalJoin(jmat,Matrix(Rationals(),1,totalprec,vecseq));
      end for;

      for i in [1..#canring[curd][1]] do
	  vecseq := [];
	  for jj in [1..#chosencusps] do
	      pp := -canring[curd][1][i][jj];
	      vecseq := vecseq cat (&cat [ Eltseq(Coefficient(pp,m)) : m in [-N..-N+maxprec-1]]);
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
  weakzero := [ &+[ v[i]*canring[curd][1][i][j] : i in [1..canringdim]]*func - &+[ v[i+canringdim]*canring[curd][1][i][j] : i in [1..canringdim]] : j in [1..#chosencusps]];
  assert &and [ IsWeaklyZero(weakzero[i]) : i in [1..#chosencusps]];

  jmap := map<C -> ProjectiveSpace(Rationals(),1) | [num,denom]>;
  return C, [num, denom], model_type, M`F0, M,mind,maxd,maxprec;
 end intrinsic;