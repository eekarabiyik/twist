/*
  main-fixed-intrinsics.m

  Intrinsic-only copy of main-fixed.m.  All named Magma functions in that
  file have been converted to user-defined intrinsics so that require
  statements are legal.  main.m and main-fixed.m remain unchanged.

  Corrected working copy of main.m.  The original main.m is intentionally
  unchanged.  Every implemented correction below is marked with "FIX:".

  REMAINING EXTERNAL OR MODEL-DEPENDENT WORK

  (1) FindRatio must obey one documented convention.  This file expects

          ratio_map = [numerator(h), denominator(h)],  h = f_0^2/E_6.

      The homogeneous branch of the currently inspected FindRatio returns
      these two entries in the opposite order.  Fix that producer (and its
      callers/tests) by changing its final homogeneous pair from
      [denominator,numerator] to [numerator,denominator]; this consumer cannot
      reliably infer that they were swapped.

  (2) The attached GL2 support code must provide the two-argument intrinsic

          GL2TorsionDegree(H, d).

      The one-argument intrinsic silently replaces d by the minimal level of
      H and is not an exact-order-d test.  torsionorder below now makes the
      correct two-argument call, but the intrinsic itself lives outside this
      file (for example in Modular/EarlierCode/gl2base.m).  The attached spec
      must load that overload before this file is used.

  (3) LowDegreeDivisor has a caller-supplied KnownDivisor option.  If no
      rational point is found within SearchBound, it tries all pairs of
      ambient coordinates.  On a curve representation for which Magma cannot
      construct any of those rational maps/divisor fibres, pass a certified
      positive-degree divisor explicitly.

  (4) The input data must be certified to use the same conjugate/fine group,
      coordinate model, j-map, and ratio map.  This file checks full
      determinant and absence of -I, but it cannot reconstruct a missing
      compatibility certificate between independently produced inputs.

  (5) The return value is the generic fibre over Q(C).  Constructing a
      globally minimal elliptic scheme requires an open cover and local
      changes of variables; that is a separate patching computation.

  (6) Run the end-to-end examples under the exact Magma/spec environment in
      which the modular-curve records are produced.  Magma was not available
      on PATH when this corrected copy was prepared, so only static checks
      could be run here.
*/


// ---------------------------------------------------------------------------
// Shared exact arithmetic and presentation helpers
// ---------------------------------------------------------------------------

// FIX: preserve the denominator used to clear rational coefficients.  The
// old code took a gcd after clearing denominators but then discarded the
// clearing factor, which gives the wrong rational content.
intrinsic RationalPolynomialContent(P::RngMPolElt) -> FldRatElt
{Returns the exact rational content of a nonzero multivariate polynomial.}
  require P ne 0: "RationalPolynomialContent is undefined for zero.";
  cs := Coefficients(P);
  den := LCM([ Denominator(c) : c in cs ]);
  nums := [ Integers()!(den*c) : c in cs ];
  return (Rationals()!Abs(GCD(nums)))/den;
end intrinsic;

intrinsic HomogeneousPairContent(pair::SeqEnum[RngMPolElt]) -> FldRatElt
{Returns the rational content of a homogeneous numerator-denominator pair.}
  require pair[1] ne 0 and pair[2] ne 0:
    "The numerator and denominator must be nonzero.";
  return RationalPolynomialContent(pair[1]) /
         RationalPolynomialContent(pair[2]);
end intrinsic;


// FIX: collect prime support from both the numerator and denominator of a
// rational content, including fractional contents.
intrinsic AddRationalPrimeSupport(primes::SeqEnum[RngIntElt],
                                      c::FldRatElt) -> SeqEnum[RngIntElt]
{Adds the prime support of a nonzero rational number to a prime sequence.}
  require c ne 0: "Cannot take the prime support of zero.";
  for p in PrimeFactors(Abs(Numerator(c))) do
    if not p in primes then
      Append(~primes,p);
    end if;
  end for;
  for p in PrimeFactors(Abs(Denominator(c))) do
    if not p in primes then
      Append(~primes,p);
    end if;
  end for;
  return primes;
end intrinsic;


// FIX: use the actual Weierstrass weights and Floor, not Round, when taking
// a common rational scaling out of a list of coefficients.
intrinsic WeightedConstantMultiplier(
    pairs::SeqEnum[SeqEnum[RngMPolElt]],
    weights::SeqEnum[RngIntElt]) -> FldRatElt
{Returns the exact common weighted rational multiplier of coefficient pairs.}
  require #pairs eq #weights: "A weight is required for every pair.";
  contents := [];
  active_weights := [];
  primes := [];
  for i in [1..#pairs] do
    require pairs[i][2] ne 0: "A homogeneous denominator is zero.";
    if pairs[i][1] ne 0 then
      c := HomogeneousPairContent(pairs[i]);
      Append(~contents,c);
      Append(~active_weights,weights[i]);
      primes := AddRationalPrimeSupport(primes,c);
    end if;
  end for;
  require #contents gt 0: "At least one coefficient must be nonzero.";

  q := Rationals()!1;
  for p in primes do
    e := Min([ Floor(Valuation(contents[i],p)/active_weights[i])
               : i in [1..#contents] ]);
    q *:= (Rationals()!p)^e;
  end for;
  return q;
end intrinsic;


// If h = num/den and q is the common multiplier, this returns a homogeneous
// presentation of h/q^weight.  FIX: for q^{-1}=nm/dm the numerator receives
// nm^weight and the denominator receives dm^weight; the old direction was
// reversed whenever q was fractional.
intrinsic ScaleHomogeneousPair(pair::SeqEnum[RngMPolElt],
                                   q::FldRatElt,
                                   weight::RngIntElt)
    -> RngMPolElt, RngMPolElt
{Returns a homogeneous pair representing the coefficient divided by q^weight.}
  nm := Numerator(1/q);
  dm := Denominator(1/q);
  return pair[1]*nm^weight, pair[2]*dm^weight;
end intrinsic;


// FIX: centralize dehomogenization into Q(C), so all final coefficients live
// in the curve function field rather than the unrelated fraction field of
// the ambient polynomial ring.
intrinsic PairToFunctionField(num::RngMPolElt, den::RngMPolElt,
                                  C::Crv, QC::Any, polyring::RngMPol) -> Any
{Dehomogenizes a polynomial pair into the supplied curve function field.}
  vals := [ QC.i : i in [1..Rank(polyring)-1] ] cat [ QC!1 ];
  require #vals eq Rank(polyring):
    "The polynomial ring and curve model have incompatible coordinates.";
  denfunc := Evaluate(den,vals);
  require denfunc ne 0: "A denominator vanishes identically on the curve.";
  return Evaluate(num,vals)/denfunc;
end intrinsic;


// FIX: one zero-safe homogenization routine replaces several duplicated
// blocks that called Max on an empty monomial list.
intrinsic FunctionToHomogeneousPair(h::Any, polyring::RngMPol)
    -> RngMPolElt, RngMPolElt
{Returns a common-degree homogeneous numerator-denominator presentation.}
  if h eq 0 then
    return polyring!0, polyring!1;
  end if;

  affine_vars := [ polyring.i : i in [1..Rank(polyring)-1] ];
  num0 := polyring!Evaluate(Numerator(h),affine_vars);
  den0 := polyring!Evaluate(Denominator(h),affine_vars);
  require den0 ne 0: "A function-field denominator was parsed as zero.";

  cnum, mnum := CoefficientsAndMonomials(num0);
  cden, mden := CoefficientsAndMonomials(den0);
  dnum := Max([ Degree(m) : m in mnum ]);
  dden := Max([ Degree(m) : m in mden ]);
  d := Max(dnum,dden);
  z := polyring.(Rank(polyring));

  num := &+[ cnum[i]*mnum[i]*z^(d-Degree(mnum[i]))
             : i in [1..#mnum] ];
  den := &+[ cden[i]*mden[i]*z^(d-Degree(mden[i]))
             : i in [1..#mden] ];
  return num, den;
end intrinsic;


intrinsic PolynomialIntegerHeight(P::RngMPolElt) -> RngIntElt
{Returns a denominator-sensitive integer coefficient height.}
  if P eq 0 then
    return 0;
  end if;
  cs := Coefficients(P);
  den := LCM([ Denominator(c) : c in cs ]);
  return Max([ den ] cat [ Abs(Integers()!(den*c)) : c in cs ]);
end intrinsic;


intrinsic PairDegree(pair::SeqEnum[RngMPolElt]) -> RngIntElt
{Returns the maximum degree of a homogeneous numerator-denominator pair.}
  numdeg := pair[1] eq 0 select 0 else Degree(pair[1]);
  dendeg := Degree(pair[2]);
  return Max(numdeg,dendeg);
end intrinsic;


// FIX: select among valid torsion-point presentations by a deterministic
// structural score (degrees, term count, coefficient height), rather than by
// the length of Magma's pretty-printed string.
intrinsic PresentationScore(
    pairs::SeqEnum[SeqEnum[RngMPolElt]]) -> SeqEnum[RngIntElt]
{Returns the deterministic structural score of a coefficient presentation.}
  // FIX: PairDegree also avoids asking Magma for the degree of the zero
  // numerator in a coefficient that vanishes.
  degrees := [ PairDegree(pair) : pair in pairs ];
  terms := [ #Coefficients(pair[1]) + #Coefficients(pair[2])
             : pair in pairs ];
  heights := [ Max(PolynomialIntegerHeight(pair[1]),
                   PolynomialIntegerHeight(pair[2])) : pair in pairs ];
  return [ Max(degrees), &+degrees, &+terms, Max(heights), &+heights ];
end intrinsic;


intrinsic HasExactOrder(P::Any, d::RngIntElt) -> BoolElt
{Returns true exactly when the elliptic-curve point P has order d.}
  if d*P ne 0*P then
    return false;
  end if;
  for p in PrimeDivisors(d) do
    if (d div p)*P eq 0*P then
      return false;
    end if;
  end for;
  return true;
end intrinsic;


intrinsic CInvariantsFromA(a::SeqEnum) -> Any, Any
{Returns c4 and c6 from five Weierstrass coefficients.}
  require #a eq 5: "Five Weierstrass coefficients are required.";
  b2 := a[1]^2+4*a[2];
  b4 := a[1]*a[3]+2*a[4];
  b6 := a[3]^2+4*a[5];
  c4 := b2^2-24*b4;
  c6 := -b2^3+36*b2*b4-216*b6;
  return c4, c6;
end intrinsic;


intrinsic PositiveDivisorDegree(D::DivCrvElt) -> RngIntElt
{Returns the degree of the positive part of a curve divisor.}
  ans := 0;
  for term in Decomposition(D) do
    if term[2] gt 0 then
      ans +:= term[2]*Degree(term[1]);
    end if;
  end for;
  return ans;
end intrinsic;


intrinsic CoefficientDivisorScore(Afunc::Any,
                                      Bfunc::Any) -> SeqEnum[RngIntElt]
{Returns the lexicographic complete-divisor score of short coefficients.}
  Adeg := PositiveDivisorDegree(Divisor(Afunc));
  Bdeg := PositiveDivisorDegree(Divisor(Bfunc));
  return [ Adeg+Bdeg, Max(Adeg,Bdeg), Adeg, Bdeg ];
end intrinsic;


// ---------------------------------------------------------------------------
// A low-degree base divisor for divisor reduction
// ---------------------------------------------------------------------------

intrinsic LowDegreeDivisor(C::Crv : KnownDivisor:=0, SearchBound:=100,
                                      verbose:=false) -> DivCrvElt
{Returns a positive-degree divisor suitable for divisor reduction.}
  // FIX: derive the genus from C instead of trusting a separate caller value;
  // genus and ambient coordinate rank are validated independently below.
  g := Genus(C);

  // FIX: permit a rigorously chosen divisor to be supplied when bounded point
  // search or the model-specific coordinate projection is unsuitable.
  if Type(KnownDivisor) ne RngIntElt then
    require Degree(KnownDivisor) gt 0:
      "KnownDivisor must have positive degree.";
    return KnownDivisor;
  end if;
  require KnownDivisor eq 0:
    "KnownDivisor must be 0 or a positive-degree divisor on C.";
  require SearchBound ge 1: "SearchBound must be positive.";

  P1 := ProjectiveSpace(Rationals(),1);
  if g eq 0 and #DefiningEquations(C) eq 0 then
    return Divisor(C![1,0]);
  elif g eq 0 then
    // FIX: -K_C has degree 2 on every genus-zero curve; describe it as a
    // positive-degree base divisor, not as evidence that the conic is
    // pointless.
    E := -CanonicalDivisor(C);
    require Degree(E) eq 2: "Unexpected canonical degree in genus zero.";
    return E;
  end if;

  pts := PointSearch(C,SearchBound);
  if #pts gt 0 then
    return Divisor(C!Eltseq(pts[1]));
  end if;

  // FIX: search every coordinate ratio rather than assuming [C.1,C.2] is a
  // nonconstant finite map on every projective model.  Individual pairs can
  // have a base locus or be constant, so failed pairs are skipped.
  if verbose then
    printf "No point found up to bound %o; trying coordinate maps.\n",
           SearchBound;
  end if;
  ncoords := Rank(CoordinateRing(Ambient(C)));
  for i in [1..ncoords-1] do
    for j in [i+1..ncoords] do
      try
        phi := map<C -> P1 | [C.i,C.j]>;
        D := Divisor(C,(P1![1,0])@@phi);
        for P in Support(D) do
          E := Divisor(P);
          if Degree(E) gt 0 then
            if verbose then
              printf "Using coordinate pair (%o,%o).\n",i,j;
            end if;
            return E;
          end if;
        end for;
      catch err;
        // FIX: an empty catch body is invalid Magma syntax.  This statement
        // also makes the skipped coordinate pair visible in verbose mode.
        if verbose then
          printf "Coordinate pair (%o,%o) failed; trying the next pair.\n",i,j;
        end if;
      end try;
    end for;
  end for;
  require false:
    "No coordinate map produced a divisor; supply KnownDivisor.";
  return 0;
end intrinsic;


// ---------------------------------------------------------------------------
// Initial reduction of y^2 = x^3 + A*x + B
// ---------------------------------------------------------------------------

intrinsic FirstReduction(polyring::RngMPol, C::Crv, E::DivCrvElt,
                             A::Any, B::Any : verbose:=false)
    -> RngMPolElt, RngMPolElt, RngMPolElt, RngMPolElt
{Reduces and homogenizes the coefficients of a short Weierstrass equation.}
  QC := FunctionField(C);
  Afunc := PairToFunctionField(Numerator(A),Denominator(A),C,QC,polyring);
  Bfunc := PairToFunctionField(Numerator(B),Denominator(B),C,QC,polyring);
  require Afunc ne 0 and Bfunc ne 0:
    "The generic j-map must avoid the identically special fibres j=0,1728.";

  Adiv := Divisor(Afunc);
  Bdiv := Divisor(Bfunc);

  // FIX: form the support as a union of the separate divisors of A, B, and E.
  // Decomposing xdiv+E can cancel a place and omit a required valuation.
  allsup := [];
  for term in (Decomposition(Adiv) cat Decomposition(Bdiv) cat
               Decomposition(E)) do
    if not term[1] in allsup then
      Append(~allsup,term[1]);
    end if;
  end for;

  avals := [ Valuation(Adiv,P) : P in allsup ];
  bvals := [ Valuation(Bdiv,P) : P in allsup ];

  // FIX: these are divisor exponents and therefore require floors.  Rounding
  // can remove too much at negative as well as positive valuations.
  changevals := [ Min(Floor(avals[i]/4),Floor(bvals[i]/6))
                  : i in [1..#allsup] ];
  change := 0*E;
  for i in [1..#allsup] do
    change +:= changevals[i]*allsup[i];
  end for;

  oldscore := CoefficientDivisorScore(Afunc,Bfunc);
  if verbose then
    printf "Starting divisor score [sum,max,A,B] = %o.\n",oldscore;
  end if;

  redD, rr, Ered, func := Reduction(change,E);
  require func ne 0: "Divisor reduction returned the zero function.";
  // Reduction gives change = redD + rr*Ered - div(func).  Thus multiplying
  // A and B by func^4 and func^6 implements the admissible Weierstrass
  // scaling.  FIX: do not assume redD has degree zero or unchanged support.
  candidateA := Afunc*func^4;
  candidateB := Bfunc*func^6;
  newscore := CoefficientDivisorScore(candidateA,candidateB);

  // FIX: compare a total deterministic score.  The old test rejected a
  // candidate only when both individual degrees strictly increased.
  if newscore lt oldscore then
    newA := candidateA;
    newB := candidateB;
    chosenfunc := func;
    chosenscore := newscore;
  else
    newA := Afunc;
    newB := Bfunc;
    chosenfunc := QC!1;
    chosenscore := oldscore;
  end if;

  Anum, Aden := FunctionToHomogeneousPair(newA,polyring);
  Bnum, Bden := FunctionToHomogeneousPair(newB,polyring);
  Apair := [ Anum, Aden ];
  Bpair := [ Bnum, Bden ];

  // FIX: normalize rational content with exact weights 4 and 6, retaining
  // denominator information and handling an empty prime support as q=1.
  q := WeightedConstantMultiplier([Apair,Bpair],[4,6]);
  Anum, Aden := ScaleHomogeneousPair(Apair,q,4);
  Bnum, Bden := ScaleHomogeneousPair(Bpair,q,6);

  // FIX: certify the square class, not just the j-invariant.  These exact
  // identities exhibit the fourth/sixth-power scale from the input short
  // equation to the reduced one.
  short_scale := chosenfunc/(QC!q);
  Acheck := PairToFunctionField(Anum,Aden,C,QC,polyring);
  Bcheck := PairToFunctionField(Bnum,Bden,C,QC,polyring);
  require Acheck eq Afunc*short_scale^4 and
          Bcheck eq Bfunc*short_scale^6:
    "Initial reduction changed the square class of the short model.";

  if verbose then
    printf "Chosen divisor score [sum,max,A,B] = %o.\n",chosenscore;
    printf "Rational weighted multiplier = %o.\n",q;
  end if;
  return Anum, Aden, Bnum, Bden;
end intrinsic;


// ---------------------------------------------------------------------------
// Rational torsion detected from the fine group
// ---------------------------------------------------------------------------

intrinsic torsionorder(GG::GrpMat) -> RngIntElt
{Returns the largest rational torsion order detected from the fine group.}
  N0 := Characteristic(BaseRing(GG));
  require N0 gt 0: "torsionorder requires a finite-level matrix group.";
  maxtors := 1;
  for d in Divisors(N0) do
    if d gt maxtors then
      // The transpose is intentional: the fine-moduli point convention is
      // dual to the ordinary column-vector Galois representation.
      Hd := sub< GL(2,Integers(d)) |
                 [ Transpose(t) : t in Generators(GG) ] >;

      // FIX: ask for primitive vectors of exact exponent d.  Calling the
      // one-argument overload here can reduce Hd to a smaller minimal level
      // and falsely report a rational d-torsion point.
      torsdeg := GL2TorsionDegree(Hd,d);
      if torsdeg eq 1 then
        maxtors := d;
      end if;
    end if;
  end for;
  return maxtors;
end intrinsic;


// ---------------------------------------------------------------------------
// Kubert--Tate form from a point of exact order d >= 3
// ---------------------------------------------------------------------------

intrinsic KTform(C::Crv, QC::Any, polyring::RngMPol,
                     A::Any, B::Any, d::RngIntElt : verbose:=false)
    -> SeqEnum[RngMPolElt], FldRatElt
{Returns a normalized Kubert--Tate presentation with marked order d at least 3.}
  require d ge 3: "KTform requires d >= 3.";

  // Retain the P^1 workaround from main.m for Magma versions affected by the
  // nested function-field root bug.
  if #DefiningEquations(C) eq 0 then
    P1case := true;
    newQC := FunctionField(Rationals());
    Ffieldpoly := FunctionField(newQC);
    Afunc := Evaluate(Numerator(A),[newQC.1,newQC!1]) /
             Evaluate(Denominator(A),[newQC.1,newQC!1]);
    Bfunc := Evaluate(Numerator(B),[newQC.1,newQC!1]) /
             Evaluate(Denominator(B),[newQC.1,newQC!1]);
    Acurve := Evaluate(Afunc,QC.1);
  else
    P1case := false;
    Ffieldpoly := FunctionField(QC);
    Afunc := PairToFunctionField(Numerator(A),Denominator(A),C,QC,polyring);
    Bfunc := PairToFunctionField(Numerator(B),Denominator(B),C,QC,polyring);
    Acurve := Afunc;
  end if;

  rawE := EllipticCurve([0,0,0,Afunc,Bfunc]);
  require Discriminant(rawE) ne 0: "The short generic fibre is singular.";

  // The Moebius product is the exact-order division polynomial.  Negative
  // Moebius exponents make a rational function, hence Numerator below.
  divpol0 := &*[ Evaluate(DivisionPolynomial(rawE,e),Ffieldpoly.1)^(
                  MoebiusMu(Integers()!(d/e))) : e in Divisors(d) ];
  divpol := Numerator(divpol0);
  if verbose then
    printf "Finding roots of the exact-order-%o division polynomial.\n",d;
  end if;
  rts := Roots(divpol);

  pts := [];
  for rt in rts do
    chk, P := IsPoint(rawE,rt[1]);
    // FIX: a division-polynomial root is accepted only after checking exact
    // order on the elliptic curve itself.
    if chk then
      if HasExactOrder(P,d) then
        Append(~pts,P);
      end if;
    end if;
  end for;
  require #pts gt 0:
    "No rational point of the required exact order was recovered.";

  have_best := false;
  best := [];
  bestscore := [];
  bestscale := Rationals()!1;
  for k in [1..#pts] do
    if verbose then
      printf "Trying exact-order point %o of %o.\n",k,#pts;
    end if;

    x0 := pts[k][1];
    y0 := pts[k][2];
    if P1case then
      x0 := Evaluate(x0,QC.1);
      y0 := Evaluate(y0,QC.1);
    end if;
    require y0 ne 0:
      "An exact-order point with d >= 3 cannot have y-coordinate 0.";

    // FIX: use the rigorously derived translation/shear formulas directly.
    // After x=X+x0, y=Y+y0 and Y=Y'+sX with
    // s=(3*x0^2+A)/(2*y0), the point is (0,0) and
    //
    //   Y'^2 + (2s)XY' + (2y0)Y' = X^3 + (3x0-s^2)X^2.
    s := (3*x0^2+Acurve)/(2*y0);
    a1 := 2*s;
    a2 := 3*x0-s^2;
    a3 := 2*y0;

    n1, d1 := FunctionToHomogeneousPair(a1,polyring);
    n2, d2 := FunctionToHomogeneousPair(a2,polyring);
    n3, d3 := FunctionToHomogeneousPair(a3,polyring);
    pairs := [ [n1,d1], [n2,d2], [n3,d3] ];

    // FIX: normalize using weights (1,2,3), exact floors, and the corrected
    // numerator/denominator scaling direction.
    q := WeightedConstantMultiplier(pairs,[1,2,3]);
    n1, d1 := ScaleHomogeneousPair(pairs[1],q,1);
    n2, d2 := ScaleHomogeneousPair(pairs[2],q,2);
    n3, d3 := ScaleHomogeneousPair(pairs[3],q,3);
    normalized := [ [n1,d1], [n2,d2], [n3,d3] ];
    score := PresentationScore(normalized);
    candidate := [n1,d1,n2,d2,n3,d3];

    if not have_best then
      have_best := true;
      best := candidate;
      bestscore := score;
      bestscale := 1/q;
    elif score lt bestscore then
      best := candidate;
      bestscore := score;
      bestscale := 1/q;
    end if;
  end for;

  require have_best: "KTform failed to construct a presentation.";
  // The second return value is the explicit c4/c6 scale from the short
  // model to the normalized Kubert--Tate model.
  return best, bestscale;
end intrinsic;


// ---------------------------------------------------------------------------
// Form with a marked point of exact order 2
// ---------------------------------------------------------------------------

intrinsic KTform2(C::Crv, QC::Any, polyring::RngMPol,
                      A::Any, B::Any : verbose:=false)
    -> SeqEnum[RngMPolElt], FldRatElt
{Returns a normalized presentation with a marked point of exact order 2.}
  if #DefiningEquations(C) eq 0 then
    P1case := true;
    newQC := FunctionField(Rationals());
    Afunc := Evaluate(Numerator(A),[newQC.1,newQC!1]) /
             Evaluate(Denominator(A),[newQC.1,newQC!1]);
    Bfunc := Evaluate(Numerator(B),[newQC.1,newQC!1]) /
             Evaluate(Denominator(B),[newQC.1,newQC!1]);
    Acurve := Evaluate(Afunc,QC.1);
  else
    P1case := false;
    Afunc := PairToFunctionField(Numerator(A),Denominator(A),C,QC,polyring);
    Bfunc := PairToFunctionField(Numerator(B),Denominator(B),C,QC,polyring);
    Acurve := Afunc;
  end if;

  rawE := EllipticCurve([0,0,0,Afunc,Bfunc]);
  require Discriminant(rawE) ne 0: "The short generic fibre is singular.";
  divpol := DivisionPolynomial(rawE,2);
  if verbose then
    printf "Finding roots of the 2-division polynomial.\n";
  end if;
  rts := Roots(divpol);

  pts := [];
  for rt in rts do
    chk, P := IsPoint(rawE,rt[1]);
    // FIX: validate exact order here as well, instead of accepting every
    // object returned from an x-coordinate root.
    if chk then
      if HasExactOrder(P,2) then
        Append(~pts,P);
      end if;
    end if;
  end for;
  require #pts gt 0:
    "No rational point of exact order 2 was recovered.";

  have_best := false;
  best := [];
  bestscore := [];
  bestscale := Rationals()!1;
  for k in [1..#pts] do
    x0 := pts[k][1];
    if P1case then
      x0 := Evaluate(x0,QC.1);
    end if;

    // FIX: translating the 2-torsion point (x0,0) to the origin gives
    // y^2=x^3+(3*x0)x^2+(3*x0^2+A)x.
    a2 := 3*x0;
    a4 := 3*x0^2+Acurve;
    n2, d2 := FunctionToHomogeneousPair(a2,polyring);
    n4, d4 := FunctionToHomogeneousPair(a4,polyring);
    pairs := [ [n2,d2], [n4,d4] ];

    // FIX: a2 and a4 have weights 2 and 4 (not 1 and 2).
    q := WeightedConstantMultiplier(pairs,[2,4]);
    n2, d2 := ScaleHomogeneousPair(pairs[1],q,2);
    n4, d4 := ScaleHomogeneousPair(pairs[2],q,4);
    normalized := [ [n2,d2], [n4,d4] ];
    score := PresentationScore(normalized);
    candidate := [n2,d2,n4,d4];

    if not have_best then
      have_best := true;
      best := candidate;
      bestscore := score;
      bestscale := 1/q;
    elif score lt bestscore then
      best := candidate;
      bestscore := score;
      bestscale := 1/q;
    end if;
  end for;

  require have_best: "KTform2 failed to construct a presentation.";
  return best, bestscale;
end intrinsic;


// ---------------------------------------------------------------------------
// Assemble one valid five-coefficient Weierstrass model over Q(C)
// ---------------------------------------------------------------------------

// FIX: Magma permits at most six mandatory arguments in an intrinsic
// signature.  Bundle [Anum,Aden,Bnum,Bden] into short_model so this intrinsic
// has five mandatory arguments rather than eight.
intrinsic FinalReduction(C::Crv, H0::GrpMat, QC::Any,
                         polyring::RngMPol,
                         short_model::SeqEnum[RngMPolElt] :
                         verbose:=false) -> SeqEnum
{Returns five certified Weierstrass coefficients over the curve function field.}
  require #short_model eq 4:
    "short_model must be [Anum,Aden,Bnum,Bden].";
  Anum := short_model[1];
  Aden := short_model[2];
  Bnum := short_model[3];
  Bden := short_model[4];
  require Aden ne 0 and Bden ne 0:
    "The short-model denominators must be nonzero.";

  ambientF := FieldOfFractions(polyring);
  A := (ambientF!Anum)/(ambientF!Aden);
  B := (ambientF!Bnum)/(ambientF!Bden);
  Afunc := PairToFunctionField(Anum,Aden,C,QC,polyring);
  Bfunc := PairToFunctionField(Bnum,Bden,C,QC,polyring);
  Eshort := EllipticCurve([QC|0,0,0,Afunc,Bfunc]);
  require Discriminant(Eshort) ne 0: "The reduced short model is singular.";

  d := torsionorder(H0);
  marked_order := 1;
  model_scale := QC!1;
  if d eq 1 then
    // FIX: all branches now return the same object: five a-invariants in QC.
    a_inv := [QC|0,0,0,Afunc,Bfunc];
  elif d eq 2 then
    lst, rational_scale := KTform2(C,QC,polyring,A,B : verbose:=verbose);
    model_scale := QC!rational_scale;
    a2 := PairToFunctionField(lst[1],lst[2],C,QC,polyring);
    a4 := PairToFunctionField(lst[3],lst[4],C,QC,polyring);
    a_inv := [QC|0,a2,0,a4,0];
    marked_order := 2;
    if verbose then
      printf "Final model: a2=(%o)/(%o), a4=(%o)/(%o).\n",
             lst[1],lst[2],lst[3],lst[4];
    end if;
  else
    // A point of order d yields one of order e for every e|d.  As in main.m,
    // use the smallest e>=3 to seek the simplest marked normal form.
    use := Min([ e : e in Divisors(d) | e ge 3 ]);
    lst, rational_scale := KTform(C,QC,polyring,A,B,use : verbose:=verbose);
    model_scale := QC!rational_scale;
    a1 := PairToFunctionField(lst[1],lst[2],C,QC,polyring);
    a2 := PairToFunctionField(lst[3],lst[4],C,QC,polyring);
    a3 := PairToFunctionField(lst[5],lst[6],C,QC,polyring);
    // FIX: the old branch returned only four entries and omitted a6.
    a_inv := [QC|a1,a2,a3,0,0];
    marked_order := use;
    if verbose then
      printf "Final model: a1=(%o)/(%o), a2=(%o)/(%o), a3=(%o)/(%o).\n",
             lst[1],lst[2],lst[3],lst[4],lst[5],lst[6];
    end if;
  end if;

  // FIX: enforce inexpensive exact postconditions on every return path.
  Eout := EllipticCurve(a_inv);
  require Discriminant(Eout) ne 0: "The final Weierstrass model is singular.";

  // FIX: unlike a j-only comparison, these two identities rule out an
  // accidental quadratic twist.  Translation and shear have u=1, while the
  // recorded model_scale is the explicit weighted scaling.
  c4short, c6short := CInvariantsFromA([QC|0,0,0,Afunc,Bfunc]);
  c4out, c6out := CInvariantsFromA(a_inv);
  require c4out eq c4short*model_scale^4 and
          c6out eq c6short*model_scale^6:
    "The final model is not in the certified short-model isomorphism class.";
  require jInvariant(Eout) eq jInvariant(Eshort):
    "A coordinate transformation changed the j-invariant.";
  if marked_order gt 1 then
    P0 := Eout![0,0,1];
    require HasExactOrder(P0,marked_order):
      "The marked point (0,0) does not have the asserted exact order.";
  end if;

  return a_inv;
end intrinsic;


intrinsic CoordinateNames(n::RngIntElt) -> SeqEnum[MonStgElt]
{Returns n distinct capitalized names for homogeneous coordinates.}
  // FIX: use capital letters so transported/output variables cannot be
  // confused with the lower-case variables in the input polynomial rings.
  standard := [ "X","Y","Z","W","T","U","V","R","S",
                "A","B","C","D","E","F","G","H","I","K",
                "L","M","N","O","P","Q","J" ];
  ans := [];
  for i in [1..n] do
    if i le #standard then
      Append(~ans,standard[i]);
    else
      // FIX: avoid the old hard failure once the coordinate rank exceeded
      // the fixed list of 26 names.
      Append(~ans,"X" cat IntegerToString(i));
    end if;
  end for;
  return ans;
end intrinsic;


/*
  Inputs:

    M0          modular-curve record for a full-determinant subgroup G that
                does not contain -I;
    model       a projective curve model for X_G;
    j_map       [jnum,jden] in homogeneous coordinates on model;
    ratio_map   [hnum,hden] for h=f_0^2/E_6, in the same coordinates.

  Optional parameters:

    verbose             diagnostic printing;
    BaseDivisor         0, or a caller-certified positive-degree divisor;
    PointSearchBound    bound used only when BaseDivisor is 0.

  Output: [a1,a2,a3,a4,a6] over Q(model).
*/
intrinsic FindUnivECModel(M0::Rec, model::Crv,
                              j_map::SeqEnum[RngMPolElt],
                              ratio_map::SeqEnum[RngMPolElt] :
                              verbose:=false, BaseDivisor:=0,
                              PointSearchBound:=100) -> SeqEnum
{Constructs five Weierstrass coefficients for the generic universal curve.}
  require #j_map eq 2 and #ratio_map eq 2:
    "j_map and ratio_map must each be [numerator,denominator].";

  inputring := Parent(j_map[1]);
  // FIX: j_map and ratio_map may have been constructed in distinct, but
  // structurally identical, multivariate polynomial rings.  Magma raises an
  // incompatibility error when such parent rings are compared with eq.  Test
  // their coefficient fields and ranks separately, then transport each
  // polynomial explicitly by evaluating corresponding variables below.
  require (BaseRing(inputring) cmpeq Rationals()) and
          (BaseRing(Parent(j_map[2])) cmpeq Rationals()) and
          (BaseRing(Parent(ratio_map[1])) cmpeq Rationals()) and
          (BaseRing(Parent(ratio_map[2])) cmpeq Rationals()):
    "All homogeneous-map entries must be defined over the rationals.";
  rank := Rank(inputring);
  require rank ge 2:
    "The maps must be given in homogeneous projective coordinates.";
  require Rank(Parent(j_map[2])) eq rank and
          Rank(Parent(ratio_map[1])) eq rank and
          Rank(Parent(ratio_map[2])) eq rank:
    "All homogeneous-map entries must have the same coordinate rank.";

  // FIX: the polynomial-ring rank is the number of homogeneous coordinates,
  // not the genus.  In particular, X(1)=P^1 needs two coordinates although
  // its genus is zero.
  polyring := PolynomialRing(Rationals(),rank,"grevlex");
  coordinate_names := CoordinateNames(rank);
  AssignNames(~polyring,coordinate_names);
  target_variables := [ polyring.i : i in [1..rank] ];
  jnum := polyring!Evaluate(j_map[1],target_variables);
  jden := polyring!Evaluate(j_map[2],target_variables);
  hnum := polyring!Evaluate(ratio_map[1],target_variables);
  hden := polyring!Evaluate(ratio_map[2],target_variables);
  require jnum ne 0 and jden ne 0 and hnum ne 0 and hden ne 0:
    "No input numerator or denominator may be the zero polynomial.";
  require IsHomogeneous(jnum) and IsHomogeneous(jden) and
          IsHomogeneous(hnum) and IsHomogeneous(hden):
    "The maps must be represented by homogeneous polynomials.";
  require Degree(jnum) eq Degree(jden) and
          Degree(hnum) eq Degree(hden):
    "Each homogeneous numerator/denominator pair must have equal degree.";

  C := model;
  require BaseRing(C) eq Rationals():
    "The modular-curve model must be defined over the rationals.";
  require Rank(CoordinateRing(Ambient(C))) eq rank:
    "The maps and curve model use different numbers of coordinates.";
  require Genus(C) eq M0`genus:
    "The curve model and modular-curve record have different genera.";

  // FIX: fail early when the hypotheses needed for a fine universal family
  // are not met.
  require GL2DeterminantIndex(M0`G) eq 1:
    "The subgroup must have full determinant.";
  require not GL2ContainsNegativeOne(M0`G):
    "The subgroup must not contain -I.";

  QC := FunctionField(C);
  // FIX: the original routine named only the ambient fraction field.  The
  // corrected routine returns coefficients in QC, so QC itself must be named
  // to avoid Magma printing its generators as $.1, $.2, and so on.  Since
  // PairToFunctionField dehomogenizes the last projective coordinate, QC.i
  // corresponds to coordinate_names[i] for i=1,...,rank-1.
  AssignNames(~QC,[ coordinate_names[i] : i in [1..rank-1] ]);
  jfunc := PairToFunctionField(jnum,jden,C,QC,polyring);
  hfunc := PairToFunctionField(hnum,hden,C,QC,polyring);
  require jfunc ne 0 and jfunc ne 1728 and hfunc ne 0:
    "The j-map or ratio degenerates in the function field of the curve.";

  Ffield := FieldOfFractions(polyring);
  AssignNames(~Ffield,coordinate_names);
  j := (Ffield!jnum)/(Ffield!jden);
  h := (Ffield!hnum)/(Ffield!hden);
  require j ne 0 and j ne 1728 and h ne 0:
    "The generic j-map/ratio is degenerate.";

  // FIX: implement the Section 13 square class correctly.  With
  // delta=j*h, direct short-Weierstrass conversion gives r0=j*delta=j^2*h.
  // Since E_{s^2*r} is isomorphic to E_r, r=h is the smaller representative
  // of precisely the same square class (take s=j).
  r := h;
  lambda := 1-1728/j;
  A := -27*r^2*lambda;
  B := 54*r^3*lambda^2;

  E := LowDegreeDivisor(C : KnownDivisor:=BaseDivisor,
                            SearchBound:=PointSearchBound,
                            verbose:=verbose);
  require Degree(E) gt 0: "Divisor reduction needs positive degree.";
  if verbose then
    printf "Using a base divisor of degree %o.\n",Degree(E);
  end if;

  Anum, Aden, Bnum, Bden :=
    FirstReduction(polyring,C,E,A,B : verbose:=verbose);
  if verbose then
    printf "Reduced A = (%o)/(%o).\n",Anum,Aden;
    printf "Reduced B = (%o)/(%o).\n",Bnum,Bden;
  end if;

  a_inv := FinalReduction(C,M0`G,QC,polyring,
                          [Anum,Aden,Bnum,Bden] : verbose:=verbose);

  // FIX: compare with the supplied modular j-map in Q(C), not merely with an
  // ambient rational expression.
  Eout := EllipticCurve(a_inv);
  require jInvariant(Eout) eq jfunc:
    "The resulting elliptic curve does not have the supplied j-map.";

  if verbose then
    print a_inv;
  end if;
  return a_inv;
end intrinsic;
