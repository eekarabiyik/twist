
/*
//Load  this to run the code on all curves in LMFDB
ChangeDirectory("/homes/ek693/Main/FindingFamilies");
AttachSpec("../spec");
FAM:=LoadFamilies(["/homes/ek693/Main/UnivEllCurve/unelcurvestuff/allfamincludingfinestuffLATEST.dat"]);
load "/homes/ek693/Main/UnivEllCurve/univellcurvedatalmfdb/lmfdbdatafine.m";
curves:=make_data();
*/

//load "/homes/ek693/Main/FindingFamilies/TwistingCode/TwistingCode2.m";
//okay it can find the family no problem.

// Helper function
// Input: C::Crv, g::RngIntElt -> DivCrvElt
// Given a curve C of genus g, returns a divisor of low degree on C 
function LowDegreeDivisor(C, g)
  P1 := ProjectiveSpace(Rationals(),1);

  // The P^1 case
  E := 0;
  phi := 0;
  if (g eq 0) and (#DefiningEquations(C) eq 0) then
    E := Divisor(C![1,0]);
  end if;
  // The pointless conic case
  if (g eq 0) and (#DefiningEquations(C) gt 0) then
    E := -CanonicalDivisor(C);
  end if;

  if (g ge 1) then
    pts := PointSearch(C,100);
    if #pts gt 0 then
      E := Divisor(C!Eltseq(pts[1]));
    else
      if (g ge 1) then
        phi := map<C -> P1 | [C.1,C.2]>;
        D := Divisor(C,(P1![1,0])@@phi);
        supp := Support(D);
        E := Divisor(supp[1]);
      end if;  
    end if;
  end if;
  return E;
end function;

// Initial reduction of the coefficients A and B in V^2 = U^3 + A*U + B
function FirstReduction(polyring, C, E, r, x, A, B)
  QC := FunctionField(C);
  vals := [ QC.i : i in [1..Rank(polyring)-1]] cat [QC!1];
  rfunc := Evaluate(r,vals);
  xfunc := Evaluate(x,vals);
  rdiv := Divisor(rfunc);
  xdiv := Divisor(xfunc);
  printf "Decomposing divisors.\n";
  decomp1 := Decomposition(rdiv);
  decomp2 := Decomposition(xdiv+E);
  allsup := [ decomp1[i][1] : i in [1..#decomp1]];
  for i in [1..#decomp2] do
    if not (decomp2[i][1] in allsup) then
      Append(~allsup,decomp2[i][1]);
    end if;
  end for;
  // Valuation of A and B at all divisors in their support
  avals := [ 2*Valuation(rdiv,allsup[j])+Valuation(xdiv,allsup[j]) : j in [1..#allsup]];
  bvals := [ 3*Valuation(rdiv,allsup[j])+2*Valuation(xdiv,allsup[j]) : j in [1..#allsup]];
  // A divisor D to "take out". We want to remove 4D from A and 6D from B.
  changevals := [ Min(Round(avals[j]/4),Round(bvals[j]/6)) : j in [1..#allsup]];
  change := &+[ changevals[j]*allsup[j] : j in [1..#allsup]];

  Adeg := &+[ avals[j]*Degree(allsup[j]) : j in [1..#allsup] | avals[j] ge 0 ];
  Bdeg := &+[ bvals[j]*Degree(allsup[j]) : j in [1..#allsup] | bvals[j] ge 0 ];
  printf "Starting degree of A = %o, degree of B = %o.\n",Adeg,Bdeg;

  redD, rr, E, func := Reduction(change,E);
  // We have change = redD + r*E - div(func).
  // In this case, redD has degree 0 and the support of E is contained in allsup
  newavals := [ avals[j] - 4*Valuation(change,allsup[j]) + 4*Valuation(redD,allsup[j]) + 4*rr*Valuation(E,allsup[j]) : j in [1..#allsup]];
  newbvals := [ bvals[j] - 6*Valuation(change,allsup[j]) + 6*Valuation(redD,allsup[j]) + 6*rr*Valuation(E,allsup[j]) : j in [1..#allsup]];

  newAdeg := &+[ newavals[j]*Degree(allsup[j]) : j in [1..#allsup] | newavals[j] ge 0];
  newBdeg := &+[ newbvals[j]*Degree(allsup[j]) : j in [1..#allsup] | newbvals[j] ge 0];
  printf "Final degree of A = %o. Final degree of B = %o.\n",newAdeg,newBdeg;

  if (newAdeg gt Adeg) and (newBdeg gt Bdeg) then
    newA := -27*rfunc^2*xfunc;
    newB := 54*rfunc^3*xfunc^2;
  else
    newA := -27*rfunc^2*xfunc*func^4;
    newB := 54*rfunc^3*xfunc^2*func^6;
  end if;

  // Now, let's do the simplification at places of Q.

  numA0 := Coefficients(Numerator(newA));
  d := LCM([ Denominator(numA0[i]) : i in [1..#numA0]]);
  numA0 := [ Integers()!(d*numA0[i]) : i in [1..#numA0]];
  denomA0 := Coefficients(Denominator(newA));
  d := LCM([ Denominator(denomA0[i]) : i in [1..#denomA0]]);
  denomA0 := [ Integers()!(d*denomA0[i]) : i in [1..#denomA0]];
  numA := GCD(numA0);
  denomA := GCD(denomA0);

  numB0 := Coefficients(Numerator(newB));
  d := LCM([ Denominator(numB0[i]) : i in [1..#numB0]]);
  numB0 := [ Integers()!(d*numB0[i]) : i in [1..#numB0]];
  denomB0 := Coefficients(Denominator(newB));
  d := LCM([ Denominator(denomB0[i]) : i in [1..#denomB0]]);
  denomB0 := [ Integers()!(d*denomB0[i]) : i in [1..#denomB0]];
  numB := GCD(numB0);
  denomB := GCD(denomB0);

  pf1 := PrimeFactors(numA);
  pf2 := PrimeFactors(denomA);
  pf3 := PrimeFactors(numB);
  pf4 := PrimeFactors(denomB);
  allprimes := pf1;
  for j in [1..#pf2] do
    if not pf2[j] in allprimes then
      Append(~allprimes,pf2[j]);
    end if;
  end for;
  for j in [1..#pf3] do
    if not pf3[j] in allprimes then
      Append(~allprimes,pf3[j]);
    end if;
  end for;
  for j in [1..#pf4] do
    if not pf4[j] in allprimes then
      Append(~allprimes,pf4[j]);
    end if;
  end for;
  change := [ Min(Round(Valuation(numA/denomA,allprimes[j])/4),Round(Valuation(numB/denomB,allprimes[j])/6)) : j in [1..#allprimes]];
  changemult := &*[ allprimes[j]^change[j] : j in [1..#allprimes]];
  newA := newA/changemult^4;
  newB := newB/changemult^6;

  // Reparse newA and newB to be ratios of elements in the polynomial ring. 

  newA2num0 := Evaluate(Numerator(newA),[polyring.i : i in [1..Rank(polyring)-1]]);
  cofs1, mons1 := CoefficientsAndMonomials(newA2num0);
  degnum := Max([ Degree(mons1[i]) : i in [1..#mons1]]);
  newA2denom0 := Evaluate(Denominator(newA),[polyring.i : i in [1..Rank(polyring)-1]]);
  cofs2, mons2 := CoefficientsAndMonomials(newA2denom0);
  degdenom := Max([ Degree(mons2[i]) : i in [1..#mons2]]);
  deg := Max(degnum,degdenom);
  newA2num := &+[ cofs1[i]*mons1[i]*(polyring.Rank(polyring))^(deg-Degree(mons1[i])) : i in [1..#mons1]];
  newA2denom := &+[ cofs2[i]*mons2[i]*(polyring.Rank(polyring))^(deg-Degree(mons2[i])) : i in [1..#mons2]];

  newB2num0 := Evaluate(Numerator(newB),[polyring.i : i in [1..Rank(polyring)-1]]);
  cofs1, mons1 := CoefficientsAndMonomials(newB2num0);
  degnum := Max([ Degree(mons1[i]) : i in [1..#mons1]]);
  newB2denom0 := Evaluate(Denominator(newB),[polyring.i : i in [1..Rank(polyring)-1]]);
  cofs2, mons2 := CoefficientsAndMonomials(newB2denom0);
  degdenom := Max([ Degree(mons2[i]) : i in [1..#mons2]]);
  deg := Max(degnum,degdenom);
  newB2num := &+[ cofs1[i]*mons1[i]*(polyring.Rank(polyring))^(deg-Degree(mons1[i])) : i in [1..#mons1]];
  newB2denom := &+[ cofs2[i]*mons2[i]*(polyring.Rank(polyring))^(deg-Degree(mons2[i])) : i in [1..#mons2]];

  return newA2num, newA2denom, newB2num, newB2denom; 
end function;

// The function below takes as input a group and outputs the maximal N for which the universal elliptic curve
// has a point of order N. 
function torsionorder(GG)
  N0 := Characteristic(BaseRing(GG));
  maxtors := 1;
  for d in Divisors(N0) do
    if (d gt maxtors) then
      torsdeg := GL2TorsionDegree(sub<GL(2,Integers(d)) | [ Transpose(t) : t in Generators(GG)]>);
      if torsdeg eq 1 then
        maxtors := d;
      end if;
    end if;
  end for;
  return maxtors;
end function;

// The function below takes as input a curve C, its function field QC, the polynomial ring used for the curve C, 
// elements A and B in QC, and an d >= 3.  It finds points of order d on V^2 = U^3 + A*U + B
// and puts the curve into the form V^2 + a1 UV + a3 V = U^3 + a2 U^2.
// The function below handles the case that d = 2.
function KTform(C,QC,polyring,A,B,d)
  // First, tweak our QC if C is P^1. This fixes a Magma bug, which should be fixed in V2.28-8.
  Ffieldpoly := 0;
  if #DefiningEquations(C) eq 0 then
    P1case := true;
    newQC := FunctionField(Rationals());
    Ffieldpoly := FunctionField(newQC);
  else
    P1case := false;
    Ffieldpoly := FunctionField(QC);
  end if;  
  if P1case then
    Afunc := Evaluate(Numerator(A),[newQC.1,1])/Evaluate(Denominator(A),[newQC.1,1]);
    Bfunc := Evaluate(Numerator(B),[newQC.1,1])/Evaluate(Denominator(B),[newQC.1,1]);
  else
    vals := [ QC.i : i in [1..Rank(polyring)-1]] cat [QC!1];    
    Afunc := Evaluate(Numerator(A),vals)/Evaluate(Denominator(A),vals);
    Bfunc := Evaluate(Numerator(B),vals)/Evaluate(Denominator(B),vals);
  end if;
  rawE := EllipticCurve([0,0,0,Afunc,Bfunc]);
  divpol0 := &*[ Evaluate(DivisionPolynomial(rawE,e),Ffieldpoly.1)^(MoebiusMu(Integers()!(d/e))) : e in Divisors(d)];
  divpol := Numerator(divpol0);
  // The roots of divpol are x-coordinates of points of exact order d.
  printf "Finding roots of division polynomial.\n";
  rts := Roots(divpol);
  printf "Done.\n";
  pts := [];
  for j in [1..#rts] do
    chk, P := IsPoint(rawE,rts[j][1]);
    if chk then
      if P[2] ne 0 then
        Append(~pts,-P);
      end if;
    end if;
  end for;
  rets := [];
  for k in [1..#pts] do
    printf "Trying point %o of %o.\n",k,#pts;
    x0 := pts[k][1];
    y0 := pts[k][2];
    if P1case then
      x0 := Evaluate(x0,QC.1);
      y0 := Evaluate(y0,QC.1);
    end if;
    alist := aInvariants(rawE);
    K<x,y> := PolynomialRing(QC,2);
    if P1case then
      alist := [ Evaluate(alist[i],QC.1) : i in [1..#alist]];
    end if;
    pol := y^2 + alist[1]*x*y + alist[3]*y - (x^3 + alist[2]*x^2 + alist[4]*x + alist[5]);
    // Step 1 - Move (x0,y0) to the origin.
    pol2 := Evaluate(pol,[x+x0,y+y0]);
    // Step 2 - Rotate so tangent line is horizontal. This step will crash if (x0,y0) has order 2.
    newalist := [ MonomialCoefficient(pol2,x*y), -MonomialCoefficient(pol2,x^2), MonomialCoefficient(pol2,y), -MonomialCoefficient(pol2,x), 0];
    s := newalist[4]/newalist[3];
    pol3 := Evaluate(pol2,[x,y+s*x]);
    a1 := MonomialCoefficient(pol3,x*y);
    a2 := -MonomialCoefficient(pol3,x^2);
    a3 := MonomialCoefficient(pol3,y);
    
    // Post-processing
    allprimes := [];
    if (a1 ne 0) then
      newa1num0 := Evaluate(Numerator(a1),[polyring.i : i in [1..Rank(polyring)-1]]);
      cofs1, mons1 := CoefficientsAndMonomials(newa1num0);
      degnum := Max([ Degree(mons1[i]) : i in [1..#mons1]]);
      newa1denom0 := Evaluate(Denominator(a1),[polyring.i : i in [1..Rank(polyring)-1]]);
      cofs2, mons2 := CoefficientsAndMonomials(newa1denom0);
      degdenom := Max([ Degree(mons2[i]) : i in [1..#mons2]]);
      deg := Max(degnum,degdenom);
      newa1num := &+[ cofs1[i]*mons1[i]*(polyring.Rank(polyring))^(deg-Degree(mons1[i])) : i in [1..#mons1]];
      newa1denom := &+[ cofs2[i]*mons2[i]*(polyring.Rank(polyring))^(deg-Degree(mons2[i])) : i in [1..#mons2]];
      numa1 := Coefficients(newa1num);
      d := LCM([ Denominator(numa1[i]) : i in [1..#numa1]]);
      numa1 := [ Integers()!(d*numa1[i]) : i in [1..#numa1]];
      denoma1 := Coefficients(newa1denom);
      d := LCM([ Denominator(denoma1[i]) : i in [1..#denoma1]]);
      denoma1 := [ Integers()!(d*denoma1[i]) : i in [1..#denoma1]];
      numa1 := GCD(numa1);
      denoma1 := GCD(denoma1);
      allprimes := PrimeFactors(numa1*denoma1);
    else
      newa1num := polyring!0;
      newa1denom := polyring!1;
      numa1 := 0;
      denoma1 := 0;
    end if;
    if (a2 ne 0) then
      newa2num0 := Evaluate(Numerator(a2),[polyring.i : i in [1..Rank(polyring)-1]]);
      cofs1, mons1 := CoefficientsAndMonomials(newa2num0);
      degnum := Max([ Degree(mons1[i]) : i in [1..#mons1]]);
      newa2denom0 := Evaluate(Denominator(a2),[polyring.i : i in [1..Rank(polyring)-1]]);
      cofs2, mons2 := CoefficientsAndMonomials(newa2denom0);
      degdenom := Max([ Degree(mons2[i]) : i in [1..#mons2]]);
      deg := Max(degnum,degdenom);
      newa2num := &+[ cofs1[i]*mons1[i]*(polyring.Rank(polyring))^(deg-Degree(mons1[i])) : i in [1..#mons1]];
      newa2denom := &+[ cofs2[i]*mons2[i]*(polyring.Rank(polyring))^(deg-Degree(mons2[i])) : i in [1..#mons2]];
      numa2 := Coefficients(newa2num);
      d := LCM([ Denominator(numa2[i]) : i in [1..#numa2]]);
      numa2 := [ Integers()!(d*numa2[i]) : i in [1..#numa2]];
      denoma2 := Coefficients(newa2denom);
      d := LCM([ Denominator(denoma2[i]) : i in [1..#denoma2]]);
      denoma2 := [ Integers()!(d*denoma2[i]) : i in [1..#denoma2]];
      numa2 := GCD(numa2);
      denoma2 := GCD(denoma2);
      if #allprimes eq 0 then
        allprimes := PrimeFactors(numa2*denoma2);
      else
        for p in PrimeFactors(numa2) do
          if not (p in allprimes) then
            Append(~allprimes,p);
          end if;
        end for;
        for p in PrimeFactors(denoma2) do
          if not (p in allprimes) then
            Append(~allprimes,p);
          end if;
        end for;
      end if;
    else
      newa2num := polyring!0;
      newa2denom := polyring!1;
      numa2 := 0;
      denoma2 := 0;
    end if;    
    if (a3 ne 0) then
      newa3num0 := Evaluate(Numerator(a3),[polyring.i : i in [1..Rank(polyring)-1]]);
      cofs1, mons1 := CoefficientsAndMonomials(newa3num0);
      degnum := Max([ Degree(mons1[i]) : i in [1..#mons1]]);
      newa3denom0 := Evaluate(Denominator(a3),[polyring.i : i in [1..Rank(polyring)-1]]);
      cofs2, mons2 := CoefficientsAndMonomials(newa3denom0);
      degdenom := Max([ Degree(mons2[i]) : i in [1..#mons2]]);
      deg := Max(degnum,degdenom);
      newa3num := &+[ cofs1[i]*mons1[i]*(polyring.Rank(polyring))^(deg-Degree(mons1[i])) : i in [1..#mons1]];
      newa3denom := &+[ cofs2[i]*mons2[i]*(polyring.Rank(polyring))^(deg-Degree(mons2[i])) : i in [1..#mons2]];
      numa3 := Coefficients(newa3num);
      d := LCM([ Denominator(numa3[i]) : i in [1..#numa3]]);
      numa3 := [ Integers()!(d*numa3[i]) : i in [1..#numa3]];
      denoma3 := Coefficients(newa3denom);
      d := LCM([ Denominator(denoma3[i]) : i in [1..#denoma3]]);
      denoma3 := [ Integers()!(d*denoma3[i]) : i in [1..#denoma3]];
      numa3 := GCD(numa3);
      denoma3 := GCD(denoma3);
      if #allprimes eq 0 then
        allprimes := PrimeFactors(numa3*denoma3);
      else
        for p in PrimeFactors(numa3) do
          if not (p in allprimes) then
            Append(~allprimes,p);
          end if;
        end for;
        for p in PrimeFactors(denoma3) do
          if not (p in allprimes) then
            Append(~allprimes,p);
          end if;
        end for;
      end if;
    else
      newa3num := polyring!0;
      newa3denom := polyring!1;
      numa3 := 0;
      denoma3 := 0;
    end if;
    nums := [numa1,numa2,numa3];
    denoms := [denoma1,denoma2,denoma3];
    //printf "nums = %o, denoms = %o.\n",nums,denoms;
    change := [ Min([ Round(Valuation(nums[i]/denoms[i],allprimes[j])/i) : i in [1..3] | nums[i] ne 0]) : j in [1..#allprimes]];
    changemult := &*[ allprimes[j]^change[j] : j in [1..#allprimes]];
    nm := Numerator(1/changemult);
    dm := Denominator(1/changemult);
    newa1num := newa1num/dm;
    newa2num := newa2num/dm^2;
    newa3num := newa3num/dm^3;
    newa1denom := newa1denom*nm;
    newa2denom := newa2denom*nm^2;
    newa3denom := newa3denom*nm^3;
    Append(~rets,[newa1num,newa1denom,newa2num,newa2denom,newa3num,newa3denom]);
  end for;
  lengths := [ #Sprintf("%o",rets[i]) : i in [1..#rets]];
  min, bestind := Min(lengths);
  return rets[bestind];
end function;

// The function below takes a universal elliptic curve in short Weierstrass form
// V^2 = U^3 + A*U + B and writes it in the form V^2 = U^3 + a*U^2 + b*U
function KTform2(C,QC,polyring,A,B)
  // First, tweak our QC if C is P^1. This fixes a Magma bug, which should be fixed in V2.28-8.
  Ffieldpoly := 0;
  if #DefiningEquations(C) eq 0 then
    P1case := true;
    newQC := FunctionField(Rationals());
    Ffieldpoly := FunctionField(newQC);
  else
    P1case := false;
    Ffieldpoly := FunctionField(QC);
  end if;  
  if P1case then
    Afunc := Evaluate(Numerator(A),[newQC.1,1])/Evaluate(Denominator(A),[newQC.1,1]);
    Bfunc := Evaluate(Numerator(B),[newQC.1,1])/Evaluate(Denominator(B),[newQC.1,1]);
  else
    vals := [ QC.i : i in [1..Rank(polyring)-1]] cat [QC!1];    
    Afunc := Evaluate(Numerator(A),vals)/Evaluate(Denominator(A),vals);
    Bfunc := Evaluate(Numerator(B),vals)/Evaluate(Denominator(B),vals);
  end if;
  rawE := EllipticCurve([0,0,0,Afunc,Bfunc]);
  divpol := DivisionPolynomial(rawE,2);
  // The roots of divpol are x-coordinates of points of exact order d.
  printf "Finding roots of division polynomial.\n";
  rts := Roots(divpol);
  printf "Done. There were %o.\n",#rts;
  pts := [];
  for j in [1..#rts] do
    chk, P := IsPoint(rawE,rts[j][1]);
    if chk then
      Append(~pts,P);
    end if;
  end for;
  rets := [];
  assert #pts ge 1;
  for k in [1..#pts] do
    //printf "Trying point %o of %o.\n",k,#pts;
    x0 := pts[k][1];
    y0 := pts[k][2];
    if P1case then
      x0 := Evaluate(x0,QC.1);
      y0 := Evaluate(y0,QC.1);
    end if;
    alist := aInvariants(rawE);
    K<x,y> := PolynomialRing(QC,2);
    if P1case then
      alist := [ Evaluate(alist[i],QC.1) : i in [1..#alist]];
    end if;
    pol := y^2 + alist[1]*x*y + alist[3]*y - (x^3 + alist[2]*x^2 + alist[4]*x + alist[5]);
    // Step 1 - Move (x0,y0) to the origin.
    pol2 := Evaluate(pol,[x+x0,y+y0]);
    a2 := -MonomialCoefficient(pol2,x^2);
    a4 := -MonomialCoefficient(pol2,x);
    
    // Post-processing
    allprimes := [];
    if (a2 ne 0) then
      newa2num0 := Evaluate(Numerator(a2),[polyring.i : i in [1..Rank(polyring)-1]]);
      cofs1, mons1 := CoefficientsAndMonomials(newa2num0);
      degnum := Max([ Degree(mons1[i]) : i in [1..#mons1]]);
      newa2denom0 := Evaluate(Denominator(a2),[polyring.i : i in [1..Rank(polyring)-1]]);
      cofs2, mons2 := CoefficientsAndMonomials(newa2denom0);
      degdenom := Max([ Degree(mons2[i]) : i in [1..#mons2]]);
      deg := Max(degnum,degdenom);
      newa2num := &+[ cofs1[i]*mons1[i]*(polyring.Rank(polyring))^(deg-Degree(mons1[i])) : i in [1..#mons1]];
      newa2denom := &+[ cofs2[i]*mons2[i]*(polyring.Rank(polyring))^(deg-Degree(mons2[i])) : i in [1..#mons2]];
      numa2 := Coefficients(newa2num);
      d := LCM([ Denominator(numa2[i]) : i in [1..#numa2]]);
      numa2 := [ Integers()!(d*numa2[i]) : i in [1..#numa2]];
      denoma2 := Coefficients(newa2denom);
      d := LCM([ Denominator(denoma2[i]) : i in [1..#denoma2]]);
      denoma2 := [ Integers()!(d*denoma2[i]) : i in [1..#denoma2]];
      numa2 := GCD(numa2);
      denoma2 := GCD(denoma2);
      if #allprimes eq 0 then
        allprimes := PrimeFactors(numa2*denoma2);
      else
        for p in PrimeFactors(numa2) do
          if not (p in allprimes) then
            Append(~allprimes,p);
          end if;
        end for;
        for p in PrimeFactors(denoma2) do
          if not (p in allprimes) then
            Append(~allprimes,p);
          end if;
        end for;
      end if;
    else
      newa2num := polyring!0;
      newa2denom := polyring!1;
      numa2 := 0;
      denoma2 := 0;
    end if;    
    if (a4 ne 0) then
      newa4num0 := Evaluate(Numerator(a4),[polyring.i : i in [1..Rank(polyring)-1]]);
      cofs1, mons1 := CoefficientsAndMonomials(newa4num0);
      degnum := Max([ Degree(mons1[i]) : i in [1..#mons1]]);
      newa4denom0 := Evaluate(Denominator(a4),[polyring.i : i in [1..Rank(polyring)-1]]);
      cofs2, mons2 := CoefficientsAndMonomials(newa4denom0);
      degdenom := Max([ Degree(mons2[i]) : i in [1..#mons2]]);
      deg := Max(degnum,degdenom);
      newa4num := &+[ cofs1[i]*mons1[i]*(polyring.Rank(polyring))^(deg-Degree(mons1[i])) : i in [1..#mons1]];
      newa4denom := &+[ cofs2[i]*mons2[i]*(polyring.Rank(polyring))^(deg-Degree(mons2[i])) : i in [1..#mons2]];
      numa4 := Coefficients(newa4num);
      d := LCM([ Denominator(numa4[i]) : i in [1..#numa4]]);
      numa4 := [ Integers()!(d*numa4[i]) : i in [1..#numa4]];
      denoma4 := Coefficients(newa4denom);
      d := LCM([ Denominator(denoma4[i]) : i in [1..#denoma4]]);
      denoma4 := [ Integers()!(d*denoma4[i]) : i in [1..#denoma4]];
      numa4 := GCD(numa4);
      denoma4 := GCD(denoma4);
      if #allprimes eq 0 then
        allprimes := PrimeFactors(numa4*denoma4);
      else
        for p in PrimeFactors(numa4) do
          if not (p in allprimes) then
            Append(~allprimes,p);
          end if;
        end for;
        for p in PrimeFactors(denoma4) do
          if not (p in allprimes) then
            Append(~allprimes,p);
          end if;
        end for;
      end if;
    else
      newa4num := polyring!0;
      newa4denom := polyring!1;
      numa4 := 0;
      denoma4 := 0;
    end if;
    nums := [numa2,numa4];
    denoms := [denoma2,denoma4];
    //printf "nums = %o, denoms = %o.\n",nums,denoms;
    if #allprimes eq 0 then
      changemult := 1;
    else
      change := [ Min([ Round(Valuation(nums[i]/denoms[i],allprimes[j])/i) : i in [1..2] | nums[i] ne 0]) : j in [1..#allprimes]];
      changemult := &*[ allprimes[j]^change[j] : j in [1..#allprimes]];
    end if;  
    nm := Numerator(1/changemult);
    dm := Denominator(1/changemult);
    newa2num := newa2num/dm^2;
    newa4num := newa4num/dm^4;
    newa2denom := newa2denom*nm^2;
    newa4denom := newa4denom*nm^4;
    //printf "Final a2 = %o/%o, final a4 = %o/%o.\n",newa2num,newa2denom,newa4num,newa4denom;
    Append(~rets,[newa2num,newa2denom,newa4num,newa4denom]);
  end for;
  lengths := [ #Sprintf("%o",rets[i]) : i in [1..#rets]];
  min, bestind := Min(lengths);
  return rets[bestind];
end function;

function FinalReduction(C,H0,QC,polyring,newA2num,newA2denom,newB2num,newB2denom)
  Ffield := FieldOfFractions(polyring);
  varsnames := ["x","y","z","w","t","u","v","r","s","a","b","c","d","e","f","g","h","i","k","l","m","n","o","p","q","j"];
  AssignNames(~Ffield,[varsnames[j] : j in [1..Rank(polyring)]]);
  d := torsionorder(H0);
  a_inv := [];
  if d eq 1 then
    a_inv := [newA2num,newA2denom,newB2num,newB2denom];
    printf "We're done.\n";
  end if;
  if d eq 2 then
    lst := KTform2(C,QC,polyring,newA2num/newA2denom,newB2num/newB2denom);
    a_inv := [0, Ffield!(lst[1]/lst[2]), 0, Ffield!(lst[3]/lst[4]), 0];
    printf "Final model is a2 = (%o)/(%o), a4 = (%o)/(%o).\n",lst[1],lst[2],lst[3],lst[4];
  end if;
  if d ge 3 then
    use := Min([ e : e in Divisors(d) | e ge 3]);
    lst := KTform(C,QC,polyring,newA2num/newA2denom,newB2num/newB2denom,use);
    a_inv := [Ffield!(lst[1]/lst[2]), Ffield!(lst[3]/lst[4]), Ffield!(lst[5]/lst[6]), 0];
    printf "Final model is a1 = (%o)/(%o), a2 = (%o)/(%o), a3 = (%o)/(%o).\n",lst[1],lst[2],lst[3],lst[4],lst[5],lst[6];
  end if;

  return a_inv;
end function;

/* 
Inputs: 
* "M0" -- Rec, modular curve record for a subgroup of GL2(Z/NZ) not containing -I
* "model" -- Crv 
* "j" -- SeqEnum, [jnum, jdenom]
* "f" -- SeqEnum, weight 3 form in M_3(G) expressed as [fnum, fdenom]
*/
function FindUnivECModel(M0, model, j_map, f: verbose:=false)
        jnum := j_map[1]; jdenom := j_map[2];
        fnum := f[1]; fdenom := f[2];
        polyring := PolynomialRing(Rationals(), M0`genus, "grevlex");
        varsnames := ["x","y","z","w","t","u","v","r","s","a","b","c","d","e","f","g","h","i","k","l","m","n","o","p","q","j"];
        AssignNames(~polyring,[varsnames[j] : j in [1..M0`genus]]);
        Ffield := FieldOfFractions(polyring);
        j := (Ffield!(jnum/jdenom));
        r := (Ffield!(fnum/fdenom));
        x := 1 - 1728/j;
        A := -27*r^2*x;
        B := 54*r^3*x^2;

        // doing initial reduction
        C := model;
        QC := FunctionField(C);
        E := LowDegreeDivisor(C, M0`genus);
        if verbose then printf "Using effective divisor of degree %o", Degree(E); end if;
        newA2num, newA2denom, newB2num, newB2denom := FirstReduction(polyring, C, E, r, x, A, B);

        if verbose then 
                printf "Numerator of A = %o.\n",newA2num;
                printf "Denominator of A = %o.\n",newA2denom;
                printf "Numerator of B = %o.\n",newB2num;
                printf "Denominator of B = %o.\n",newB2denom;

                printf "Starting A size = %o. Ending A size = %o.\n",#Sprintf("%o",A),#Sprintf("%o",newA2num/newA2denom);
                printf "Starting B size = %o. Ending B size = %o.\n",#Sprintf("%o",B),#Sprintf("%o",newB2num/newB2denom);
        end if;

        a_inv := FinalReduction(C,M0`G,QC,polyring,newA2num,newA2denom,newB2num,newB2denom);
        if verbose then print(a_inv); end if;
        return a_inv;

end function;

/*
for k in Keys(curves) do
//if k in [190000..200000] then continue; end if;
G:=curves[k]`subgroup;
M0 := CreateModularCurveRec(G);
H := GL2IncludeNegativeOne(G);
TY := SL2Intersection(H);
famkey,_,H := FamilyFinder(H, TY, FAM);
M := CreateModularCurveRec(H);
M := FindModelOfXG(M : G0:=FAM[famkey]`calG);
C, jmap, _, _, _, _, _ := AbsoluteJmap(M);
// Jmap or AbsoluteJmap

if #BaseRing(G) eq Infinity() then continue; end if;
//if GL2Index(G) eq GL2Index(GL2AgreeableClosure(G)) then continue; end if;
       
        print(k);
        time0:=Realtime();
        
        
        if GL2Order(G) eq 1 then continue; end if;
        if assigned G`SL then delete G`SL; end if;
        T:=SL2Intersection(G);
        //famkey,famG,Gcong,calGlift,Tcong:=FamilyFinderFine(G,T,FAM);
        //famkey;
        //print(famkey);
        //AgreeableClosure(G);
        //GL2Level(AgreeableClosure(G));
        //GL2Level(GL2AgreeableClosure(G));
        //GL2AgreeableClosure(G);xx
        //time1:=Realtime();
        //H1:=AgreeableClosure(G);
        //print(Realtime(time1));
        //time2:=Realtime();
        //H2:=GL2AgreeableClosure(G);
        //print(Realtime(time2));
        //assert GL2Project(AgreeableClosure(G),GL2Level(AgreeableClosure(G))) eq GL2Project(GL2AgreeableClosure(G),GL2Level(GL2AgreeableClosure(G)));
        FF:=Weight3Twister(G,T,FAM: redcub:=true);
        print(FF);
        //print(jmap);
        //print(gon_2);
        print(Realtime(time0));
        
end for;
*/ 