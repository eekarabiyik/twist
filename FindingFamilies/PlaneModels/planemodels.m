intrinsic IdentifyAffinePatch(KC::FldFunFracSch) -> Any
  {Return the index of the variable used to create affine patch, i.e., the one used as a denominator}
  dens := [Denominator(ProjectiveRationalFunction(KC.i)) : i in [1..Rank(KC)]];
  R := Parent(dens[1]);
  proj_vars := GeneratorsSequence(R);
  ds := [el : el in dens | el in proj_vars];
  assert #Seqset(ds) eq 1; // should all have same denominator, if it's one of the variables
  return Index(proj_vars,ds[1]);
end intrinsic;

intrinsic MakeAffineVariableList(KC::FldFunFracSch, ind::RngIntElt) -> Any
  {}
  return [KC.i : i in [1..(ind-1)]] cat [KC!1] cat [KC.i : i in [ind..Rank(KC)]];
end intrinsic;

intrinsic RationalFunctionToFunctionFieldElement(C::Crv, j::FldFunRatMElt) -> Any
  {Convert FldFunRatMElt to FldFunFracSchElt}
  KC := FunctionField(C);
  ind := IdentifyAffinePatch(KC);
  j_Cs := [];
  for f in [Numerator(j), Denominator(j)] do
    f_C := Evaluate(f, MakeAffineVariableList(KC,ind));
    Append(~j_Cs,f_C);
  end for;
  return j_Cs[1]/j_Cs[2];
end intrinsic;

intrinsic JMapSanityCheck(j::FldFunFracSchElt) -> BoolElt
  {Make sure that the j-map is only ramified above 0, 1728, oo}

  pts, mults := Support(Divisor(Differential(j)));
  for el in pts do
    val := j(RepresentativePoint(el));
    if not ((val eq 0) or (val eq 1728) or (val eq Infinity())) then
      return false;
    end if;
  end for;
  return true;
end intrinsic;

intrinsic DegreeLowerBound(g::RngIntElt) -> RngIntElt
  {A lower bound for the degree of the plane model for a curve of genus g}
  assert g ge 0;
  if g eq 0 then
    return 1;
  elif g eq 1 then
    return 3;
  else
    return Ceiling((3+Sqrt(1+8*g)/2));
  end if;
end intrinsic;

intrinsic DegreeUpperBound(g::RngIntElt) -> RngIntElt
  {A upper bound for the degree of the plane model for a curve of genus g, embedded using}
  assert g ge 4;
  return 4*(g-1)-3;
end intrinsic;


// Several methods for checking whether the projection onto the plane curve is birational.
// It is possible that some of these methods might claim that a projection is invalid when
// it is actually valid (if we hit some bad points), but the claim that a projection is
// valid does not rely on avoiding bad points.
reduction_prime := 997; // should be larger than the level

intrinsic HasIndeterminacy(Igens::SeqEnum, lin_forms::SeqEnum) -> BoolElt
{Checks whether there is a common zero locus for the linear forms defining the projection.}
    I := Ideal(Igens cat lin_forms);
    return not IsProper(I);
end intrinsic;

// These two methods were slower approaches for checking whether a plane model was valid

intrinsic ValidPlaneModel(f::RngMPolElt, g::RngIntElt) -> BoolElt
{A quick check for whether the plane curve defined by f is a valid reduction}
    p := reduction_prime;
    fbar := ChangeRing(f, GF(p));
    return IsIrreducible(fbar) and Genus(Curve(Proj(Parent(f)), f)) eq g;
end intrinsic;
/*
intrinsic ValidPlaneModel2(f::RngMPolElt, X::Crv, proj::ModMatRngElt) -> BoolElt
{A quick check for whether the plane curve defined by f is a valid reduction}
    p := reduction_prime;
    fbar := ChangeRing(f, GF(p));
    if not IsIrreducible(fbar) then return false; end if;
    C := Curve(Proj(Parent(f)), f);
    R := Parent(DefiningEquations(X)[1]);
    Rgens := [R.i : i in [1..NumberOfGenerators(R)]];
    coords := [&+[Rgens[i] * proj[j,i] : i in [1..#Rgens]] : j in [1..3]];
    pi := map<X -> C | coords>;
    return Degree(pi) eq 1;
end intrinsic;
*/

intrinsic ValidModel(proj::MapSch : num_tests:=3, show_reason:=false) -> BoolElt
{
Input:
    proj - a map between irreducible curves
Output:
    whether proj is birational.  Can return a false negative with low probability but shouldn't return false positives
}
    p := reduction_prime;
    X := Domain(proj);
    C := Codomain(proj);
    Xbar := ChangeRing(X, GF(p));
    Cbar := ChangeRing(C, GF(p));
    if not IsIrreducible(Cbar) then
        if show_reason or GetVerbose("User1") gt 0 then
            print "Invalid model: reducible";
        end if;
        return false;
    end if;
    Igens := DefiningEquations(X);
    R := ChangeRing(Universe(Igens), GF(p));
    Igens := [R!g : g in Igens];
    coords := [R!g : g in DefiningEquations(proj)];
    if HasIndeterminacy(Igens, coords) then
        if show_reason or GetVerbose("User1") gt 0 then
            print "Invalid model: indeterminacy";
        end if;
        return false;
    end if;
    for run in [1..num_tests] do
        P := Random(Cbar(GF(p)));
        I := Ideal(Igens cat [coords[j] - P[j] : j in [1..#coords]]);
        if QuotientDimension(I) ne 1 then
            if show_reason or GetVerbose("User1") gt 0 then
                print Sprintf("Invalid model: %o mod-%o preimages", QuotientDimension(I), p);
            end if;
            continue;
        end if;
        return true;
    end for;
    return false;
end intrinsic;

intrinsic F0Combination(F0::SeqEnum, M::ModMatRngElt) -> SeqEnum //ERAY: this one should be useful for me as well.
{F0 is as in ModularCurveRec, M is a 3 by n matrix over the integers with full rank, where n is the length of F0.
Applies the matrix M to the expansions, projecting F0 onto 3 modular forms (given by expansions at cusps as normal)}
    // I can't get matrix vector multiplication working reasonably, so we do this by hand
    //vecs := [Vector([F0[i][j] : i in [1..#F0]]) : j in [1..#F0[1]]];
    //vec3s := [v * Transpose(M) : v in vecs];
    //return [[vec3s[i][j] : i in [1..#vec3s]] : j in [1..3]];
    ans := [[Parent(F0[1][1])!0 : a in [1..#F0[1]]] : j in [1..3]];
    for a in [1..#F0[1]] do
        for j in [1..3] do
            for i in [1..#F0] do
                ans[j][a] +:= M[j][i] * F0[i][a];
            end for;
        end for;
    end for;
    return ans;
end intrinsic;

ProjectorRec := recformat<n, poss_pivots, cur_idx_pivots, max_idx_pivots, nonpiv_vecmax, nonpiv_ctr>;

intrinsic InitProjectorRec(n::RngIntElt) -> Rec
{INPUT: n >= 4,
Initializes the state object for iterating over certain full-rank 3xn matrices}
    poss_pivots := [Reverse(x) : x in Sort([Reverse(SetToSequence(pivs)) : pivs in Subsets({1..n}, 3)])];
    return rec<ProjectorRec | n:=n, poss_pivots:=poss_pivots, cur_idx_pivots:=1, max_idx_pivots:=2, nonpiv_vecmax:=[0 : _ in [1..#poss_pivots]], nonpiv_ctr:=[0 : _ in [1..#poss_pivots]]>;
end intrinsic;

intrinsic NextProjector(~state::Rec, ~M::ModMatRngElt)
{Updates M to be the next projector matrix, as iterated through by the state object}
    pividx := state`cur_idx_pivots;
    pivots := state`poss_pivots[pividx];
    v := state`nonpiv_ctr[pividx];
    vmax := state`nonpiv_vecmax[pividx];
    if vmax eq 0 then
        nonpivs := [];
    else
        nonpivs := IntegerToSequence(v, 2*vmax + 1);
        for j in [1..#nonpivs] do
            if nonpivs[j] mod 2 eq 1 then
                nonpivs[j] := 1 + (nonpivs[j] div 2);
            else
                nonpivs[j] := -nonpivs[j] div 2;
            end if;
        end for;
    end if;
    nonpivs cat:= [0 : _ in [1..3*state`n - 9]];
    ML := [[0 : i in [1..state`n]] : j in [1..3]];
    for j in [1..3] do
        ML[j][pivots[j]] := 1;
    end for;
    npctr := 1;
    for i in [1..state`n] do
        if i in pivots then continue; end if;
        for j in [1..3] do
            ML[j][i] := nonpivs[npctr];
            npctr +:= 1;
        end for;
    end for;
    M := Matrix(ML);

    // Now we update the state
    if v eq (2*vmax+1)^(3*state`n - 9) - 1 then
        state`nonpiv_vecmax[pividx] +:= 1;
        state`nonpiv_ctr[pividx] := 2*state`nonpiv_vecmax[pividx] - 1;
    else
        repeat
            state`nonpiv_ctr[pividx] +:= 1;
        until Max(IntegerToSequence(state`nonpiv_ctr[pividx], 2*state`nonpiv_vecmax[pividx]+1)) ge 2*state`nonpiv_vecmax[pividx] - 1;
    end if;
    if pividx eq state`max_idx_pivots then
        if state`max_idx_pivots lt #state`poss_pivots then
            state`max_idx_pivots +:= 1;
        end if;
        state`cur_idx_pivots := 1;
    else
        state`cur_idx_pivots +:= 1;
    end if;
end intrinsic;

function planemodel_gonbound(f)
    fP := Parent(f);
    degrees := [Degree(f, fP.i): i in [1..Ngens(fP)]];
    return Min([d: d in degrees | d ne 0]);
end function;

intrinsic planemodel_sortkey(f::RngMPolElt) -> Tup
{}
    return <planemodel_gonbound(f), #sprint(f)>;
end intrinsic;


intrinsic PlaneModelFromQExpansions(rec::Rec, Can::Crv : prec:=0) -> BoolElt, Crv, SeqEnum
{rec should be of type ModularCurveRec, genus larger than 3 and not hyperelliptic}
    assert reduction_prime gt rec`N;
    
    if prec eq 0 then
        prec := rec`prec;
    end if;
    if not assigned rec`F0 then
        if not assigned rec`F then
            rec := FindModularForms(2,rec);
        end if;
        rec := FindCuspForms(rec);
    end if;

    g := rec`genus;
    low := DegreeLowerBound(g);
    high := DegreeUpperBound(g);
    rels := [];
    state := InitProjectorRec(g);
    M := ZeroMatrix(Integers(), 3, g);
    nvalid := 0;
    R<X,Y,Z> := PolynomialRing(Rationals(), 3);
    Rg := PolynomialRing(Rationals(), g); // variable names assigned in LMFDBWritePlaneModel
    CanEqs := DefiningEquations(Can);

    list:=[];
    repeat
        NextProjector(~state, ~M);
        MF := F0Combination(rec`F0, M);
        for m in [low..high] do
        t0:=Cputime();

            rels := FindRelationsOverKG(rec,MF, m);
        
            if #rels gt 0 then
                f := R!rels[1];
                proj := [&+[M[i,j] * Rg.j : j in [1..g]] : i in [1..3]];
                // Note that FindRelations is inexact: the modular forms may not actually satisfy the relations exactly, but instead only up to some precision which is lower than the precision of the forms themselves.  As a consequence, proj may not actually define a map from Can to the plane model.  This is checked in RecordPlaneModel.
                X:=CanEqs;
                // First check whether the model is valid (to catch bugs elsewhere)
                XC := Curve(Proj(Universe(X)), X);
                C := Curve(Proj(Parent(f)), f);

                try
                    projection := map<XC -> C | proj>;
                catch e
                      print e;
                end try;
                valid := ValidModel(projection);
                if not valid then
                    "invalid model";
                      
               
                else
                    nvalid:=nvalid+1;
                    list:=list cat [<f,proj>];
                end if;
                break;
            elif Cputime() - t0 gt 600 then
                break;
            end if;
        end for;
        // Since this is part of the process where we compute the canonical model (and we give that a long timeout), we don't want this to spin forever.
    until nvalid ge 25 or state`nonpiv_ctr[1] ge 728 or (nvalid gt 0 and Cputime() - t0 gt 60) or (Cputime() - t0 gt 600);
    //ReportEnd(label, "searching for plane models", t0);
    //ReportEnd(label, "plane model relations", trel : elapsed:=trel);
    //ReportEnd(label, "plane model validations", tval : elapsed:=tval);
    //ReportEnd(label, "plane model reductions", tred : elapsed:=tred);

    f, M := Explode(list[1]);
    C := Curve(Proj(Parent(f)), f);
    vprint User1: Sprintf("Plane model: %o model(s) found\n", nvalid);
    return true, list;
end intrinsic;




































/*


intrinsic RecordPlaneModel(fproj::Tup, X::SeqEnum, best::SeqEnum, bestkey::Tup, alg::MonStgElt, label::MonStgElt : warn_invalid:=true) -> SeqEnum, Tup, BoolElt, FldReElt, FldReElt
{
Input:
    fproj - a pair, with the first value a polynomial in X,Y,Z defining a plane curve, and the second a sequence of length 3 giving the projection map from the canonical model
    X - the sequence of defining equations for the canonical model (or some other smooth model in the hyperelliptic case)
    best - the current best option, as a sequence of length 0 or 1 of records like fproj
    bestkey - the value of planemodel_sortkey for the best option
    label - the label of the modular curve (for writing to disc)
    warn_invalid - whether a warning should be printed if the model is invalid
Output:
    best - the new best option, which may be fproj or the old best option
    bestkey - the value of planemodel_sortkey on the best option
    valid - whether fproj was a valid model
    time_val - time spent on model validation
    time_red - time spent on reducemodel_padic
File input:
    gonality bounds from LMFDBReadGonalityBounds
File output:
    If the model is better than the currently known model, writes to disc using LMFDBWritePlaneModel
    If gonality bounds are improved, writes new ones using LMFDBWriteGonalityBounds
}
    f, proj := Explode(fproj);
    // First check whether the model is valid (to catch bugs elsewhere)
    XC := Curve(Proj(Universe(X)), X);
    C := Curve(Proj(Parent(f)), f);
    tval := Cputime();
    try
        projection := map<XC -> C | proj>;
    catch e
        if warn_invalid then
            print e;
        end if;
        return best, bestkey, false, Cputime(tval), 0.0;
    end try;
    valid := ValidModel(projection : show_reason:=warn_invalid);
    tval := Cputime(tval);
    if not valid then
        if warn_invalid then
            // We want the traceback
            try
                print C`invalid; // User errors don't have tracebacks
            catch e
                if assigned e`Traceback then
                    print e`Traceback;
                end if;
                print "Invalid";
                print "fproj", fproj;
                print "X", X;
                print "best", best;
                print "error: invalid model", assigned e`Position select e`Position else "";
            end try;
        end if;
        return best, bestkey, false, tval, 0.0;
    end if;
    tred := Cputime();
    f, adjust := reducemodel_padic(f);
    tred := Cputime(tred);
    skey := planemodel_sortkey(f);
    if #best eq 0 or skey lt bestkey then
        gonbounds := LMFDBReadGonalityBounds(label);
        QQ := Rationals(); // entries of adjust may be in degree 1 extension of Q
        proj := [proj[i] / QQ!adjust[i] : i in [1..3]];
        best := [<f, proj>];
        bestkey := skey;
        LMFDBWritePlaneModel(f, proj, alg, label);
        if skey[1] lt gonbounds[2] then // improvement to the Q-gonality (and possibly Qbar-gonality)
            gonbounds[2] := skey[1];
            gonbounds[4] := Min(gonbounds[4], skey[1]);
            LMFDBWriteGonalityBounds(gonbounds, label);
        end if;
    end if;
    return best, bestkey, true, tval, tred;
end intrinsic;

*/