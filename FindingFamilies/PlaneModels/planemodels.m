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

intrinsic ValidModel(proj::MapSch, p::RngIntElt : num_tests:=3, show_reason:=false) -> BoolElt
{
Input:
    proj - a map between irreducible curves
    p - a prime to use for the reduction (should be larger than the level of the modular curve)
Output:
    whether proj is birational.  Can return a false negative with low probability but shouldn't return false positives
}
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

intrinsic F0Combination(F0::SeqEnum, M) -> SeqEnum //ERAY: this one should be useful for me as well.
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

intrinsic F0Twister(F0::SeqEnum, M,cyclevel) -> SeqEnum //ERAY: this one should be useful for me as well.
{F0 is as in ModularCurveRec, M is a m by n matrix over the integers with full rank, where n is the length of F0.
Applies the matrix M to the expansions, projecting F0 onto 3 modular forms (given by expansions at cusps as normal)}
    // I can't get matrix vector multiplication working reasonably, so we do this by hand
    //vecs := [Vector([F0[i][j] : i in [1..#F0]]) : j in [1..#F0[1]]];
    //vec3s := [v * Transpose(M) : v in vecs];
    //return [[vec3s[i][j] : i in [1..#vec3s]] : j in [1..3]];
     exists(t){t:t in [1..Ncols(M)]|not M[1][t] eq 0 };
    K:=Parent(M[1][t]);
    K;
    L:=Parent(Coefficient(F0[1][1],0));
    L;
    Z<z>:=CyclotomicField(cyclevel);
    Z;
    assert L subset Z;
    assert K subset Z;
    M:=ChangeRing(M,Z);
    FF<qw>:=PowerSeriesRing(Z);
    Mf:=[];
    for l in [1..#F0] do
        cu:=[];
        for j in [1..#F0[l]] do
            a:=&+[Coefficient(F0[l][j],i)*qw^i: i in [0..AbsolutePrecision(F0[l][j])-1]]+O(qw^(AbsolutePrecision(F0[l][j])));
            cu:=cu cat [a];
        end for;
        Mf:= Mf cat [cu];
    end for;
    F0:=Mf;
    ans := [[FF!0 : a in [1..#F0[1]]] : j in [1..Nrows(M)]];
    for a in [1..#F0[1]] do
        for j in [1..Nrows(M)] do
            for i in [1..Ncols(M)] do
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

intrinsic PlaneModelsFromQExpansions(rec::Rec, Can::Crv : success_amount:=25, giveup_time:=600, success_time:=60, ctr_bound:=728) -> SeqEnum
{
    Input:
      - rec: a ModularCurveRec, not hyperelliptic with genus larger than 3
      - Can: The canonical model as found by FindCanonicalModel
      - success_amount: The number of distinct projections sought (default 25)
      - giveup_time: how long to run before returning an empty sequence (default 600 seconds)
      - success_time: how long to run before returning a nonempty sequence with fewer than success_amount entries (default 60 seconds)
      - ctr_bound: A bound on the size of the projector matrix; this should not get triggered (default 728)

    Output:
      - a sequence of pairs <f, proj>, where proj is a 3 by g array of integers defining a projection from rec`F0 to a projective plane and f is the defining equation of the image of the canonical model under this projection.
}
    assert reduction_prime gt rec`N;

    if not assigned rec`F0 then
        if not assigned rec`F then
            rec := FindModularForms(2,rec);
        end if;
        rec := FindCuspForms(rec);
    end if;

    g := rec`genus;
    assert g gt 3; // For genus 3 curves, the canonical model is already a plane model
    low := DegreeLowerBound(g);
    high := DegreeUpperBound(g);
    state := InitProjectorRec(g);
    M := ZeroMatrix(Integers(), 3, g);
    R<X,Y,Z> := PolynomialRing(Rationals(), 3);
    Rg := PolynomialRing(Rationals(), g); // variable names should be assigned later
    CanEqs := DefiningEquations(Can);

    t0:=Cputime();
    ans:=[];
    repeat
        NextProjector(~state, ~M);
        MF := F0Combination(rec`F0, M);

        for m in [low..high] do

            rels := FindRelationsOverKG(rec, MF, m);

            if #rels gt 0 then
                f := R!rels[1];
                proj := [&+[M[i,j] * Rg.j : j in [1..g]] : i in [1..3]];
                // Note that FindRelations is inexact: the modular forms may not actually satisfy the relations exactly, but instead only up to some precision which is lower than the precision of the forms themselves.  As a consequence, proj may not actually define a map from Can to the plane model.  This is checked in ValidModel below.
                XC := Curve(Proj(Universe(CanEqs)), CanEqs);
                C := Curve(Proj(Parent(f)), f);

                try
                    projection := map<XC -> C | proj>;
                    valid := ValidModel(projection,997: show_reason:=true);

                    //print(valid);
                    if valid then

                        Append(~ans, <f,proj,M,MF>);

                    else
                        vprint User1: "invalid model, continuing to next m";
                    end if;
                catch e
                    vprint User1: e;
                end try;
            elif Cputime() - t0 gt giveup_time then
                break;
            end if;
        end for;
        if state`nonpiv_ctr[1] ge ctr_bound then
            print "ctr_bound reached, terminating";
            break;
        end if;
        // Since this is part of the process where we compute the canonical model (and we give that a long timeout), we don't want this to spin forever.
    until #ans ge success_amount or (#ans gt 0 and Cputime() - t0 gt success_time) or (Cputime() - t0 gt giveup_time);

    vprint User1: Sprintf("Plane model: %o model(s) found\n", #ans);
    return ans;
end intrinsic;




intrinsic PlaneModelsFromQExpansionsForm(rec::Rec, Can::Crv, MFF/*modular forms*/ : success_amount:=25, giveup_time:=600, success_time:=60, ctr_bound:=728, verbose:=false) -> SeqEnum
{
    Input:
      - rec: a ModularCurveRec, not hyperelliptic with genus larger than 3
      - Can: The canonical model as found by FindCanonicalModel
      - MFF: The modular forms that are to be used.
      - success_amount: The number of distinct projections sought (default 25)
      - giveup_time: how long to run before returning an empty sequence (default 600 seconds)
      - success_time: how long to run before returning a nonempty sequence with fewer than success_amount entries (default 60 seconds)
      - ctr_bound: A bound on the size of the projector matrix; this should not get triggered (default 728)

    Output:
      - a sequence of pairs <f, proj>, where proj is a 3 by g array of integers defining a projection from rec`F0 to a projective plane and f is the defining equation of the image of the canonical model under this projection.
}
    assert reduction_prime gt rec`N;



    g := rec`genus;
    assert g gt 3; // For genus 3 curves, the canonical model is already a plane model
    low := DegreeLowerBound(g);
    high := DegreeUpperBound(g);
    state := InitProjectorRec(g);
    M := ZeroMatrix(Integers(), 3, g);
    R<X,Y,Z> := PolynomialRing(Rationals(), 3);
    Rg := PolynomialRing(Rationals(), g); // variable names should be assigned later
    CanEqs := DefiningEquations(Can);

    t0:=Cputime();
    ans:=[];
    repeat
        NextProjector(~state, ~M);
        MF := F0Combination(MFF, M);
        relsbydeg:=AssociativeArray();
        for m in [low..high] do
            if verbose then printf "Degree is %o\n",m; end if;

            rels := FindRelationsOverKG(rec, MF, m);
            relsbydeg[m]:=rels;
            if m gt low then
                monm:=MonomialsOfDegree(R,m);
                V:=VectorSpace(Rationals(),#monm);
                W:=sub<V| [V![MonomialCoefficient(o*R!f,mo): mo in monm] : o in [R!X,R!Y,R!Z], f in relsbydeg[m-1]]>;
                V3:=sub<V| [V![MonomialCoefficient(R!f,mo): mo in monm] : f in relsbydeg[m]]>;
                J:=[];
                i:=1;
                while Dimension(W) lt Dimension(V3) do
                    v:=V![MonomialCoefficient(R!relsbydeg[m][i],mo): mo in monm];
                    if v notin W then
                        W:=sub<V|Generators(W) join {v}>;
                        J:=J cat [R!relsbydeg[m][i]];
                    end if;
                    i:=i+1;
                end while;
                rels:=J;
            end if;
            
            if #rels gt 0 then
                //for fff in rels do
                //f:=R!fff;
                f := R!rels[1];
                if verbose then printf "Looking at relations %o\n",f; end if;
                proj := [&+[M[i,j] * Rg.j : j in [1..g]] : i in [1..3]];
                // Note that FindRelations is inexact: the modular forms may not actually satisfy the relations exactly, but instead only up to some precision which is lower than the precision of the forms themselves.  As a consequence, proj may not actually define a map from Can to the plane model.  This is checked in ValidModel below.
                XC := Curve(Proj(Universe(CanEqs)), CanEqs);
                C := Curve(Proj(Parent(f)), f);

                try
                    if verbose then printf "within try\n"; end if;
                    projection := map<XC -> C | proj>;
                    valid := ValidModel(projection,997: show_reason:=true);

                    //print(valid);
                    if valid then
                        if verbose then printf "valid\n"; end if;
                        Append(~ans, <f,proj,M>);

                    else
                        vprint User1: "invalid model, continuing to next m";
                    end if;
                catch e
                     vprint User1: e;
                end try;
                //end for;
            elif Cputime() - t0 gt giveup_time then
                break;
            end if;
        end for;
        if state`nonpiv_ctr[1] ge ctr_bound then
            print "ctr_bound reached, terminating";
            break;
        end if;
        // Since this is part of the process where we compute the canonical model (and we give that a long timeout), we don't want this to spin forever.
    until #ans ge success_amount or (#ans gt 0 and Cputime() - t0 gt success_time) or (Cputime() - t0 gt giveup_time);

    vprint User1: Sprintf("Plane model: %o model(s) found\n", #ans);
    return ans;
end intrinsic;



