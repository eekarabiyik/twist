intrinsic PolynomialTwister(L::SeqEnum, MAT, K) -> SeqEnum
{
    L consists of rational homogeneous coordinates of one degree defining a
    rational map on the representative curve X/Q.  For the package's rational
    action matrices, A = MAT from TwistCurve satisfies sigma(A)*A^(-1) in
    GL(s,Q) for every sigma in Gal(K/Q).  Assume L(A*x) on the twist descends
    as a rational map to Q.  Return coordinates of the same degree with
    rational coefficients, as polynomials over K.
}
    Pol := PolynomialRing(K, NumberOfRows(MAT));
    A := ChangeRing(MAT, K);
    Itw := [Pol | (Pol!f)^A : f in L];
    if Type(K) eq FldRat then
        return Itw;
    end if;

    GAL, _, sigma := AutomorphismGroup(K);
    n := #GAL;
    b := Basis(K)[n];  // Keep the original weight when its conjugates form a basis.
    t := 0;
    while Rank(Matrix([Eltseq(sigma(g)(b)) : g in GAL])) lt n do
        // K.1 is primitive in the package's nontrivial absolute fields.
        // For b = 1/(t-K.1), the determinant of its conjugate embeddings
        // has a pole of order n at t=K.1. Only finitely many t can fail.
        t +:= 1;
        b := 1/(t-K.1);
    end while;

    // At x=A^(-1)*y, the weighted trace is a sum of rational classes
    // f(sigma(A)*A^(-1)*y) with independent weights sigma(b)/n.
    // The class with weight b/n is f(y), so a nonzero class stays nonzero.
    Lnew := [Pol | ];
    for pol in Itw do
        coeffs, mons := CoefficientsAndMonomials(pol);
        q := Pol!0;
        for j in [1..#coeffs] do
            q +:= (Trace(b*coeffs[j])/n)*mons[j];
        end for;
        Append(~Lnew, q);
    end for;
    return Lnew;
end intrinsic;
