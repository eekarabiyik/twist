intrinsic F0Twister(F0::SeqEnum, M::ModMatRngElt) -> SeqEnum //ERAY: this one should be useful for me as well.
{F0 is as in ModularCurveRec, M is m 3 by n matrix over the integers with full rank, where n is the length of F0.
Applies the matrix M to the expansions, projecting F0 onto m modular forms (given by expansions at cusps as normal)}
    // I can't get matrix vector multiplication working reasonably, so we do this by hand
    //vecs := [Vector([F0[i][j] : i in [1..#F0]]) : j in [1..#F0[1]]];
    //vec3s := [v * Transpose(M) : v in vecs];
    //return [[vec3s[i][j] : i in [1..#vec3s]] : j in [1..3]];
    exists(t){t:t in [1..Ncols(M)]|not M[1][t] eq 0 };
    K:=Parent(M[1][t]);
    L:=Parent(Coefficient(F0[1][1],0));
    Z:=Compositum(K,L);
    FF<qw>:=PowerSeriesRing(Z);
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
