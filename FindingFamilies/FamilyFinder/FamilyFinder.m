//THIS IS NOW OLD.


//By David Zywina
intrinsic ContainsScalars(G::GrpMat)-> BoolElt
{    For a subgroup of GL(2,Z/N) with N>1, return true if G contains all the scalar matrices and false otherwise.}
    N:=#BaseRing(G);
    GL2:=GL(2,Integers(N));
    U,iota:=UnitGroup(Integers(N));
    return &and [ (GL2![iota(U.i),0,0,iota(U.i)]) in G : i in [1..Ngens(U)] ];
end intrinsic;

//By David Zywina
intrinsic AdjoinScalars(G::GrpMat)->GrpMat
    { For a subgroup of GL(2,Z/N) with N>1, return the group obtained by adding all the scalar matrices to G.}
    N:=#BaseRing(G);
    GL2:=GL(2,Integers(N));
    gens:=[G.i: i in [1..Ngens(G)]];
    U,iota:=UnitGroup(Integers(N));
    gens:= gens cat [ GL2![iota(U.i),0,0,iota(U.i)] : i in [1..Ngens(U)] ];
    return sub<GL2|gens>;
end intrinsic;



//Based on Andrew Sutherland's intrinsic (which is faster than what I was using).
intrinsic FiniteLift(A::GrpMatElt, N::RngIntElt, M::RngIntElt) -> GrpMat
{
    Lifts an element A of GL(2,Z/N) to GL(2, Z/M)
}
    assert IsDivisibleBy(M, N);
    if N eq M then return A; end if;
    GL2 := GL(2,Integers(M));
    M2 := MatrixRing(Integers(),2);
    m := &*[a[1]^a[2]: a in Factorization(M)| N mod a[1] eq 0];
    return GL2!CRT([M2!A, Identity(M2)], [m, M div m]);
end intrinsic;

//This is the code for, given a subgroup G of GL_2(Zhat) containing identity and having full determinant, finding the family it lies in.
//We first compute its agreeable closure calG', using this we find the family F(calG,B) such that calG' is conjugate to calG.
intrinsic FamilyFinderNew(G::GrpMat, T::GrpMat, FAM::SeqEnum) -> RngIntElt, Rec, GrpMat, GrpMat, GrpMat
{
    Input:
	    G       : a subgroup of GL2(Zhat) full det, -I in G
	    T       : G meet SL2
        FAM     : The list of families
    Output:
        The family containing G

}

    N:=#BaseRing(G);
    M:=#BaseRing(T);
    g:=GL2Genus(T);
    T_level:=SL2Level(T);
    //Level 1 is not liked by magma so deal with it separately.
    if T_level eq 1 then
        exists(s){s: s in [1..#FAM]| SL2Level(FAM[s]`B) eq 1};
        assert FAM[s]`B eq SL2Project(T,2);
        return s, FAM[s], G, FAM[s]`calG, T;
    end if;
    //We compute the level to compute the agreeable closure. Level of calG has the same odd divisors as T_level.
    T:=SL2Project(T,T_level);
    X:=AssociativeArray();
    G_level:=GL2Level(G);
    levelneededG:=LCM([G_level,2]);
    levelneededT:=LCM([T_level,2]);
    G:=GL2Lift(G,LCM([G_level,2]));
    T:=SL2Lift(T,LCM([T_level,2]));
    callevel:=1;
    for p in PrimeDivisors(#BaseRing(T)) do
        callevel:=callevel*p^(Maximum(Valuation(levelneededT,p),Valuation(levelneededG,p)));
    end for;
    calG:=GL2Project(G,callevel);
    if not ContainsScalars(calG) then calG:=AdjoinScalars(calG); end if;
    calG_level:=GL2Level(calG);
    //Now agreeable closure is computed, we deal with level 1 case separately.
    if calG_level eq 1 then
        exists(s){s: s in [1..#FAM]| GL2Level(FAM[s]`calG) eq 1 and not SL2Level(FAM[s]`B) eq 1};
        assert T eq FAM[s]`B;
        return s, FAM[s], G, FAM[s]`calG, T;
    end if;
    //Adjusting the levels.
    calG:=GL2Project(calG,calG_level);
    T:=SL2Project(T,T_level);
    G:=GL2Project(G,N);
    Y:=AssociativeArray();
    M:=LCM([calG_level,T_level]);
    //We now search for the family it lies in. We check if the agreeable closure and T matches.
    for k in [1..#FAM] do
        if FAM[k]`B_level eq T_level and g eq FAM[k]`genus and FAM[k]`calG_level eq calG_level and IsConjugate(GL(2,Integers(T_level)),T,FAM[k]`B) then
            A,b:=IsConjugate(GL(2,Integers(calG_level)),calG,FAM[k]`calG);
            if A then
                Y[k]:=<k,b>;
            end if;
        end if;
    end for;

    o:=-1;
    u:=-1;
    //Y is an array of possible families that contains G.
    //We know possible families. We conjugate to land in them, then we check whether the SL2 intersections match. 
    for t in Keys(Y) do
        b:=FiniteLift(Y[t][2],calG_level,M);
        Tcong:=Conjugate(SL2Lift(T,M),b);
        Tcong`SL:=true;
        //we check if the SL2 intersection are the same.
        if SL2Project(Tcong,T_level) eq FAM[t]`B then;
            o:=t;
            break t;
        else
            //If not, it is possible that T is conjugate in the normalizer of calG, we check if this is the case. Either one of these cases will happen.
            norm:=Normalizer(GL2Ambient(M),GL2Lift(FAM[t]`calG,M));
            for i in [1..#FAM[t]`conjugacyofB] do
                conB:=FAM[t]`conjugacyofB[i];
                conB`SL:=true;
                con,element:=IsConjugate(norm,SL2Lift(conB,M),Tcong);
                if con then
                    u:=t;
                    neededb:=element;
                    break t;
                end if;
            end for;
        end if;
    end for;

    if o ne -1 then
        //If we have found the family with correct SL2intersection:
        b:=FiniteLift(Y[o][2],calG_level,N);
        bm:=FiniteLift(Y[o][2],calG_level,M);
        Gcong:=Conjugate(G,b);
        Tcong:=Conjugate(SL2Lift(T,M),bm);

        return o,FAM[o],Gcong,FAM[o]`calG,Tcong;
    else
        //Otherwise T is conjugate to a normalizer conjugate.
        bm:=FiniteLift(Y[u][2],calG_level,M);
        Tcong:=Conjugate(SL2Lift(T,M),bm);//figure out conjugation
        Tcong:=Conjugate(Tcong,neededb);
        b:=FiniteLift(Y[u][2],calG_level,N);
        Gcong:=Conjugate(G,b);
        neededbN:=FiniteLift(neededb,M,N);
        Gcong:=Conjugate(Gcong,neededbN);

        return u,FAM[u],Gcong,FAM[u]`calG,Tcong;
    end if;
end intrinsic;



