
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



intrinsic FamilyFinderWithCusps(G::GrpMat, T::GrpMat, FAM::SeqEnum) -> RngIntElt, Rec, GrpMat, GrpMat, GrpMat
{
    Input:
	    G       : a subgroup of GL2(Zhat) full det, -I in G
	    T       : G meet SL2
        FAM     : The list of families
    Output:
        The family containing G
            u-key of the family
            FAM[u]-family record that contains G
            Gcong- Group G conjugated into the family
            FAM[u]`calG-agreeable closure (not just an agreeable group that contains G)
            Tcong-T conjugated into family
        This one can compute among all families. It utilizes index genus level and cusp number data

}

    
    g:=GL2Genus(T);
    T_level,T:=SL2Level(T);
    G_level,G:=GL2Level(G);
    N:=#BaseRing(G);
    M:=#BaseRing(T);
    //Level 1 is not liked by magma so deal with it separately.
    if T_level eq 1 then
        exists(s){s: s in [1..#FAM]| SL2Level(FAM[s]`B) eq 1};
        FAM[s]`B`SL:=true;
        assert  SL2Project(FAM[s]`B,2) eq SL2Project(T,2);
        return s, FAM[s], G, FAM[s]`calG, T;
    end if;
    //We compute the level to compute the agreeable closure. Level of calG has the same odd divisors as T_level.
    calG:=GL2AgreeableClosure(G);
    calG_level:=GL2Level(calG);
    if calG_level eq 1 then
        exists(s){s: s in [1..#FAM]| GL2Level(FAM[s]`calG) eq 1 and not SL2Level(FAM[s]`B) eq 1};
        assert T eq FAM[s]`B;
        return s, FAM[s], G, FAM[s]`calG, T;
    end if;
    //Adjusting the levels.
    Y:=AssociativeArray();
    M:=LCM([calG_level,T_level]);
    index:=GL2Index(G);
    numberofcusps:=GL2CuspCount(G);
    //We now search for the family it lies in. We check if the agreeable closure and T matches.
    for k in [1..#FAM] do
        if not assigned FAM[k]`H or FAM[k]`fine eq true then continue; end if;
        if index eq FAM[k]`index and FAM[k]`B_level eq T_level and g eq FAM[k]`genus and FAM[k]`calG_level eq calG_level and numberofcusps eq FAM[k]`numberofcusps /*and IsConjugate(GL(2,Integers(T_level)),T,FAM[k]`B)*/ then   //This seems to be working 
            A,b:=IsConjugate(GL(2,Integers(calG_level)),calG,FAM[k]`calG);
            if A then
                Y[k]:=<k,b>;
            end if;
        end if;
    end for;
    o:=-1;
    u:=-1;
    //Y is an array of possible families that contains G.
    //We know the possible families. We conjugate to land in them, then we check whether the SL2 intersections match. 
    for t in Keys(Y) do
        FAM[t]`B`SL:=true;
        b:=FiniteLift(Y[t][2],calG_level,M);
        Tcong:=Conjugate(SL2Lift(T,M),b);
        Tcong`SL:=true;
        //we check if the SL2 intersection are the same.
        if SL2Project(Tcong,T_level) eq FAM[t]`B then;
            o:=t;
            break t;
        else
            FAM[t]`B`SL:=true;
            //If not, it is possible that T is conjugate in the normalizer of calG, we check if this is the case. Either one of these cases will happen.
            norm:=Normalizer(GL2Ambient(M),GL2Lift(FAM[t]`calG,M));
            conj,element:=IsConjugate(norm,SL2Lift(Tcong,M),SL2Lift(FAM[t]`B,M));
            if conj then
                neededb:=element;
                u:=t;
                break t;
            end if;
            // for i in [1..#FAM[t]`conjugacyofB] do

            //     conB:=FAM[t]`conjugacyofB[i];
            //     conB`SL:=true;
            //     lev,conB:=SL2Level(conB);
            //     //M; lev;
            //     assert IsDivisibleBy(M,lev); 
            //     FAM[t]`B`SL:=true;
            //     assert IsConjugate(SL2Ambient(M),SL2Lift(FAM[t]`B,M),SL2Lift(conB,M));
            //     con,element:=IsConjugate(norm,Tcong,SL2Lift(conB,M));
            //     if con then
            //         //i;
            //         FAM[t]`B`SL:=true;
            //         conj,element:=IsConjugate(norm,SL2Lift(Tcong,M),SL2Lift(FAM[t]`B,M));
            //         assert conj;
            //         u:=t;
            //         neededb:=element;
            //         //break t;
            //     end if;
            // end for;
        end if;
    end for;
    if o ne -1 then
        FAM[o]`B`SL:=true;
        //If we have found the family with correct SL2intersection:
        b:=FiniteLift(Y[o][2],calG_level,N);
        bm:=FiniteLift(Y[o][2],calG_level,M);
        Gcong:=Conjugate(G,b);
        Tcong:=Conjugate(SL2Lift(T,M),bm);
        assert Tcong eq SL2Project(SL2Intersection(Gcong),M);
        assert Tcong eq SL2Lift(FAM[o]`B,M);
        _,Tcong:=SL2Level(Tcong);
        Gconglevel,Gcong:=GL2Level(Gcong);
        assert Gcong subset GL2Lift(FAM[o]`calG,Gconglevel);
        return o,FAM[o],Gcong,FAM[o]`calG,Tcong;
    else
        FAM[u]`B`SL:=true;
        //Otherwise T is conjugate to a normalizer conjugate.
        bm:=FiniteLift(Y[u][2],calG_level,M);
        Tcong:=Conjugate(SL2Lift(T,M),bm);
        Tcong:=Conjugate(Tcong,neededb);
        b:=FiniteLift(Y[u][2],calG_level,N);
        Gcong:=Conjugate(G,b);
        neededbN:=FiniteLift(neededb,M,N);
        Gcong:=Conjugate(Gcong,neededbN);
        assert Tcong eq SL2Lift(FAM[u]`B,M);
        assert Tcong eq SL2Project(SL2Intersection(Gcong),M);
        _,Tcong:=SL2Level(Tcong);
        Gconglevel,Gcong:=GL2Level(Gcong);
        assert Gcong subset GL2Lift(FAM[u]`calG,Gconglevel);
        return u,FAM[u],Gcong,FAM[u]`calG,Tcong;
    end if;
end intrinsic;



//Uses canonical generators
intrinsic FamilyFinderCanon(G::GrpMat, T::GrpMat, FAM::SeqEnum,aggcan: use_agg_label:=false,use_family_label:=false,use_parent_can:=false, family_label:="",agreeable_label:="", use) -> RngIntElt, Rec, GrpMat, GrpMat, GrpMat
{
    Input:
	    G       : a subgroup of GL2(Zhat) full det, -I in G
	    T       : G meet SL2
        FAM     : The list of families
    Output:
            The family containing G
            u-key of the family
            FAM[u]-family record that contains G
            Gcong- Group G conjugated into the family
            FAM[u]`calG-agreeable closure (not just an agreeable group that contains G)
            Tcong-T conjugated into family
        This one can compute among all families. But if the parameters are used can use the agreeable closure label or the families label or the p It utilizes index genus level and cusp number data
}
    N:=#BaseRing(G);
    if use_agg_label then 
        YY:=[k: k in Keys(FAM)| agreeable_label eq FAM[k]`agreeable_label];
    elif use_family_label then
        YY:=[k: k in Keys(FAM)| family_label eq FAM[k]`family_label];
    elif use_parent_can then 
        YY:=[k: k in Keys(FAM)| aggcan eq FAM[k]`calG_cangen];
    else 
        YY:=Keys(FAM);
    end if;
    
    Y:=AssociativeArray();
    calG:=GL2AgreeableClosure(G);
    calG_level:=#BaseRing(calG);
    if Type(calG_level) eq Infty then calG_level:=1; end if;
    T_level,T:=SL2Level(T);
    if T_level eq 1 then
        listkeys:=[k: k in Keys(FAM)| #BaseRing(FAM[k]`B) eq 2 and FAM[k]`B eq SL2Ambient(2) and SL2Level(FAM[k]`B) eq 1];
        s:=listkeys[1];
        assert FAM[s]`B eq SL2Project(T,2);
        return s, FAM[s], G, FAM[s]`calG, T;
    end if;
    if calG_level eq 1 then
        listkeys:=[k: k in Keys(FAM)| #BaseRing(FAM[k]`calG) eq 2 and FAM[k]`calG eq GL2Ambient(2) and SL2Level(FAM[k]`B) eq 2];
        s:=listkeys[1];
        assert T eq FAM[s]`B;
        return s, FAM[s], G, FAM[s]`calG, T;
    end if;
    g:=GL2Genus(T);
    M:=LCM([calG_level,T_level]);
    index:=GL2Index(G);
    for k in YY do
        if not assigned FAM[k]`H or FAM[k]`fine eq true then continue; end if;
        if index eq FAM[k]`index and FAM[k]`B_level eq T_level and g eq FAM[k]`genus and FAM[k]`calG_level eq calG_level and IsConjugate(GL(2,Integers(T_level)),T,FAM[k]`B) then   //This seems to be working
            //k;
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
            conj,element:=IsConjugate(norm,SL2Lift(Tcong,M),SL2Lift(FAM[t]`B,M));
            if conj then
                neededb:=element;
                u:=t;
                break t;
            end if;
            // for i in [1..#FAM[t]`conjugacyofB] do

            //     conB:=FAM[t]`conjugacyofB[i];
            //     conB`SL:=true;
            //     lev,conB:=SL2Level(conB);
            //     //M; lev;
            //     assert IsDivisibleBy(M,lev); 
            //     FAM[t]`B`SL:=true;
            //     assert IsConjugate(SL2Ambient(M),SL2Lift(FAM[t]`B,M),SL2Lift(conB,M));
            //     con,element:=IsConjugate(norm,Tcong,SL2Lift(conB,M));
            //     if con then
            //         //i;
            //         FAM[t]`B`SL:=true;
            //         conj,element:=IsConjugate(norm,SL2Lift(Tcong,M),SL2Lift(FAM[t]`B,M));
            //         assert conj;
            //         u:=t;
            //         neededb:=element;
            //         //break t;
            //     end if;
            // end for;
        end if;
    end for;
    if o ne -1 then
        //If we have found the family with correct SL2intersection:
        b:=FiniteLift(Y[o][2],calG_level,N);
        bm:=FiniteLift(Y[o][2],calG_level,M);
        Gcong:=Conjugate(G,b);
        Tcong:=Conjugate(SL2Lift(T,M),bm);
        assert Tcong eq SL2Project(SL2Intersection(Gcong),M);
        assert Tcong eq SL2Lift(FAM[o]`B,M);
        _,Tcong:=SL2Level(Tcong);
        _,Gcong:=GL2Level(Gcong);
        return o,FAM[o],Gcong,FAM[o]`calG,Tcong;
    else
        //Otherwise T is conjugate to a normalizer conjugate.
        bm:=FiniteLift(Y[u][2],calG_level,M);
        Tcong:=Conjugate(SL2Lift(T,M),bm);
        Tcong:=Conjugate(Tcong,neededb);
        b:=FiniteLift(Y[u][2],calG_level,N);
        Gcong:=Conjugate(G,b);
        neededbN:=FiniteLift(neededb,M,N);
        Gcong:=Conjugate(Gcong,neededbN);
        assert Tcong eq SL2Lift(FAM[u]`B,M);
        assert Tcong eq SL2Project(SL2Intersection(Gcong),M);
        _,Tcong:=SL2Level(Tcong);
        _,Gcong:=GL2Level(Gcong);
        return u,FAM[u],Gcong,FAM[u]`calG,Tcong;
    end if;
end intrinsic;




//This is the code for, given a subgroup G of GL_2(Zhat) containing identity and having full determinant, finding the family it lies in.
//We first compute its agreeable closure calG', using this we find the family F(calG,B) such that calG' is conjugate to calG.
intrinsic FamilyFinderFine(G::GrpMat, T::GrpMat, FAM::SeqEnum) -> RngIntElt, Rec, GrpMat, GrpMat, GrpMat
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
    T_level,T:=SL2Level(T);
    G_level,G:=GL2Level(G);
    //Level 1 is not liked by magma so deal with it separately.
    if T_level eq 1 then
        exists(s){s: s in [1..#FAM]| SL2Level(FAM[s]`B) eq 1};
        assert FAM[s]`B eq SL2Project(T,2);
        return s, FAM[s], G, FAM[s]`calG, T;
    end if;
    //We compute the level to compute the agreeable closure. Level of calG has the same odd divisors as T_level.
    calG:=GL2AgreeableClosure(G);
    calG_level:=GL2Level(calG);
    if calG_level eq 1 then
        exists(s){s: s in [1..#FAM]| GL2Level(FAM[s]`calG) eq 1 and not SL2Level(FAM[s]`B) eq 1};
        assert T eq FAM[s]`B;
        return s, FAM[s], G, FAM[s]`calG, T;
    end if;
    //Adjusting the levels.
    Y:=AssociativeArray();
    M:=LCM([calG_level,T_level]);
    index:=GL2Index(G);
    numberofcusps:=GL2CuspCount(G);
    //We now search for the family it lies in. We check if the agreeable closure and T matches.
    for k in [1..#FAM] do
        if not FAM[k]`fine eq true then continue; end if;
        if index eq FAM[k]`index and FAM[k]`B_level eq T_level and g eq FAM[k]`genus and FAM[k]`calG_level eq calG_level and numberofcusps eq FAM[k]`numberofcusps and IsConjugate(GL(2,Integers(T_level)),T,FAM[k]`B) then
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
            conj,element:=IsConjugate(norm,SL2Lift(Tcong,M),SL2Lift(FAM[t]`B,M));
            if conj then
                neededb:=element;
                u:=t;
                break t;
            end if;
            // for i in [1..#FAM[t]`conjugacyofB] do

            //     conB:=FAM[t]`conjugacyofB[i];
            //     conB`SL:=true;
            //     lev,conB:=SL2Level(conB);
            //     //M; lev;
            //     assert IsDivisibleBy(M,lev); 
            //     FAM[t]`B`SL:=true;
            //     assert IsConjugate(SL2Ambient(M),SL2Lift(FAM[t]`B,M),SL2Lift(conB,M));
            //     con,element:=IsConjugate(norm,Tcong,SL2Lift(conB,M));
            //     if con then
            //         //i;
            //         FAM[t]`B`SL:=true;
            //         conj,element:=IsConjugate(norm,SL2Lift(Tcong,M),SL2Lift(FAM[t]`B,M));
            //         assert conj;
            //         u:=t;
            //         neededb:=element;
            //         //break t;
            //     end if;
            // end for;
        end if;
    end for;
    if o ne -1 then
        //If we have found the family with correct SL2intersection:
        b:=FiniteLift(Y[o][2],calG_level,N);
        bm:=FiniteLift(Y[o][2],calG_level,M);
        Gcong:=Conjugate(G,b);
        Tcong:=Conjugate(SL2Lift(T,M),bm);
        assert Tcong eq SL2Project(SL2Intersection(Gcong),M);
        assert Tcong eq SL2Lift(FAM[o]`B,M);
        _,Tcong:=SL2Level(Tcong);
        _,Gcong:=GL2Level(Gcong);
        return o,FAM[o],Gcong,FAM[o]`calG,Tcong;
    else
        //Otherwise T is conjugate to a normalizer conjugate.
        bm:=FiniteLift(Y[u][2],calG_level,M);
        Tcong:=Conjugate(SL2Lift(T,M),bm);
        Tcong:=Conjugate(Tcong,neededb);
        b:=FiniteLift(Y[u][2],calG_level,N);
        Gcong:=Conjugate(G,b);
        neededbN:=FiniteLift(neededb,M,N);
        Gcong:=Conjugate(Gcong,neededbN);
        assert Tcong eq SL2Lift(FAM[u]`B,M);
        assert Tcong eq SL2Project(SL2Intersection(Gcong),M);
        _,Tcong:=SL2Level(Tcong);
        _,Gcong:=GL2Level(Gcong);
        return u,FAM[u],Gcong,FAM[u]`calG,Tcong;
    end if;
end intrinsic;


/*
intrinsic FamilyFinder(G::GrpMat, T::GrpMat, FAM::SeqEnum) -> RngIntElt, Rec, GrpMat, GrpMat, GrpMat
{
    Input:
	    G       : a subgroup of GL2(Zhat) full det, -I in G
	    T       : G meet SL2
        FAM     : The list of families
    Output:
        The family containing G

}

    
    g:=GL2Genus(T);
    T_level,T:=SL2Level(T);
    G_level,G:=GL2Level(G);
    N:=#BaseRing(G);
    M:=#BaseRing(T);
    //Level 1 is not liked by magma so deal with it separately.
    if T_level eq 1 then
        exists(s){s: s in [1..#FAM]| SL2Level(FAM[s]`B) eq 1};
        assert FAM[s]`B eq SL2Project(T,2);
        return s, FAM[s], G, FAM[s]`calG, T;
    end if;
    //We compute the level to compute the agreeable closure. Level of calG has the same odd divisors as T_level.
    calG:=GL2AgreeableClosure(G);
    calG_level:=GL2Level(calG);
    if calG_level eq 1 then
        exists(s){s: s in [1..#FAM]| GL2Level(FAM[s]`calG) eq 1 and not SL2Level(FAM[s]`B) eq 1};
        assert T eq FAM[s]`B;
        return s, FAM[s], G, FAM[s]`calG, T;
    end if;
    //Adjusting the levels.
    Y:=AssociativeArray();
    M:=LCM([calG_level,T_level]);
    index:=GL2Index(G);
    //We now search for the family it lies in. We check if the agreeable closure and T matches.
    for k in [1..#FAM] do
        if not assigned FAM[k]`H or FAM[k]`fine eq true then continue; end if;
        if index eq FAM[k]`index and FAM[k]`B_level eq T_level and g eq FAM[k]`genus and FAM[k]`calG_level eq calG_level and IsConjugate(GL(2,Integers(T_level)),T,FAM[k]`B) then
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

//Uses labels of the agreeable closure
intrinsic FamilyFinderAgLabel(G::GrpMat, T::GrpMat, FAM::SeqEnum,agglabel) -> RngIntElt, Rec, GrpMat, GrpMat, GrpMat
{
    Input:
	    G       : a subgroup of GL2(Zhat) full det, -I in G
	    T       : G meet SL2
        FAM     : The list of families
    Output:
        The family containing G

}
    N:=#BaseRing(G);
    YY:=[k: k in Keys(FAM)| agglabel eq FAM[k]`agreeable_label];
    Y:=AssociativeArray();
    calG:=GL2AgreeableClosure(G);
    calG_level:=#BaseRing(calG);
    T_level,T:=SL2Level(T);
    g:=GL2Genus(T);
    M:=LCM([calG_level,T_level]);
    index:=GL2Index(G);
    for k in YY do
        if not assigned FAM[k]`H or FAM[k]`fine eq true then continue; end if;
        if index eq FAM[k]`index and FAM[k]`B_level eq T_level and g eq FAM[k]`genus and FAM[k]`calG_level eq calG_level and IsConjugate(GL(2,Integers(T_level)),T,FAM[k]`B) then   //This seems to be working
            //k;
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
*/



intrinsic OldFamilyFinderWithCusps(G::GrpMat, T::GrpMat, FAM::SeqEnum) -> RngIntElt, Rec, GrpMat, GrpMat, GrpMat
{
    Input:
	    G       : a subgroup of GL2(Zhat) full det, -I in G
	    T       : G meet SL2
        FAM     : The list of families
    Output:
        The family containing G

}

    
    g:=GL2Genus(T);
    T_level,T:=SL2Level(T);
    G_level,G:=GL2Level(G);
    N:=#BaseRing(G);
    M:=#BaseRing(T);
    //Level 1 is not liked by magma so deal with it separately.
    if T_level eq 1 then
        exists(s){s: s in [1..#FAM]| SL2Level(FAM[s]`B) eq 1};
        FAM[s]`B`SL:=true;
        assert  SL2Project(FAM[s]`B,2) eq SL2Project(T,2);
        return s, FAM[s], G, FAM[s]`calG, T;
    end if;
    //We compute the level to compute the agreeable closure. Level of calG has the same odd divisors as T_level.
    calG:=GL2AgreeableClosure(G);
    calG_level:=GL2Level(calG);
    if calG_level eq 1 then
        exists(s){s: s in [1..#FAM]| GL2Level(FAM[s]`calG) eq 1 and not SL2Level(FAM[s]`B) eq 1};
        assert T eq FAM[s]`B;
        return s, FAM[s], G, FAM[s]`calG, T;
    end if;
    //Adjusting the levels.
    Y:=AssociativeArray();
    M:=LCM([calG_level,T_level]);
    index:=GL2Index(G);
    numberofcusps:=GL2CuspCount(G);
    //We now search for the family it lies in. We check if the agreeable closure and T matches.
    for k in [1..#FAM] do
        if not assigned FAM[k]`H or FAM[k]`fine eq true then continue; end if;
        if index eq FAM[k]`index and FAM[k]`B_level eq T_level and g eq FAM[k]`genus and FAM[k]`calG_level eq calG_level and numberofcusps eq FAM[k]`numberofcusps /*and IsConjugate(GL(2,Integers(T_level)),T,FAM[k]`B)*/ then   //This seems to be working 
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



intrinsic ConjugateIntoFamily(G,T,fam)->RngIntElt, Rec, GrpMat, GrpMat, GrpMat
     {
        Input:  G open subgroup
                T: G meet SL2
                fam: a single family. We already know that G is in fam
        Output: G and T conjugated into this family.
     }
    g:=GL2Genus(T);
    T_level,T:=SL2Level(T);
    G_level,G:=GL2Level(G);
    N:=#BaseRing(G);
    M:=#BaseRing(T);
      M:=LCM([#BaseRing(fam`calG),T_level]);

    A,b:=GL2IsConjugateSubgroup(GL2Lift(fam`calG,G_level),G);
    A;
    Tcong:=Conjugate(SL2Lift(T,G_level),b);
    Tcong`SL:=true;

     o:=-1;
    u:=-1;
    t:=31;
        if SL2Project(Tcong,T_level) eq fam`B then;
            o:=t;

        else
            fam`B`SL:=true;
            //If not, it is possible that T is conjugate in the normalizer of calG, we check if this is the case. Either one of these cases will happen.
            norm:=Normalizer(GL2Ambient(M),GL2Lift(fam`calG,M));
            conj,element:=IsConjugate(norm,SL2Lift(Tcong,M),SL2Lift(fam`B,M));
            if conj then
                neededb:=element;
                u:=t;
            end if;

        end if;

    if o ne -1 then
        //If we have found the family with correct SL2intersection:

        bm:=GL2Ambient(M)!ChangeRing(b,Integers(M));
        bm;
        Gcong:=Conjugate(G,b);
        Tcong:=Conjugate(SL2Lift(T,M),bm);
        assert Tcong eq SL2Project(SL2Intersection(Gcong),M);
        assert Tcong eq SL2Lift(fam`B,M);
        _,Tcong:=SL2Level(Tcong);
        _,Gcong:=GL2Level(Gcong);
        return o,fam,Gcong,fam`calG,Tcong;
    else
        //Otherwise T is conjugate to a normalizer conjugate.
        bm:=GL2Ambient(M)!ChangeRing(b,Integers(M));
        Tcong:=Conjugate(SL2Lift(T,M),bm);
        Tcong:=Conjugate(Tcong,neededb);
        //b:=FiniteLift(Y[u][2],calG_level,N);
        Gcong:=Conjugate(G,b);
        neededbN:=FiniteLift(neededb,M,N);
        Gcong:=Conjugate(Gcong,neededbN);
        assert Tcong eq SL2Lift(fam`B,M);
        assert Tcong eq SL2Project(SL2Intersection(Gcong),M);
        _,Tcong:=SL2Level(Tcong);
        _,Gcong:=GL2Level(Gcong);
        return u,fam,Gcong,fam`calG,Tcong;
    end if;
end intrinsic;