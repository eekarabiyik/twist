AttachSpec("/homes/ek693/OptimizingTheProject/DrewMagma/magma.spec");
//By David Zywina
function ContainsScalars(G)
    // For a subgroup of GL(2,Z/N) with N>1, return true if G contains all the scalar matrices and false otherwise.
    N:=#BaseRing(G);
    GL2:=GL(2,Integers(N));
    U,iota:=UnitGroup(Integers(N));
    return &and [ (GL2![iota(U.i),0,0,iota(U.i)]) in G : i in [1..Ngens(U)] ];
end function;
//By David Zywina
function AdjoinScalars(G)
    // For a subgroup of GL(2,Z/N) with N>1, return the group obtained by adding all the scalar matrices to G.
    N:=#BaseRing(G); 
    GL2:=GL(2,Integers(N));
    gens:=[G.i: i in [1..Ngens(G)]];
    U,iota:=UnitGroup(Integers(N));
    gens:= gens cat [ GL2![iota(U.i),0,0,iota(U.i)] : i in [1..Ngens(U)] ];
    return sub<GL2|gens>;
end function;



//Based on Andrew Sutherland's intrinsic (which is faster than what I was using). 
function FiniteLift(A,N,M) 
    assert IsDivisibleBy(M, N);
    if N eq M then return A; end if;
    GL2 := GL(2,Integers(M));
    M2 := MatrixRing(Integers(),2);
    m := &*[a[1]^a[2]: a in Factorization(M)| N mod a[1] eq 0];
    return GL2!CRT([M2!A, Identity(M2)], [m, M div m]);
end function;




//This is the code for, given a subgroup G of GL_2(Zhat) containing identity and having full determinant, finding the family it lies in. 
//We first compute its agreeable closure calG', using this we find the family F(calG,B) such that calG' is conjugate to calG.  
function FamilyFinderNew(G, T)   
 /*
    Input:
	    G       : a subgroup of GL2(Zhat) full det, -I in G
	    T       : G meet SL2
    Output:  
        A family that G lies in. 
            
    Note: Assumes that the families.

 */
    


 time0:=Realtime();
    N:=#BaseRing(G);
    M:=#BaseRing(T);
    g:=GL2Genus(T);
    T_level:=SL2Level(T);
    if T_level eq 1 then 
        exists(s){s: s in Keys(FAM)| SL2Level(FAM[s]`B) eq 1};
        assert FAM[s]`B eq SL2Project(T,2);
        return s,FAM[s], G, FAM[s]`calG, T;
    end if;
    T:=SL2Project(T,T_level);
    X:=AssociativeArray();
    G_level:=GL2Level(G);
    levelneededG:=LCM([G_level,2]);
    levelneededT:=LCM([T_level,2]);
    G:=GL2Lift(G,LCM([G_level,2]));
    T:=SL2Lift(T,LCM([T_level,2]));
    callevel:=1;
    Realtime(time0);
    time1:=Realtime();
    time4:=Realtime();
    for p in PrimeDivisors(#BaseRing(T)) do
        callevel:=callevel*p^(Maximum(Valuation(levelneededT,p),Valuation(levelneededG,p)));
    end for;
    calG:=GL2Project(G,callevel);
    if not ContainsScalars(calG) then calG:=AdjoinScalars(calG); end if;
    calG_level:=GL2Level(calG);
        if calG_level eq 1 then
        exists(s){s: s in Keys(FAM)| GL2Level(FAM[s]`calG) eq 1 and not SL2Level(FAM[s]`B) eq 1};
        assert T eq FAM[s]`B;
        return s,FAM[s], G, FAM[s]`calG, T;
    end if;
    calG:=GL2Project(calG,calG_level);
    T:=SL2Project(T,T_level);
    G:=GL2Project(G,N);
    Y:=AssociativeArray();
    M:=LCM([calG_level,T_level]);
    Realtime(time4);









    time10:=Realtime();
   
    for k in Keys(FAM) do
       //if not FAM[k]`genus eq g or not FAM[k]`B_level eq T_level or not FAM[k]`calG_level eq calG_level then continue; end if;
       
       //time0:=Realtime();
        if FAM[k]`B_level eq T_level  and g eq FAM[k]`genus and FAM[k]`calG_level eq calG_level and IsConjugate(GL(2,Integers(T_level)),T,FAM[k]`B) then
            
            A,b:=IsConjugate(GL(2,Integers(calG_level)),calG,FAM[k]`calG);
            if A then 
                Y[k]:=<k,b>;
                //break k;
                //print(k);
            end if;
        end if;
        //print(Realtime(time0));
    end for;
   
    o:=-1;
    u:=-1;
   // "number of keys is";
    //#Y;
    //Keys(Y);
    print(Realtime(time10));
        for t in Keys(Y) do
            b:=FiniteLift(Y[t][2],calG_level,M);
            Tcong:=Conjugate(SL2Lift(T,M),b);
            Tcong`SL:=true;
            
            if SL2Project(Tcong,T_level) eq FAM[t]`B then;
                o:=t;
                break t;
            else
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

   

    if not o eq -1 then
        b:=FiniteLift(Y[o][2],calG_level,N);
        bm:=FiniteLift(Y[o][2],calG_level,M);
        Gcong:=Conjugate(G,b);
        Tcong:=Conjugate(SL2Lift(T,M),bm);

        return o,FAM[o],Gcong,FAM[o]`calG,Tcong;
    else
        bm:=FiniteLift(Y[u][2],calG_level,M);
        Tcong:=Conjugate(SL2Lift(T,M),bm);//figure out conjugation
        Tcong:=Conjugate(Tcong,neededb);
        b:=FiniteLift(Y[u][2],calG_level,N);
        Gcong:=Conjugate(G,b);
        neededbN:=FiniteLift(neededb,M,N);
        Gcong:=Conjugate(Gcong,neededbN);

        return u,FAM[u],Gcong,FAM[u]`calG,Tcong;
    end if;
    
    
    

end function;




//This should be completely fine at this point.