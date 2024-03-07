



//This is really dumb I think.
function FiniteLift(A,N1,N2)
    /* Input:
        N1, N2: integers greater than 1 where N1 divides N2
        A: a matrix in GL(2,Z/N1)
        Output:
            A matrix B in GL(2,Z/N2) whose image modulo N1 is A.
    */
    assert A in GL(2,Integers(N1));
    Aint:=Matrix(Integers(),2,2,[Integers()!i: i in Eltseq(A)] ); 
    c:=Integers()!Determinant(Aint);
    if GCD([c,N2]) eq 1 then 
        return GL(2,Integers(N2))!A; 
    else
        T:=[Integers()!i: i in Eltseq(Aint)]; 
        for i in [1..4] do
            if not T[i] eq 0 and GCD([N1,N2,T[i]]) eq 1 then 
                while not GCD([T[i],N2]) eq 1 do
                    T[i]:=T[i]+N1;
        
                end while;
            end if;    
        end for;
        TT:=Matrix(Integers(),2,2,[T[i]: i in [1..4]] );
        while not GCD([Determinant(TT),N2]) eq 1 do
            T[1]:=T[1]+N1;
            TT:=Matrix(Integers(),2,2,[T[i]: i in [1..4]] );
        end while;
        return GL(2,Integers(N2))![T[i]: i in [1..4]];
    end if;
end function;


















//This is the code for, given a subgroup G of GL_2(Zhat) containing identity and having full determinant, finding the family it lies in. 
//We first compute its agreeable closure calG', using this we find the family F(calG,B) such that calG' is conjugate to calG.  
//G:=curves[71]`subgroup;
//T:=G meet SL(2,Integers(#BaseRing(G)));
function FamilyFinderNew(G, T)   
 /*
    Input:
	    G       : a subgroup of GL2(Zhat)
	    T       : G meet SL2
    Output:  
        Famil(ies) that G lies in. Hopefully there will only be one family. 
            
    Note: Assumes that the families are loaded?

 */

    N:=#BaseRing(G);
    M:=#BaseRing(T);
    g:=GL2Genus(T);
    T_level:=sl2Level(T);
    T:=ChangeRing(T,Integers(T_level));
    X:=AssociativeArray();
    G_level:=gl2Level(G);
    Comm_level:=FindCommutatorSubgroup(G);
    callevel:=LCM([G_level,2*LCM([Comm_level,4])]);
    calG:=gl2Lift(G,callevel);
    if not ContainsScalars(calG) then calG:=AdjoinScalars(calG); end if;
    calG_level:=gl2Level(calG);
    calG:=ChangeRing(calG,Integers(calG_level));
    Y:=AssociativeArray();
    for k in Keys(FAM) do
       
       
       time0:=Realtime();
        if FAM[k]`B_level eq T_level and IsConjugate(GL(2,Integers(T_level)),T,FAM[k]`B) and g eq FAM[k]`genus and FAM[k]`calG_level eq calG_level then
            
             A,b:=IsConjugate(GL(2,Integers(calG_level)),calG,FAM[k]`calG);
            if A then 
                Y[k]:=<k,b>;
                //print(k);
            end if;
        end if;
        //print(Realtime(time0));
    end for;
    
    o:=1;
    for t in Keys(Y) do
        b:=FiniteLift(Y[t][2],calG_level,N);
        Tcong:=Conjugate(sl2Lift(T,N),b);
        if ChangeRing(Tcong,Integers(T_level)) eq FAM[t]`B then;
            o:=t;
        end if;
        
    end for;

    b:=FiniteLift(Y[o][2],calG_level,N);

    Gcong:=Conjugate(G,b);
    assert Gcong subset gl2Lift(FAM[o]`calG,N);

    Tcong:=Conjugate(sl2Lift(T,N),b);

    assert Tcong eq sl2Lift(FAM[o]`B,N);


        

return o,FAM[o],Gcong,gl2Lift(FAM[o]`calG,N),Tcong;

end function;


