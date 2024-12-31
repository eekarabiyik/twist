 intrinsic AgreeableClosure(G::GrpMat)->GrpMat
 {Computes the agreeable closure}
    T:=SL2Intersection(G);
    T`SL:=true;
    T_level:=SL2Level(T);
    T:=SL2Project(T,T_level);
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
    calG:=GL2Project(calG,calG_level);
    return calG;
end intrinsic;