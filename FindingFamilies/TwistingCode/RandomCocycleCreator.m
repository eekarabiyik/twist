intrinsic RandomCocycle(calG:: GrpMat, G:: GrpMat, N:: RngIntElt)-> SeqEnum //only for coarse families so far but gotta try for fine fams.
{gives a list of random cocycle to calG/G. It is given by a set of elements that lies in calGmeetSL2/GmeetSL2 (because there is such an isomorphism)} //How will this change for families over number fields? who knows? in general it is not easy to know things.
    UN,iotaN:=UnitGroup(Integers(N));
    S:=Generators(UN);
    W:=SL2Intersection(calG);
    B:=SL2Intersection(G);
    Blevel,B:=SL2Level(B);
    _,W:=SL2Level(W);
    W:=SL2Lift(W,Blevel);
    /*
    Trans:=Transversal(W,B);
    Trans:=[t: t in Trans];
    listgamma:=[];
    for g in S do
        t:=Random(1,#Trans);
        Append(~listgamma,<g,Trans[t]>);

    end for;
    

    gamma:=hom<UN -> W | listgamma>;
    */
quot,quomap:=quo<W|B>;
quott,quottmap:=AbelianGroup(quot);
L:=Homomorphisms(UN,quott);
list:=[];
for mu in L do 
    if #Kernel(mu) eq #UN then continue; end if;    
    phi:=map<UN->W|[<s,(mu(s)@@quottmap)@@quomap>: s in UN]>;
    list:=list cat [<phi,UN,iotaN,N>];
end for;

return list;
end intrinsic;





intrinsic TwistGroup(groupslist, realgamma,UN,iotaN,N)   -> RngIntElt,SeqEnum
{
    This function takes a cocycle and produces the twisted group.
}
    calG:=groupslist[1];  G:=groupslist[2]; T:=groupslist[3];
    N1,calG:=GL2Level(calG);
    N2,G:=GL2Level(G);
    N3,T:=SL2Level(T);
    assert N mod LCM([N1,N2,N3]) eq 0;
    calG:=GL2Lift(calG,N);
    G:=GL2Lift(G,N);
    T:=SL2Lift(T,N);
    Trans:=Transversal(G, T); 
 // Note: Could precompute this if it is slow. this is ofcourse isomorphic to the UN
    assert #Trans eq #UN;
    // The function xi: (Z/N)^* -> Gc maps each d to a matrix in Gc with determinant d.
    txi:=map<{iotaN(d): d in UN}-> Parent([1]) | [<Determinant(t),[Integers()!a: a in Eltseq(t)]>: t in Trans]>;  // for each number give a matrix whose determinant is that
    // Note:  Could precompute this if it is slow
    S:=Generators(UN);
    gens:=[];
    for u in S do
        d:=Integers()!iotaN(u); 
        g:=GL(2,Integers(N))! txi(Integers(N)!d); // element of G mod N with determinant d
        assert g in calG;
        lifter:=SL2ElementLifter(N3,N);
        h:=lifter(SL(2,Integers(N3))!realgamma(d @@ iotaN)); // David does this so it lies in SL2! PROBLEMMMMM! Okay I know how to create this thing for full determinant.
        assert h in calG;
        g:=h*g;
        gens:=gens cat [g];
    end for;
    gens:= [SL(2,Integers(N))!g : g in Generators(T)] cat gens;
return N, gens;
end intrinsic; 





