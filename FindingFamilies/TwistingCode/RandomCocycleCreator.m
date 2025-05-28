intrinsic RandomCocycle(calG:: GrpMat, G:: GrpMat, N:: RngIntElt)-> SeqEnum //only for coarse families so far but gotta try for fine fams.
{gives a list of random cocycle to calG/G. It is given by a set of elements that lies in calGmeetSL2/GmeetSL2 (because there is such an isomorphism)} //How will this change for families over number fields? who knows? in general it is not easy to know things.
    //UN,iotaN:=UnitGroup(Integers(N));
    GL1:=GL1Ambient(N);
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
AbelGL1,abelmap:=AbelianGroup(GL1);
L:=Homomorphisms(AbelGL1,quott);
list:=[];
for mu in L do 
    if #Kernel(mu) eq #GL1 then continue; end if;    
    phi:=map<GL1->W|[<s @@ abelmap,(mu(s)@@quottmap)@@quomap>: s in AbelGL1]>;
    list:=list cat [<phi,GL1,N>];
end for;

return list;
end intrinsic;

function lift_hom(f, M)
    R := BaseRing(Domain(f));
    GM := GL1Lift(Domain(f), M);
    return hom<GM -> Codomain(f) | [<GM.i, ChangeRing(GM.i, R) @ f> : i in [1..Ngens(GM)]] >;
end function;


intrinsic TwistGroup(groupslist, realgamma,GL1,N)   -> RngIntElt,SeqEnum
{
    This function takes a cocycle and produces the twisted group.
}   tttt:=Cputime();
    calG:=groupslist[1];  G:=groupslist[2]; T:=groupslist[3];
    N1,calG:=GL2Level(calG);
    N2,G:=GL2Level(G);
    N3,T:=SL2Level(T);
    NewN:=LCM([N1,N2,N3,N]);
    NewN;


    GL1:=GL1Lift(GL1,NewN);
    realgamma:=lift_hom(realgamma,NewN);
    calG:=GL2Lift(calG,NewN);
    G:=GL2Lift(G,NewN);
    T:=SL2Lift(T,NewN);


    /*
    listofelements:=[];
    for d in GL1 do
        exists(g){g:g in G|Matrix([[Determinant(g)]]) eq d};
        listofelements:=listofelements cat [<d,g>];
    end for;
    */    
    "Forming the determinant map";
    detmapp:=hom<G->GL1|[<g,Matrix([[Determinant(g)]])>: g in Generators(G)]>;


    //tttxi:=map<GL1>;
    //Trans:=Transversal(G, T); 
 // Note: Could precompute this if it is slow. this is ofcourse isomorphic to the UN
    //assert #Trans eq #GL1;
    // The function xi: (Z/N)^* -> Gc maps each d to a matrix in Gc with determinant d.
    "Inverse Determinant map";
    txi:=map<{d: d in GL1}-> G | [<d,d @@ detmapp >: d in GL1]>; 
    //txi:=map<{d: d in GL1}-> G | listofelements>; 

    Cputime(tttt); // for each number give a matrix whose determinant is that
    // Note:  Could precompute this if it is slow
    S:=Generators(GL1);
    gens:=[];
    "Forming the group";
    for u in S do
        d:=Integers()!u[1][1]; 
        g:=GL(2,Integers(NewN))! txi(u); // element of G mod N with determinant d
        assert g in calG;
        lifter:=SL2ElementLifter(N3,NewN);
        h:=lifter(SL(2,Integers(N3))!realgamma(u)); // David does this so it lies in SL2! PROBLEMMMMM! Okay I know how to create this thing for full determinant.
        assert h in calG;
        g:=h*g;
        gens:=gens cat [g];
    end for;
    "Done";
    Cputime(tttt);
    gens:= [SL(2,Integers(NewN))!g : g in Generators(T)] cat gens;
return NewN, gens;
end intrinsic; 





