intrinsic RandomCocycle(calG:: GrpMat, G:: GrpMat, N:: RngIntElt)-> SeqEnum //only for coarse families so far but gotta try for fine fams.
{gives a random cocycle to calG/G. It is given by a set of elements that lies in calGmeetSL2/GmeetSL2 (because there is such an isomorphism)}
    UN,iotaN:=UnitGroup(Integers(N));
    S:=Generators(UN);
    W:=SL2Intersection(calG);
    B:=SL2Intersection(G);
    Blevel,B:=SL2Level(B);
    _,W:=SL2Level(W);
    W:=SL2Lift(W,Blevel);
    Trans:=Transversal(W,B);
    Trans:=[t: t in Trans];
    listgamma:=[];
    for g in S do
        t:=Random(1,#Trans);
        Append(~listgamma,<g,Trans[t]>);

    end for;

    gamma:=hom<UN -> W | listgamma>;

quot,quomap:=quo<W|B>;
quott,quottmap:=AbelianGroup(quot);
L:=Homomorphisms(UN,quott);
list:=[];
for mu in L do 
    phi:=map<UN->W|[<s,(mu(s)@@quottmap)@@quomap>: s in UN]>;
    list:=list cat [<phi,UN,iotaN,N>];
end for;

return list;
end intrinsic;





intrinsic TwistGroup(groupslist, realgamma,UN,iotaN,N)   -> RngIntElt,SeqEnum
{
// Input: calG: Agreeable closure of G.
// realgamma: UN-> calG is the lift of the homomorphism to calG/G to calG. So each d maps to an element in calG meet SL_2 that represents the coset in calG/G.  
// Each image should have determinant 1. We can ensure this because there is an isomorphism (calG meet SL2)/T -> calG/G.
// The other file GroupToCocycleForTwist actually has code for that but possibly slow. 
// G: group in the family (calG,T).
// T: G meet SL2
// N: N above. levels of G,T and calG should divide this number. For the remaining case, do we need them? If so I can code that as well.
// UN: Unitgroup of integers(N), which is the domain of realgamma. There are ofcourse ways I do no need to add these but you know, just doing trials here.
// Output: level of G_gamma and gens of G_gamma..
// UN needs to be defined there are issues here try all these. maybe can use the domain of xi? and use an isomorphism

//needto use gammadd kind of map for this xi. make it work.
}
    calG:=groupslist[1];  G:=groupslist[2]; T:=groupslist[3];
    N1,calG:=GL2Level(calG);
    N2,G:=GL2Level(G);
    N3,T:=SL2Level(T);
    assert N mod LCM([N1,N2,N3]) eq 0;
    "1";
    calG:=GL2Lift(calG,N);
    "2";
    G:=GL2Lift(G,N);
    "3";
    T:=SL2Lift(T,N);
    "4";
    Trans:=Transversal(G, T); 
    "5"; // Note: Could precompute this if it is slow. this is ofcourse isomorphic to the UN
    assert #Trans eq #UN;
    // The function xi: (Z/N)^* -> Gc maps each d to a matrix in Gc with determinant d.
    "6";
    txi:=map<{iotaN(d): d in UN}-> Parent([1]) | [<Determinant(t),[Integers()!a: a in Eltseq(t)]>: t in Trans]>;  // for each number give a matrix whose determinant is that
    // Note:  Could precompute this if it is slow.

    S:=Generators(UN);
    gens:=[];
    "7";
    for u in S do
        d:=Integers()!iotaN(u); 

        g:=GL(2,Integers(N))! txi(Integers(N)!d); // element of G mod N with determinant d
         
        h:=GL(2,Integers(N))!realgamma(d @@ iotaN); // David does this so it lies in SL2! PROBLEMMMMM! Okay I know how to create this thing for full determinant.
        g:=g*h;

        gens:=gens cat [g];
    end for;

    gens:= [SL(2,Integers(N))!g : g in Generators(T)] cat gens;

return N, gens;
end intrinsic; 