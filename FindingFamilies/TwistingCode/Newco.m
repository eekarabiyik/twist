
intrinsic GroupToCocycle(calG::GrpMat, H::GrpMat, G::GrpMat, T::GrpMat, AOfMF::Assoc) -> HomGrp, FldNum, GrpPerm, Map
{
        Input:  calG: This is an open subgroup of GL2(Zhat), containing negative identity with full determinant.
                H: A representative in the family F(calG,G)=F(calG,B) for some B arising from our calculations. Check Zywina-Explicit Open Image-Chapter 14 for details.
                G: A group in the family F(calG,G). This will be the group we are trying to compute the modular curve of.
                T: SL2 intersection of H
                AOfMF: an associative array with keys the integers from 1 to the number of generators for the automorphism group of calG, and values the images of these elements as // TODO
                Note that G and H are in the reverse order from the prior version GroupToCocycle
        Output:
                xi: Gal(K/Q)-> GL(#M`F0,K) 1-cocycle arising from the map H-> calG/G
                K: a number field
                GAL1: the Galois group of Gal(K/Q) as an automorphism group
                sigma1: the map from GAL1 to the set of automorphisms of K
}
    //Arranging the levels
    time0:=Cputime();
    N1:=#BaseRing(calG);
    N3:=#BaseRing(H);
    calGAut:=GL2Lift(calG,LCM([N1,N3]));
    N:=LCM([N1,N3]);
    NG:=#BaseRing(G);
    "1";
    Cputime(time0);
    //When N divides NG everything is easier. Figureouthow to fix this
    if not IsDivisibleBy(NG,N) then
        G:=GL2Lift(G,LCM([NG,N]));
    end if;
    "2";
    Cputime(time0);
    H:=GL2Lift(H,N);
    NG:=#BaseRing(G);
    T:=SL2Intersection(G);//This is fast now.
    UNG,iotaN:=UnitGroup(Integers(NG));
    SL2:=SL2Ambient(NG);
    "3";
    Cputime(time0);
    //Forming the quotient calG/H. We have to make it into an abelian group so that the kernels actually work.

    //Defining the necessary quotient maps
    calG:=GL2Lift(calG,N);
    quocalG,quomapG:= quo<calG|H>;
    quocalGG,quomapGG:=AbelianGroup(quocalG);
    "untiltrans:";
    Cputime(time0);
    //Transversals are representatives from the cosets. Very useful for many things.
    K:=Transversal(G,T);
    "aftertrans";
    Cputime(time0);
    xi:=map<{iotaN(d): d in UNG}-> G | [<Determinant(t),G!([Integers()!a:a in Eltseq(t)])>: t in K]>;
    xii:=map<{iotaN(d): d in UNG}-> calG|[<Determinant(t),ChangeRing((xi(Determinant(t))),BaseRing(calG))>:t in K]>;
    "some maps";
    Cputime(time0);
    //Abelian work. gammadd here is an homomorphism whose kernel will be useful.
    gammad:=map<{iotaN(d): d in UNG}-> quocalGG | [<Determinant(t),quomapGG(quomapG((xii(Determinant(t)))))>: t in K]>;

    gammadd:=hom<UNG-> quocalGG | [gammad(iotaN(UNG.i)): i in [1..Ngens(UNG)]]>;// This is a homomorphism. With this new concept it is not a homomorphism anymore, is there a problem with the finite lift thing or something else. Would it be a homomorphism if I choose nice lifts? Do I need a lift hom with respect to codomain?
    "gamma formed";
    Cputime(time0);
    //Now we have some of the maps we needed. We will put all these in nice forms.

    //First we create Cyclotomic field and write the above maps from the Galois group.
    KNG<a>:=CyclotomicField(NG);
    "cyc formed";
    Cputime(time0);
    GAL,iota,sigma:=AutomorphismGroup(KNG);
    "field formed";
    Cputime(time0);
    genlist:=[];
    gallist:=[];
    for i in [1..Ngens(UNG)] do
        Append(~genlist,UNG.i);
        _:=exists(g0){g0: g0 in GAL | sigma(g0)(a) eq a^(Integers()!iotaN(UNG.i)) };//This should not be negative. There were some instances it were. Be careful!!!
        Append(~gallist,g0);
    end for;
    "exists stuff done";
    Cputime(time0);
    galiso:=hom<UNG->GAL | [gallist[i]: i in [1..Ngens(UNG)]]>;
    galisoa:=Inverse(galiso);
    xi1:=hom<GAL-> quocalGG | [gammadd(galisoa(GAL.i)): i in [1..Ngens(GAL)]]>;//This is the cocycleish
    "maps formed";
    Cputime(time0);
    //Now fine tuning stuff.
    Ker:=Kernel(xi1);
    Kfield:=FixedField(KNG,Ker);
    GAL1,iota1,sigma1:=AutomorphismGroup(Kfield);
    #GAL1;
    "fixed field computed";
    Cputime(time0);
    quogal,qmapgal:= quo<GAL|Ker>;
    bool,isomap:=IsIsomorphic(GAL1,quogal);
    "iso";
    Cputime(time0);
    xi2:=hom<GAL1-> calG | [<d,(gammadd(galisoa(isomap(d) @@ qmapgal)) @@ quomapGG)@@ quomapG>: d in GAL1]>;
    //This takes from the field of definition and gives matrices that can be put into autofmodularforms.
 
    //xi:=map<GAL1-> MatrixRing(Kfield,#M`F0) | [<d,AutomorphismOfModularForms(M,M`F0,xi2(d))>: d in GAL1]>;
    ro:=Nrows(AOfMF[1]);
    aut:=hom<calGAut ->GL(ro,Kfield) | [AOfMF[i]:i in [1..Ngens(calGAut)]]>;
    //aut:=lift_hom(aut1,N);

    xi:=hom<GAL1-> GL(ro,Kfield) | [<d,aut(xi2(d))>: d in GAL1]>;//Note that the way we did the precomputation makes the levels match.
    "end";
    Cputime(time0);

    //xi:=hom<GAL1-> GL(#M`F0,Kfield) | [<d,AutomorphismOfModularForms(M,M`F0,xi2(d))>: d in GAL1]>;

    return xi,Kfield,GAL1,sigma1;
end intrinsic;


