//THIS IS THE MAIN ONE.



// This function takes a subgroup of GL(1,Integers(N)) and an instance of Q(zeta_N)
// and returns a simple representation of the corresponding subfield of
// Q(zeta_N), as well as a primitive element for the extension.
function fieldfind(G, K)
  N := Characteristic(BaseRing(G));
  z := K.1;
  nprim := N;
  if (N mod 4 eq 2) then
    z := z^2;
    nprim := (N div 2);
  end if;
  if (N mod 4 eq 0) then
    nprim := (N div 2);
  end if;
  prim := &+[ z^(k*(Integers()!g[1][1])) : k in Divisors(nprim), g in G];
  es := Eltseq(prim);
  es2 := [ Integers()!es[i] : i in [1..#es]];
  g := GCD(es2);
  if (g ne 0) then
    prim := prim/g;
  end if;
  minpoly := MinimalPolynomial(prim);
  assert Degree(minpoly) eq (EulerPhi(N)/#G);
  return NumberField(minpoly), prim;
end function;



intrinsic GroupToCocycleProj(calG::GrpMat, H::GrpMat, G::GrpMat, T::GrpMat, AOfMF::Assoc) -> HomGrp, FldNum, GrpPerm, Map
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
    //When N divides NG everything is easier. 
    if not IsDivisibleBy(NG,N) then
        G:=GL2Lift(G,LCM([NG,N]));
    end if;
    H:=GL2Lift(H,N);
    NG:=#BaseRing(G);
    //T:=SL2Intersection(G);//This is fast now.
    UNG,iotaN:=UnitGroup(Integers(NG));
    SL2:=SL2Ambient(NG);
    //Forming the quotient calG/H. We have to make it into an abelian group so that the kernels actually work.
    calG:=GL2Lift(calG,N);
    quocalG,quomapG:= quo<calG|H>;
    quocalGG,quomapGG:=AbelianGroup(quocalG);
    //To be able to form a transversal easily for G/T we use the GenericAbelianGroup feature. This allows us to use chosen generators and so newgammadd function can be defined.
    GUNG:=GenericAbelianGroup(UNG);
    AA:=sub<GUNG|[Determinant(g) @@ iotaN : g in Generators(G)]:UseUserGenerators:=true>;
    //newgammadd:=hom<AA->G | [<Determinant(g) @@ iotaN,g>: g in Generators(G)]>;
    newgammadd:=hom<AA->quocalGG | [<Determinant(g) @@ iotaN,quomapGG(quomapG(ChangeRing(g,BaseRing(calG))))>: g in Generators(G)]>;
    //This function is basically our cocycle.
    gammadd:=hom<UNG->quocalGG|[newgammadd(UNG.i): i in [1..Ngens(UNG)]]>;
    //First we create Cyclotomic field. Then find the fixed field coming from our homomorphism. Afterwards the cocycle is transformed into an honest galois cocycle via the cyclotomic character.
    GL1:=GL1Ambient(NG);
    KNG<z>:=NumberField(CyclotomicPolynomial(NG));
    kernell:=Kernel(gammadd);
    degneeded:=Index(UNG,kernell);
    kerrr:=sub<GL1|[[iotaN(kernell.i)]: i in [1..Ngens(kernell)]]>;
   if not GL1Order(kerrr) eq GL1Order(GL1) then 


        L,prim:=fieldfind(kerrr,KNG);
            //L<zz>:=L;
        L<zz>:=sub<KNG|[prim]>;
    //Find the Galois map via cyclotomic character.
    GAL,iota,sigma:=AutomorphismGroup(L);
    quotientgamma,quogammamap:=quo<UNG|kernell>;
    quogamma:=hom<quotientgamma->quocalGG| [gammadd(quotientgamma.i @@ quogammamap): i in [1..Ngens(quotientgamma)]]>;
    jj:=KNG!zz;
    listinho:=Eltseq(jj);
    genlist:=[];
    gallist:=[];
    for i in [1..Ngens(quotientgamma)] do
        exponento:=Integers()!iotaN(quotientgamma.i @@ quogammamap);
        a:=0;
        for j in [1..#listinho] do
            a:=a+listinho[j]*(z^((j-1)*exponento));
        end for;
        Append(~genlist,quotientgamma.i);
        //This is a brute force way. But it seems fast enough because the degree of the Galois group is uniformly bounded for our twists.
        _:=exists(g0){g0: g0 in GAL | sigma(g0)(zz) eq a };
        Append(~gallist,g0);
    end for;
    galiso:=hom<quotientgamma->GAL | [gallist[i]: i in [1..Ngens(quotientgamma)]]>;
    galisoa:=Inverse(galiso);
    xi1:=hom<GAL-> calG | [(quogamma(galisoa(GAL.i))@@ quomapGG) @@ quomapG: i in [1..Ngens(GAL)]]>;//This is the cocycleish/

    //This takes from the field of definition and gives matrices that can be put into autofmodularforms.

    else
    //Separately handle if the cocycle is the trivial map.  
      L:=Rationals();
      GAL,iota,sigma:=AutomorphismGroup(L);
      xi1:=hom<GAL->calG|[<g,Id(calG)>: g in GAL]>;
    end if;
    //Transform the cocycle into the form for H90. This uses how the matrices in calG acts on the space of modular forms.
    ro:=Nrows(AOfMF[1]);
    aut:=hom<calGAut ->GL(ro,L) | [AOfMF[i]:i in [1..Ngens(calGAut)]]>; //Be careful levels should match here.
    //aut:=lift_hom(aut1,N);
    xi:=hom<GAL-> GL(ro,L) | [<d,aut(xi1(d))>: d in GAL]>;//Note that the way we did the precomputation makes the levels match.
    return xi,L,GAL,sigma,UNG,kerrr,NG;
end intrinsic;

