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
    //Transversals are representatives from the cosets. Very useful for many things. WROOOOOONG
    GUNG:=GenericAbelianGroup(UNG);
    AA:=sub<GUNG|[Determinant(g) @@ iotaN : g in Generators(G)]:UseUserGenerators:=true>;
    
    //newgammadd:=hom<AA->G | [<Determinant(g) @@ iotaN,g>: g in Generators(G)]>;
    newgammadd:=hom<AA->quocalGG | [<Determinant(g) @@ iotaN,quomapGG(quomapG(ChangeRing(g,BaseRing(calG))))>: g in Generators(G)]>;
    gammadd:=hom<UNG->quocalGG|[newgammadd(UNG.i): i in [1..Ngens(UNG)]]>;
    "aftertrans";
    Cputime(time0);
    //xi:=map<{iotaN(d): d in UNG}-> G | [<Determinant(t),G!([Integers()!a:a in Eltseq(t)])>: t in K]>;
    //xii:=map<{iotaN(d): d in UNG}-> calG|[<Determinant(t),ChangeRing((xi(Determinant(t))),BaseRing(calG))>:t in K]>;
    "some maps";
    Cputime(time0);
    //Abelian work. gammadd here is an homomorphism whose kernel will be useful.
    //gammad:=map<{iotaN(d): d in UNG}-> quocalGG | [<Determinant(t),quomapGG(quomapG((xii(Determinant(t)))))>: t in K]>;

    //gammadd:=hom<UNG-> quocalGG | [gammad(iotaN(UNG.i)): i in [1..Ngens(UNG)]]>;// This is a homomorphism. With this new concept it is not a homomorphism anymore, is there a problem with the finite lift thing or something else. Would it be a homomorphism if I choose nice lifts? Do I need a lift hom with respect to codomain?
    "gamma formed";
    Cputime(time0);
    //Now we have some of the maps we needed. We will put all these in nice forms.

    //First we create Cyclotomic field and write the above maps from the Galois group.
    GL1:=GL1Ambient(NG);
    //KNG<z>:=CyclotomicField(NG);
    KNG<z>:=NumberField(CyclotomicPolynomial(NG));
    kernell:=Kernel(gammadd);
    degneeded:=Index(UNG,kernell);
    kerrr:=sub<GL1|[[iotaN(kernell.i)]: i in [1..Ngens(kernell)]]>;
    "order of kerr";
    GL1Order(kerrr);
  if not GL1Order(kerrr) eq GL1Order(GL1) then 


    /*
        TT:=[Integers()!iotaN(u): u in kernell];
        L:=sub<KNG|[KNG!1]>;
        i:=0;
        while Degree(L) lt degneeded do
            i:=i+1;
            print(i);
            a:=&+[ Conjugate(z^i,t): t in TT ]; // will lie in K_G
            print(a);
            "summed";
            L:=sub<KNG| Generators(L) cat [a]>;
        end while;
          L:=OptimizedRepresentation(L); //improve presentation of field        
        */
            "computing the fixed field";
        L,prim:=fieldfind(kerrr,KNG);
            "computed";
            "field is";
            //L<zz>:=L;
            L<zz>:=sub<KNG|[prim]>;

            //assert L subset KNG;//just find something for this please
      Cputime(time0);
      "find prim and check containment"; 
        //assert L subset KNG;
        Cputime(time0);
        /*
        OO:=RingOfIntegers(X`KG);
        A:=ChangeRing(Matrix([Eltseq(KN!a): a in Basis(OO)]),Integers());
        A:=LLL(A:Proof:=false);

        X`KG_integral_basis_cyclotomic:=[KN!Eltseq(a): a in Rows(A)];
        X`KG_integral_basis:=[X`KG!a: a in X`KG_integral_basis_cyclotomic];
        */







    "Auto and mops start";
    Cputime(time0);
    
    GAL,iota,sigma:=AutomorphismGroup(L);
    quotientgamma,quogammamap:=quo<UNG|kernell>;
    quogamma:=hom<quotientgamma->quocalGG| [gammadd(quotientgamma.i @@ quogammamap): i in [1..Ngens(quotientgamma)]]>;
    jj:=KNG!zz;
    listinho:=Eltseq(jj);
    "auto maps done";
    Cputime(time0);
//Burayakadargeldik

    "field formed";
    Cputime(time0);
    genlist:=[];
    gallist:=[];
    for i in [1..Ngens(quotientgamma)] do
        exponento:=Integers()!iotaN(quotientgamma.i @@ quogammamap);
        a:=0;
        for j in [1..#listinho] do
            a:=a+listinho[j]*(z^((j-1)*exponento));
        end for;
        Append(~genlist,quotientgamma.i);
        _:=exists(g0){g0: g0 in GAL | sigma(g0)(zz) eq a };//This should not be negative. There were some instances it were. Be careful!!!
        Append(~gallist,g0);
    end for;
    "exists stuff done";
      Cputime(time0);
    galiso:=hom<quotientgamma->GAL | [gallist[i]: i in [1..Ngens(quotientgamma)]]>;
    galisoa:=Inverse(galiso);
    xi1:=hom<GAL-> calG | [(quogamma(galisoa(GAL.i))@@ quomapGG) @@ quomapG: i in [1..Ngens(GAL)]]>;//This is the cocycleish

    //This takes from the field of definition and gives matrices that can be put into autofmodularforms.
 
    //xi:=map<GAL1-> MatrixRing(Kfield,#M`F0) | [<d,AutomorphismOfModularForms(M,M`F0,xi2(d))>: d in GAL1]>;
    else
      L:=Rationals();
      GAL,iota,sigma:=AutomorphismGroup(L);
      xi1:=hom<GAL->calG|[<g,Id(calG)>: g in GAL]>;
    end if;
    
    
    ro:=Nrows(AOfMF[1]);
    aut:=hom<calGAut ->GL(ro,L) | [AOfMF[i]:i in [1..Ngens(calGAut)]]>; //Be careful levels should match here.
    //aut:=lift_hom(aut1,N);

    xi:=hom<GAL-> GL(ro,L) | [<d,aut(xi1(d))>: d in GAL]>;//Note that the way we did the precomputation makes the levels match.
    "end";
    Cputime(time0);

    //xi:=hom<GAL1-> GL(#M`F0,Kfield) | [<d,AutomorphismOfModularForms(M,M`F0,xi2(d))>: d in GAL1]>;

    return xi,L,GAL,sigma;
end intrinsic;

