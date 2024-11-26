
function FiniteLift(A,N,M) 
    assert IsDivisibleBy(M, N);
    if N eq M then return A; end if;
    GL2 := GL(2,Integers(M));
    M2 := MatrixRing(Integers(),2);
    m := &*[a[1]^a[2]: a in Factorization(M)| N mod a[1] eq 0];
    return GL2!CRT([M2!A, Identity(M2)], [m, M div m]);
end function;


function GroupToCocycleNew(calG,H,G,T,AOfMF)
    /*
        Input:  calG: This is an open subgroup of GL2(Zhat), containing negative identity with full determinant.
                H: A representative in the family F(calG,G)=F(calG,B) for some B arising from our calculations. Check Zywina-Explicit Open Image-Chapter 14 for details.
                G: A group in the family F(calG,G). This will be the group we are trying to compute the modular curve of. 
                T: SL2 intersection of H, and at the same time SL2Intersection(G)
                M: Modular curve of G.
                Note that G and H are switched here, notationwise
        Output: 
                xi: Gal(K/Q)-> GL(#M`F0,K) 1-cocycle arising from the map H-> calG/G
    */
    //Arranging the levels
    
    
    N1:=#BaseRing(calG);
    N3:=#BaseRing(H);
    calGAut:=GL2Lift(calG,LCM([N1,N3]));
    N:=LCM([N1,N3]);
    NG:=#BaseRing(G);
    if not IsDivisibleBy(NG,N) then
        G:=GL2Lift(G,LCM([NG,N]));
    end if;
    H:=GL2Lift(H,N);
    NG:=#BaseRing(G);
    
    T:=SL2Intersection(G);
    UNG,iotaN:=UnitGroup(Integers(NG));
    SL2:=SL2Ambient(NG);
    //Forming the quotient calG/G. We have to make it into an abelian group so that the kernels actually work.
    
    //Defining the necessary map like inclusions and so on.
    
    calG:=GL2Lift(calG,N);
    quocalG,quomapG:= quo<calG|H>;
    quocalGG,quomapGG:=AbelianGroup(quocalG);

    //Transversals are like representatives from the cosets. Very useful for many things.
    K:=Transversal(G,T);  
    xi:=map<{iotaN(d): d in UNG}-> G | [<Determinant(t),G!([Integers()!a:a in Eltseq(t)])>: t in K]>;
    xii:=map<{iotaN(d): d in UNG}-> calG|[<Determinant(t),ChangeRing((xi(Determinant(t))),BaseRing(calG))>:t in K]>;
   
    
    //Abelian work. gammadd here is an homomorphism whose kernel will be useful. 
    gammad:=map<{iotaN(d): d in UNG}-> quocalGG | [<Determinant(t),quomapGG(quomapG((xii(Determinant(t)))))>: t in K]>; //This gamma for now gives what? it gives in the quotient as  permutations 

    gammadd:=hom<UNG-> quocalGG | [gammad(iotaN(UNG.i)): i in [1..Ngens(UNG)]]>;// This is a homomorphism. With this new concept it is not a homomorphism anymore, is there a problem with the finite lift thing or something else. Would it be a homomorphism if I choose nice lifts? Do I need a lift hom with respect to codomain? 

    
    //These are only with quocalG. Migt be useful. map gamma gives matrices which can be useful to calculate the ambient automorphism matrices.
    //gammad1:=map<{iotaN(d): d in UN}-> quocalG | [<Determinant(t),quomapG(phi(xi(Determinant(t))))>: t in K]>; //This gamma for now gives what? it gives in the quotient as  permutations 
    //gammadd1:=hom<UN-> quocalG | [gammad1(iotaN(UN.i)): i in [1..Ngens(UN)]]>;// This is a homomorphism
    //gamma:=map<UN-> calG | [ <d,gammadd1(d) @@ quomapG>: d in UN]>;//this gives the matrices so that i can put the images into autofmodcurves

    //Now we have some of the maps we needed. We will put all these in nice forms. 
    KNG<a>:=CyclotomicField(NG);
    GAL,iota,sigma:=AutomorphismGroup(KNG);

    genlist:=[];
    gallist:=[];
    for i in [1..Ngens(UNG)] do
        Append(~genlist,UNG.i);
        _:=exists(g0){g0: g0 in GAL | sigma(g0)(a) eq a^(Integers()!iotaN(UNG.i)) };//This should not be negative. There were some instances it were. Be careful!!!
        Append(~gallist,g0);
    end for;

    galiso:=hom<UNG->GAL | [gallist[i]: i in [1..Ngens(UNG)]]>;
    galisoa:=Inverse(galiso);
    xi1:=hom<GAL-> quocalGG | [gammadd(galisoa(GAL.i)): i in [1..Ngens(GAL)]]>;//This is the cocycleish

    //Now fine tuning stuff.
    Ker:=Kernel(xi1);
    Kfield:=FixedField(KNG,Ker);
    GAL1,iota1,sigma1:=AutomorphismGroup(Kfield);
 

    quogal,qmapgal:= quo<GAL|Ker>;
    bool,isomap:=IsIsomorphic(GAL1,quogal);

    
    
    xi2:=hom<GAL1-> calG | [<d,(gammadd(galisoa(isomap(d) @@ qmapgal)) @@ quomapGG)@@ quomapG>: d in GAL1]>;
    //This takes from the field of definition and gives matrices that can be put into autofmodularforms.
       
    //xi:=map<GAL1-> MatrixRing(Kfield,#M`F0) | [<d,AutomorphismOfModularForms(M,M`F0,xi2(d))>: d in GAL1]>;
    ro:=Nrows(AOfMF[1]);
    aut:=hom<calGAut ->GL(ro,Kfield) | [AOfMF[i]:i in [1..Ngens(calGAut)]]>;
    //aut:=lift_hom(aut1,N);

    xi:=hom<GAL1-> GL(ro,Kfield) | [<d,aut(xi2(d))>: d in GAL1]>;



    //xi:=hom<GAL1-> GL(#M`F0,Kfield) | [<d,AutomorphismOfModularForms(M,M`F0,xi2(d))>: d in GAL1]>;



    return xi,Kfield,GAL1,sigma1;


end function;


