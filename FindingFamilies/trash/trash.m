   //xi:=map<{iotaN(d): d in UNG}-> G | [<Determinant(t),G!([Integers()!a:a in Eltseq(t)])>: t in K]>;
    //xii:=map<{iotaN(d): d in UNG}-> calG|[<Determinant(t),ChangeRing((xi(Determinant(t))),BaseRing(calG))>:t in K]>;
    //Abelian work. gammadd here is an homomorphism whose kernel will be useful.
    //gammad:=map<{iotaN(d): d in UNG}-> quocalGG | [<Determinant(t),quomapGG(quomapG((xii(Determinant(t)))))>: t in K]>;

    //gammadd:=hom<UNG-> quocalGG | [gammad(iotaN(UNG.i)): i in [1..Ngens(UNG)]]>;// This is a homomorphism. With this new concept it is not a homomorphism anymore, is there a problem with the finite lift thing or something else. Would it be a homomorphism if I choose nice lifts? Do I need a lift hom with respect to codomain?
    //Now we have some of the maps we needed. We will put all these in nice forms.

            //assert L subset KNG;//just find something for this please
        /*
        OO:=RingOfIntegers(X`KG);
        A:=ChangeRing(Matrix([Eltseq(KN!a): a in Basis(OO)]),Integers());
        A:=LLL(A:Proof:=false);

        X`KG_integral_basis_cyclotomic:=[KN!Eltseq(a): a in Rows(A)];
        X`KG_integral_basis:=[X`KG!a: a in X`KG_integral_basis_cyclotomic];
        */
    






    
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