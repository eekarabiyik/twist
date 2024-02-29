/*
We load the modular curves from "agreeable.dat".

Consider any such modular curve M for which Gc:=M`Gc is defined.  Define G=M`G.
Lifting them to subgroups of GL(2,Zhat), G is agreeable and Gc is a subgroup of G with
full determinant and G meet SL(2,Zhat) = [G,G].
(The modular curve X_G will have infinitely many rational points.)


The sequence M`Gc_decomp consists of groups G_1,...,G_r.  Lifting the G_i to GL(2,Zhat), each
G_i lies between G and Gc and we have a natural isomorphism  G/Gc->G/G_1 x .... x G/G_r.  The quotient 
groups G/G_i are cyclic of prime power > 1.   
Also the sequence M`cyclic_generators consists of a choice of generator g_i for each cylic group G/G_i.


As discussed in the paper, there is a cover Y->X_G that has Galois group G/Gc.    
We construct a, possibly singular, model of Y that consists of equations of the form
    F(x_1,...x_m)= c_F
with F a homogeneous polynomial and c_F in Q(X_G).  What is nice is that with respect to this model, we 
will have a natural G/Gc action and an obvious map Y-> X_G.

The polynomials F we use depend on the cardinality of the cyclic group G/Gc and our choice is given in 
the file "cyclic_invariant_polynomials.m".

The following code computes appropriate c_F and records them as M`cyclic_models,
We update the file "agreeable.dat" afterwards.

*/



load "../main/GL2GroupTheory.m";        
load "../main/ModularCurves.m";

load "../data-files/cyclic_invariant_polynomials.m"; 

I:=Open("../data-files/agreeable.dat", "r");
X:=AssociativeArray();
repeat
	b,y:=ReadObjectCheck(I);
	if b then
		X[y`key]:=y;
	end if;
until not b;
for k in Keys(X) do
    if X[k]`genus le 1 then
        X[k]`map_to_jline:=[*MapTojLine(X,k)*];
    end if;
end for;

total_time:=Cputime();



keys:=[k: k in Keys(X) | assigned X[k]`Gc_decomp];

for k in keys do
    X[k]`cyclic_models:=[];

    for i in [1..#X[k]`Gc_decomp] do
        H:=X[k]`Gc_decomp[i];
        N:=#BaseRing(H);

        if X[k]`degree eq 1 then
            G:=GL(2,Integers(N));
        else
            G:=gl2Lift(X[k]`G,N);
        end if;
        ind:=Index(G,H);
        assert ind eq X[k]`cyclic_invariants[i];
        assert ind gt 1 and IsPrimePower(ind);
        ContainsMinusI:=G![-1,0,0,-1] in H;  // We will need to keep track of whether H contains -I.

        Q,iota:=quo<G|H>;
      
        " ";   "--------"; ind;

        g:=X[k]`cyclic_generators[i];
        assert Determinant(g) eq 1;
        assert sub<G|Generators(H) join {g}> eq G;

        if ContainsMinusI eq false then 
            wt:=3; 
        else
            wt:=2;  
        end if;

        prec:=60; // ad hoc precision, increase if needed
        if k[1] eq "32A0-32a" then prec:=80; end if;
        if ind eq 16 then prec:=70; end if;  

        M:=CreateModularCurveRec0(H);
        done:=false;
        repeat            
            repeat                
                time M:=FindModularForms(wt,M,prec);
                if M`dimMk eq 0 then
                    wt:=wt+2;
                end if;
            until M`dimMk ne 0;
        
            time C:=AutomorphismOfModularForms(M,M`F,g : wt:=wt);
            _,_,seq:=PrimaryRationalForm(C);
            
            assert Maximum([Degree(f[1]): f in seq]) eq EulerPhi(ind);

            R<t>:=PolynomialRing(Rationals());
            
            if R!CyclotomicPolynomial(ind) in {R!f[1]: f in seq} then
                if IsOdd(wt) or R!(t-1) in {R!f[1]: f in seq} then
                    done:=true;
                end if;
            end if;

            if not done then
                assert IsEven(wt);                
                wt:=wt+2;
            end if;            
        until done;     

        M0:=X[k];                
        if {R!p[1]: p in seq} eq {R!CyclotomicPolynomial(ind)} then
            F:=M`F;
        else
            D:=CompanionMatrix(CyclotomicPolynomial(ind));
            P:=&+[ Trace(D^i)*C^i : i in [0..(ind-1)] ];
            P:=Transpose(P);

            basis:=Basis(Image(P));
            basis:=[ LCM([Denominator(c): c in Eltseq(b)])*b  : b in basis];   // Make sure we have integers coordinates.
            basis:=[ Eltseq(b): b in basis];

            F:=[ [&+[b[i]*M`F[i][j]: i in [1..#M`F]]  : j in [1..M`vinf]] : b in basis];
        
                //CHECKS
                Cnew:=AutomorphismOfModularForms(M,F,g : wt:=wt);
                _,_,seq0:=PrimaryRationalForm(Cnew);
                assert {R!f[1]: f in seq0} eq {R!CyclotomicPolynomial(ind)};

            F:=SimplifyModularFormBasis(M,F);           
        end if;
        f:=F[1];
    

        if ContainsMinusI then  
            assert IsEven(wt);

            // Look for modular form fixed by g
            P:=&+[ C^i : i in [0..(ind-1)] ]; 
            P:=Transpose(P);       
            basis:=Basis(Image(P));
            basis:=[ LCM([Denominator(c): c in Eltseq(b)])*b  : b in basis];   // Make sure we have integers coordinates.
            basis:=[ Eltseq(b): b in basis];
            F_:=[ [&+[b[i]*M`F[i][j]: i in [1..#M`F]]  : j in [1..M`vinf]] : b in basis];
            F_:=SimplifyModularFormBasis(M,F_);
            assert #F_ ne 0;
            h:=F_[1];
                    // Check
                    h_check:=ConvertModularFormExpansions(M, M, g^i, h);
                    assert &and[IsWeaklyZero( h[j]-h_check[j]) : j in [1..M`vinf]];


            f:=[ f[j]/h[j]: j in [1..M`vinf]];
            f_conj:=[ConvertModularFormExpansions(M, M, g^i, f) : i in [0..EulerPhi(ind)-1]];

            psi:=inv_polynomials[ind][2];
            psi_eval:=[];
            for P in psi do
                h0:=[ Evaluate(P,[h[j]: h in f_conj]) : j in [1..M`vinf] ];
                h0:=ConvertModularFormExpansions(X[k], M, [1,0,0,1], h0);
                psi_eval:=psi_eval cat [h0];                
            end for;

            u:=1;
        else
            assert wt eq 3;
            M0:=FindModularForms(2,X[k],prec);
            if M0`dimMk ne 0 then
                h:=M0`F[1];
                h:=[a^3: a in h];
            else
                M0:=FindModularForms(6,X[k],prec);
                assert M`dimMk ne 0;
                h:=M0`F[1];
            end if;
    
            _<q1>:=LaurentSeriesRing(Rationals());
            E6:=[Eisenstein(6,q1+O(q1^100))];   
            assert exists(base){k: k in Keys(X) | X[k]`N eq 1};
            E6:=ConvertModularFormExpansions(X[k],X[base],[1,0,0,1],E6);

            r:=[h[j]/E6[j]: j in [1..X[k]`vinf]];
            if X[k]`genus eq 0 then
                K<t>:=FunctionField(Integers());
                u:= K!FindRelationRationalBruteForce(X[k],r);

                J0:=X[k]`map_to_jline[1];
                J:=Eltseq(J0([t,1]));
                J:=K!(J[1]/J[2]);                    
                u:=J*u;
            else
                K<x,y>:=FunctionField(X[k]`C);
                u:= K!FindRelationEllipticBruteForce(X[k],r);
                J0:=X[k]`map_to_jline[1];
                J:=Eltseq(J0([x,y,1]));
                J:=K!(J[1]/J[2]);                    
                u:=J*u;
            end if;

            f_conj:=[ConvertModularFormExpansions(M, M, g^i, f :wt:=wt) : i in [0..EulerPhi(ind)-1]];

            psi:=inv_polynomials[ind][2];

            psi_eval:=[];
            for P in psi do
                assert IsEven(Degree(P));
                h0:=[ Evaluate(P,[h[j]: h in f_conj]) : j in [1..M`vinf] ];
                h0:=ConvertModularFormExpansions(M0, M, [1,0,0,1], h0);
                h0:=[ h0[j]/h[j]^(Degree(P) div 2) : j in [1..M0`vinf]];   
                psi_eval:=psi_eval cat [h0];                
            end for;
        end if;

            //checks
            Cnew:=AutomorphismOfModularForms(M,f_conj,g : wt:=wt);
            //Cnew; CompanionMatrix(CyclotomicPolynomial(ind));
            C_expected:=Transpose(ChangeRing( (CompanionMatrix(CyclotomicPolynomial(ind))) , Rationals()));
            assert Cnew eq C_expected;


        cover:=[];
        for e in [1..#psi] do
            c:=psi_eval[e];
            if X[k]`genus eq 0 then  
                K<t>:=FunctionField(Rationals());                
                time cover:=cover cat [ K!FindRelationRationalBruteForce(X[k],c) * K!u^(Degree(psi[e]) div 2) ];
            else
                K<x,y>:=FunctionField(X[k]`C);
                time cover:=cover cat [ K!FindRelationEllipticBruteForce(X[k],c) * K!u^(Degree(psi[e]) div 2) ];
            end if;
        end for;
        
        // Simplify
        if X[k]`genus eq 0 then
            R<t>:=FunctionField(Integers());
            cover:=[R!f: f in cover];
            deg:=[Degree(P): P in psi];

            irred:={};
            for f in cover do
                irred:=irred join {g[1]: g in Factorization(Denominator(f))};
            end for;
            for pi in irred do
                e:=Maximum( [Ceiling(Maximum([-Valuation(cover[i],pi),0])/deg[i]) : i in [1..#psi] ] );
                cover:=[ cover[i]*pi^(deg[i]*e) : i in [1..#cover]];
            end for;
                
            irred:={};
            for f in cover do
                if f eq 0 then continue f; end if;
                irred:=irred join {g[1]: g in Factorization(Numerator(f))};
            end for;
            for pi in irred do
                e:=Minimum( [  Floor(Valuation(cover[i],pi)/deg[i]) : i in [1..#psi] ] );
                cover:=[ cover[i]/pi^(deg[i]*e) : i in [1..#cover]];
            end for;

            K<x>:=FunctionField(X[k]`C);
            cover:=[ Evaluate(f,x) : f in cover];
        end if;

        inv_polynomials[ind];
        cover;

        X[k]`cyclic_models:=X[k]`cyclic_models cat [cover];

    end for;
end for;


Cputime(total_time);


// some extra steps that makes saving easier/possible.
for k in Keys(X) do    
    if assigned X[k]`high_genus_model then
        b:=X[k]`pi[1];
        if X[b]`genus eq 0 then
            Pol<t>:=PolynomialRing(Rationals());
        else
            Pol<x,y,z>:=PolynomialRing(Rationals(),3);
        end if;
        X[k]`high_genus_model:=[Pol!a: a in X[k]`high_genus_model];
    end if;

    delete X[k]`map_to_jline;

    if assigned X[k]`cyclic_models and X[k]`genus eq 0 then
        F<t>:=FunctionField(Rationals());        
        X[k]`cyclic_models:=[ [F!f: f in b] : b in X[k]`cyclic_models];
    end if;

    if assigned X[k]`cyclic_models and X[k]`genus eq 1 then
        R<x,y,z>:=PolynomialRing(Rationals(),3);
        cyclic_models:=[];
        for b in X[k]`cyclic_models do
            c:=[];
            for f in b do
                phi:=ProjectiveRationalFunction(f);   
                c:=c cat[ [R!Numerator(phi),R!Denominator(phi)] ];
            end for;
            cyclic_models:=cyclic_models cat [c];
        end for; 
        X[k]`cyclic_models:=cyclic_models;
    end if;

end for;


// Write modular curves to a file.
I:=Open("../data-files/agreeable.dat", "w");
for k in Keys(X) do
	y:=X[k];
    WriteObject(I, y);
end for;
