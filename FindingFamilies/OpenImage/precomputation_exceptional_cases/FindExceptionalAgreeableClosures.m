/*

    After a classification, there are a finite number of j-invariants of a non-CM E/Q left to consider.
    This code is for computing the agreeable closure of the image of rho_E^*.

    The data is saved to "../data-files/agreeable_closures_exceptional.dat"

*/

// nohup magma -t 36 "FindExceptionalAgreeableClosures.m" &

load "../main/FindOpenImage.m";

jinvariants:=[j: j in known_exceptional_jinvariants];
jinvariants:=Reverse(Sort(jinvariants));  // j-invariants we need to consider

ExceptionalImages:=AssociativeArray(); // array to keep track of agreeable closure

function OpenMaximalSubgroups(G)
    /*
        Input:  
            Let G be a subgroup of GL(2,Z/N) that has full determinant and contains the scalar matrices.

        By lifting, we can view G as a subgroup of GL(2,Z_N).

        Output:
            Sequence of the maximal subgroups M of G in GL(2,Z_N), up to conjugation in GL(2,Z_N), such that
                - M has full determinant and contains the scalar matrices,
                - M and G have same ell-adic projections for all ell dividing N

        Warning: this function is incredibly slow; that is why we don't use it for the main cases.
    */

    /* Idea behind function:  Assume N divisible by 4 if even.    Suppose M is one of the desired maximal subgroup
        of G.    Then M and G disagree modulo N*ell for some prime ell dividing N.
        [If M equals G modulo N*ell for all ell, then one shows that M contains all A in GL(2,Z_N) congruent to I modulo N]
        Moreover, one does not need to check the largest ell dividing N if it is at least 5.
    */

    max_subgroups:=[];  // sequence to keep tracks of maximal subgroups

    // Call our group G0 instead; need to make sure that its level is divisible by 4 if even.
    G0:=G;
    N0:=#BaseRing(G0);
    if N0 mod 4 eq 2 then
        N0:=N0*2;
        G0:=gl2Lift(G0,N0);
    end if;    
    
    ell_max:=Maximum(PrimeDivisors(N0));
    
    for ell in PrimeDivisors(N0) do
        if ell eq ell_max and ell_max ge 5 then 
            N:=N0;
        else
            N:=N0*ell;  
        end if;

        G:=gl2Lift(G0,N);
        PG,iota:=quo<G|Center(GL(2,Integers(N)))>;

        HH:=[ H`subgroup: H in MaximalSubgroups(PG)];
        HH:=[ H@@iota: H in HH];

        // Only want subgroups with full determinant and correct p-adic projections.
        for p in PrimeDivisors(N0) do
            Np:=p^Valuation(N,p);
            Gp:=ChangeRing(G,Integers(Np));
            HH:=[ H : H in HH | ChangeRing(H,Integers(Np)) eq Gp];
            HH:=[ H: H in HH | GL2DetIndex(H) eq 1];
        end for;

        max_subgroups:=max_subgroups cat HH;
    end for;

    max_subgroups:=[ ChangeRing(H,Integers(gl2Level(H))): H in max_subgroups];  // reduce groups mod their level

    // want to consider groups that are nonconjugate in GL(2,Z_N)
    groups:=[];
    for H in max_subgroups do
        b:= exists{H2: H2 in groups | #BaseRing(H) eq #BaseRing(H2) and IsConjugate(GL(2,BaseRing(H)),H,H2)};
        if not b then
            groups:=groups cat [H];
        end if;
    end for;

    return groups;
end function;


for j in jinvariants do
    "-------------------------------";
    "j=",j;

    b,k,G:=FindAgreeableClosure(j : use_exceptional_data:=false);  
    // NOTE: it is extremely vital to have "use_exceptional_data" set to false (otherwise we are computing from scratch)
    
    if b then  // Cases where we already know the agreeable closure
        G:=X[k]`G;
        assert IsAgreeable(G);
        // ExceptionalImages[j]:=G;    // do not need to keep track of.
        continue j;
    else
        ExceptionalImages[j]:=G;
    end if;

    // We start with a group G:=ExceptionalImages[j], viewed as an open subgroup of GL(2,Zhat) that
    // contains the scalars; it contains the image of rho_E^* for any non-CM elliptic curve E/Q with j-invariant j.
    // The group G has the additional property that its ell-adic projections agree with those of the image of 
    // rho_E^* with the scalar matrices adjoined.     
    
    // We now, up to conjugacy in GL(2,Zhat), construct open subgroup of G that contain the image of rho_E^* and
    // the scalars.   Once computed we can find then find the agreeable closure of the image of rho_E^*.

    groups:=[ExceptionalImages[j]];

    E:=EllipticCurveWithjInvariant(j);
    E:=MinimalTwist(E); 

    N:=#BaseRing(G);
    bad_primes:=Set(BadPrimes(E)) join {2,3} join Set(PrimeDivisors(N));

    repeat
        smaller_group_found:=false;
        
        G:=ExceptionalImages[j];  
        N:=#BaseRing(G);
        if IsOdd(N) then 
            G:=gl2Lift(G,2*N);  // we want to always consider the prime 2
        end if; 

        time subgroups:=OpenMaximalSubgroups(G);  // candidate subgroups of G (this might be very slow!)

        for H in subgroups do
            N_:=LCM(#BaseRing(H),#BaseRing(G));
            G_:=gl2Lift(G,N_);
            H_:=gl2Lift(H,N_);
            assert H_ subset G_;
            ConjH:=[C[3]: C in ConjugacyClasses(H_)];
            ConjG:=[C[3]: C in ConjugacyClasses(G_)];

            // pairs (tr(c),det(c)) mod N_ as c varies over all the elements of H
            trdet1:= { [Trace(c),Determinant(c)] : c in ConjH };
            
            // if H is a normal subgroup of G, then the set of 
            // pairs (tr(c),det(c)) mod N_ as c varies over all the elements of G not in H
            trdet2 := { [Trace(c),Determinant(c)] : c in ConjG | c notin H_ };
        
            p:=2;
            done:=false;
            splitting_primes:=[];
            while not done do
                repeat
                    p:=NextPrime(p);
                until p notin bad_primes;

                td:=[Integers(N_)!TraceOfFrobenius(E,p), Integers(N_)!p];
                if td notin trdet1 then   
                    // this means Frob_p not in H, which rules out H containing the image of Galois
                    done:=true;
                end if;

                if td notin trdet2 then  
                    // When H is normal in G, this means Frob_p is in H;
                    // we record this info.
                    splitting_primes:=splitting_primes cat [p];
                end if;
                

                if p ge 30000 and Index(G_,H_) eq 2 then
                    // In this case H_ is normal in G_ of index 2, and this gives rise
                    // to an extension K/Q of degree at most 2 that is unramified at primes p 
                    // for which E has good reduction and not dividing N_

                    // We have found a set "splitting_primes" of primes that will split in K.
                    // We can thus find all the possible fields K of degree at most 2.

                    // We have K=Q if and only if the image of Galois does lie in H_

                    dd:=&*PrimeDivisors(N_*&*BadPrimes(E));
                    D:={d: d in Divisors(dd) | d ne 1} join {-d: d in Divisors(dd)}; // squarefree integers except 1 dividing dd
                    D:=[* KroneckerCharacter(d): d in D *];
                    D:=[* chi: chi in D | &and[ chi(p) eq 1 : p in splitting_primes] *];

                    "Found smaller group";
                    smaller_group_found:=true;                                    
                    if #D ne 0 then  // When #D eq 0, we have provable showed that K=Q
                        "Warning: have candidate only; need to check directly", j;
                        // We have done these verifications as outlined in the paper.
                    end if;
            
                    G_new:=ChangeRing(H_,Integers(gl2Level(H_)));
                    ExceptionalImages[j]:=G_new;
                    
                    done:=true;
                    groups:=[ExceptionalImages[j]] cat groups;

                elif p ge 30000 then 
                    "===This case should not occur!===";
                    ExceptionalImages[j]; #ExceptionalImages[j];
                    assert false;  
                end if;
                
            end while;

        end for;

    until smaller_group_found eq false;

    groups:=[H: H in groups | IsAgreeable(H)];

    if #groups eq 0 then
        // This is the case where j is not exceptional at all!!
        // Some maximal agreeable subgroups of an agreeable group have index 6 and are contained in a unique index 2 subgroup
        // (which is not agreeable).   If j came from a non-CM point of the corresponding degree 2 cover of our original modular
        // curve we marked it as exceptional for checking.

        b,k,_:=FindAgreeableClosure(j : use_exceptional_data:=false);
        k1:=X[k]`pi[1]; 
        ExceptionalImages[j]:=X[k1]`G;

        assert not b and k in Keys(X) and X[k]`is_agreeable eq false;
        assert X[k]`degree/X[k1]`degree eq 2 and X[k1]`is_agreeable;
    else
        ind:=[#GL(2,BaseRing(H))/#H : H in groups];
        assert Reverse(Sort(ind)) eq ind;  // so largest value in ind will be first
        ExceptionalImages[j]:=groups[1];
    end if;

    GG:=ExceptionalImages[j];
    <j,#BaseRing(GG),[Eltseq(g): g in Generators(GG)]>;
end for;



// Now compute output for "FindAgreeableClosure" for exceptional j-invariants
S:=[];
for j in Keys(ExceptionalImages) do

	G:=ExceptionalImages[j];
	b,k,G0:=FindAgreeableClosure(j: use_exceptional_data:=false);
	assert not b;
	
	N:=LCM([#BaseRing(G),#BaseRing(G0)]);	
	G_:=gl2Lift(G,N);
	G0:=gl2Lift(G0,N);

	if #G0/#G_ lt 1  then 
        // case where j was not exceptional at all
		k1:=X[k]`pi[1];
        assert X[k]`is_agreeable eq false and X[k1]`is_agreeable;

        pts:=LiftQpoints(X[k1]`map_to_jline[1],{X[base]`C![j,1]});
        pts:={Eltseq(P): P in pts};
        tuple:=[* j,true,k1,pts *]; 
        tuple;
	else
        tuple:=[*j,false,k,ExceptionalImages[j]*];
    end if;

    S:=S cat [tuple];
end for;

// Write data to a file.
I:=Open("../data-files/agreeable_closures_exceptional.dat", "w");
for y in S do
    WriteObject(I, y);
end for;

