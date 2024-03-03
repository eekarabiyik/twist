/* 
    We find all the agreeable subgroups G of GL(2,Zhat), up to conjugacy, so that: 
        - X_G has genus at most 1,
        - X_G has a non-CM rational point,
        - X_H has infinitely many rational points for all subgroups H of GL(2,Zhat) that are strictly larger than G.
    For each G, we compute a model of X_G and compute the morphism from X_G to the j-line.   
    
    We also compute finitely many subgroup G of GL(2,Zhat) with X_G having genus at least 2 such that if H is an agreeable subgroup
    for which X_H(Q) has a non-CM point and X_H has genus at least 2, then one of the following hold:
        - H is conjugate to a subgroup of one of our G,
        - for some prime p, X_{H'} has genus at least 2 where H' is the subgroup of GL(2,Zhat) with p-power level that
          has the same p-adic projection as H.
        

    We start by loading the file "agreeable.dat", produced by "FindUnentangledAgreeable.m", which has computed all such modular curves of genus 
    at most 1 for G with the additonal property:
        - G is the product of its ell-adic projections, i.e., no "entanglements",     
    Our groups G are encoded by an associative array X which we save by updating "agreeable.dat".  


    Labeling convention:
        For our groups G, the products of the ell-adic projections will give a group already considered whose label is a sequence k;
        the label for G will be k with a unique positive integer adjoined to the end.
*/

load "../main/GL2GroupTheory.m";        
load "../main/ModularCurves.m";


// Load modular curves from "agreeable.dat" into associative array X.
I:=Open("../data-files/agreeable.dat", "r");
X:=AssociativeArray();
repeat
	b,y:=ReadObjectCheck(I);
	if b then
		X[y`key]:=y;
	end if;
until not b;
for k in Keys(X) do
    X[k]`map_to_jline:=[* MapTojLine(X,k) *];
end for;


total_time:=Realtime();

keys:=[k: k in Keys(X) | X[k]`has_infinitely_many_points];
_:=exists(base){k: k in Keys(X) | X[k]`N eq 1};  // "base" is the label of the j-line

for i in [1..#keys] do   
    k:=keys[i];
    print " "; k; 
    print "i=",i;

    // We shall look for agreeable groups so that the product of their ell-adic projections
    // is the subgroup of GL(2,Zhat) associated to X[k]
 
    label_count:=1;  // extra label parameter for those groups we wish to add to the array X

    S:=[];  // sequence for keeping track of groups up to conjugacy in GL(2,Zhat) we have seen.
    low_genus_rejects:=[* *];   // we keep track of groups G of genus 0 and 1 that we throw away because X_G(Q) has no non-CM point


    time0:=Realtime();

    todo:=[k];  // todo list containing labels we need to study
    repeat 
        b:=todo[1];  // next label to study
        Remove(~todo,1);

        // Compute the maximal agreeable subgroups of X[b]`G 
        time max:=  MaximalAgreeable(X[b]);
        "Number of max agreeable subgroups:",#max;

        for G in max do      

            // First ensure that G is a group not seen yet up to conjugacy.
            for G1 in S do
                N1:=#BaseRing(G1[1]);
                if N1 eq #BaseRing(G[1]) and IsConjugate(GL(2,Integers(N1)),G1[1],G[1]) then
                    continue G;
                end if;
            end for;
            S:=S cat [G];

            M:=CreateModularCurveRec0(G[1]);

            if GL2ContainsCC(M`G) eq false then 
                // Curve X_G has no real points and hence no rational points
                if M`genus le 1 then
                    low_genus_rejects:=low_genus_rejects cat [* M *];
                end if;
                continue G; 
            end if;  
       
            // check agreeability
            is_agreeable:=IsAgreeable(M);
            assert is_agreeable;
            M`is_agreeable:=is_agreeable;  


            if M`index / X[b]`index eq 6 and M`genus ge 2 then
                /* Let G1 and G0 be the agreeable subgroups of GL(2,Zhat) corresponding to M and X[b], respectively. 
                   In the case where [G0:G1]=6, we will find an intermediate subgroup G_new with [G_new:G1]=2; the
                   group G_new need not be agreeable.

                   In cases, where X_{G_new} has only finitely many rational points, we remember it and do not remember G1.
                   If X_{G_new} has infinitely many rational points, we include G_new with our groups and remember G1.
                */
                // We first find G_new.
                N0:=M`N;  
                G0:=gl2Lift(X[b]`G,N0);
                G1:=M`G;
                assert Index(G0,G1) eq 6;
                T,_:=RightTransversal(G0, G1); 
                for g in T do
                    G_new:=sub<GL(2,Integers(N0)) | Generators(G1) join {g}>;
                    if Index(G0,G_new) eq 2 then 
                        break g;
                    end if;
                end for;
                assert Index(G0,G_new) eq 2;
                assert IsAgreeable(G_new) eq false;


                N_new:=gl2Level(G_new);
                G_new:=ChangeRing(G_new,Integers(N_new));
                gens_new:=[Eltseq(a): a in Generators(G_new)];
                M_new:=CreateModularCurveRec(N_new, gens_new);
                M_new`is_agreeable:=false;
                
                M_old:=M;                  
                // remember the original group as M_old;  we will add it to X later if X_{G_new} has infinitely many rational points.
                M:=M_new;                
            end if;

            if M`genus ge 2 then
                M`pi:=[*b*];
                // Give our modular curve a new label; add a unique number to end of the label k.
                k_new:=k cat [IntegerToString(label_count)];
                label_count:=label_count+1;

                // add new modular curve to list
                X[k_new]:=M;
                X[k_new]`key:=k_new;                                
                continue G;
            end if;
            
            // Our modular curve X_G corresponding to M now has genus as most 1.


            // The following looks complicated, but it is only computing a boolean "serre_type" which will determine
            // which method we use to compute a model for our modular curve X_G.
            serre_type:=false;
            if IsEven(M`N) and #PrimeDivisors(M`N) gt 1 and M`is_agreeable then
                N1:=2^Valuation(M`N,2);
                N2:=M`N div N1;
                if ChangeRing(M`G,Integers(N1)) eq GL(2,Integers(N1)) then
                    GL2:=GL(2,Integers(N1));
                    rho:=hom<M`G->GL2 | [GL2!M`G.i: i in [1..Ngens(M`G)]]>;            
                    B2:=ChangeRing(Kernel(rho),Integers(N2));
                    G2:=ChangeRing(M`G,Integers(N2));
                    if Index(G2,B2) eq 2 then
                        G0:=G2;     
                        N0:=gl2Level(G0);
                        G0:=ChangeRing(G0,Integers(N0));
                        k0:=[k: k in Keys(X) | X[k]`N eq N0 and IsConjugate(GL(2,Integers(N0)),G0,X[k]`G)];
                        assert #k0 ne 0;
                        k0:=k0[1];
                        if X[k0]`genus eq 0 then
                            serre_type:=true;
                            assert G0 eq X[k0]`G;  // Should hold by how we are constructing groups
                        end if;
                    end if;
                end if;
            end if;

            // Make an ad hoc choice of "prec"; this specifies how many terms of q-expansions we compute.  If runtime
            // errors occur, we need to increase prec!
            prec:=60;  
            if k in { [ "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "13A0-13a", "1A0-1a", "1A0-1a", "1A0-1a" ],
                      [ "1A0-1a", "3A0-3a", "5B0-5a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a" ] } then
                prec:=120;
            end if;
            if k in { [ "1A0-1a", "9B0-9a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a" ] } then
                prec:=150;
            end if;
            if k in { [ "1A0-1a", "1A0-1a", "1A0-1a", "7B0-7a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a" ] } then
                prec:=100;
            end if;
            if k in { 
                      [ "1A0-1a", "1A0-1a", "1A0-1a", "7D0-7a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a" ],
                      [ "1A0-1a", "9C0-9a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a" ],
                      [ "2B0-2a", "1A0-1a", "5B0-5a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a" ] } then
                prec:=80;
            end if;
            if serre_type then
                prec:=60; 
            end if;

            // Compute a model of X_G
            if not serre_type then
                // Compute model of X_G using modular forms.
                M:=FindModelOfXG(M, prec);            
            else
                M:=FindSerreTypeModel(X[k0],M,prec); 
            end if;            

            // Check that from the model we were able to verify whether or not it has a rational point.
            assert assigned M`has_point;

            if M`has_point eq false then
                low_genus_rejects:=low_genus_rejects cat [*M*];
                continue G;
            end if;

            
            // Compute morphism down to previously computed modular curve
            phi:=FindMorphismBetweenModularCurves(M,X[b],[1,0,0,1]);
            M`pi:=[*b,phi*];

            // Check if modular curve has a non-CM rational point
            if M`has_infinitely_many_points then
                M`has_nonCM_point:=true;
            else
                // Case where modular curve has genus 1 and a finite number of rational points.
                // We map the rational points to the j-line and see if we get any j-invariants of non-CM elliptic curves.
                assert M`genus eq 1 and M`has_infinitely_many_points eq false;
                b:=M`pi[1];
                psi:=M`pi[2];
                phi:=map< M`C->X[b]`C | psi >;
                J:=MapTojLine(X,b);
                J:=phi*J;  // Morphism from M`C to j-line

                A,f:=MordellWeilGroup(M`C);
                S0:={f(a): a in A};
                S0:={J(P): P in S0};
                S0:={P[1]/P[2] : P in S0 | P[2] ne 0};  // remove cusp
                CM_jInvariants:={0, 54000, -12288000, 1728, 287496, -3375, 16581375, 8000, -32768, 
                    -884736, -884736000, -147197952000, -262537412640768000};
                S0:={P: P in S0 | P notin CM_jInvariants};  // remove CM j-invariants
                M`exceptional_jinvariants:=[j: j in S0];
                M`has_nonCM_point:=#M`exceptional_jinvariants ne 0;
            end if;

            if M`has_nonCM_point eq false then
                low_genus_rejects:=low_genus_rejects cat [*M*];
                continue G;
            end if;

            // Give modular curve a new label; add a unique number to end of the label k.
            k_new:=k cat [IntegerToString(label_count)];
            label_count:=label_count+1;

            // add new modular curve
            X[k_new]:=M;
            X[k_new]`key:=k_new;
            X[k_new]`map_to_jline:=[* MapTojLine(X,k_new) *];

            if X[k_new]`is_agreeable eq false and X[k_new]`has_infinitely_many_points eq true then                
                k1:=k cat [IntegerToString(label_count)];
                label_count:=label_count+1;

                X[k1]:=M_old;
                X[k1]`key:=k1;
                X[k1]`pi:=[*k_new*];
            end if;


            // When the modular curve has infinitely many rational points, we need to look for more agreeable subgroups;
            // we add it to our to-do list.
            if X[k_new]`has_infinitely_many_points and X[k_new]`is_agreeable then
                todo:=todo cat [k_new];
            end if;
        end for;

    until #todo eq 0;


    /*  The array X now has all the agreeable groups we need arising from the key k.  
        Unfortunately, we may have some redundant high genus cases.

        Consider a group G in our list for which X_G has genus at least 2.   Let G0 be the group that is the product
        of the ell-adic projections of G; the curve X_G0 will have infinitely many rational points.
    
        We want to remove any group G as above for which G is a proper subgroup of a subgroup G_ of G0 with
        X_{G_} having only finitely many rational points.
    */

    keys0:=[u: u in Keys(X) | [u[i]: i in [1..#k]] eq k and u ne k];  // labels for the groups we added associated to X[k].
    keys0:=[u: u in keys0 | X[u]`genus ge 2 or not X[u]`has_infinitely_many_points];

    for k1 in keys0 do
        N:=X[k1]`N;
        G:=X[k1]`G;

        if X[k]`N ne 1 then
            G0:=gl2Lift(X[k]`G,N);
        else    
            G0:=GL(2,Integers(N));
        end if;

        // We look at some agreeable groups G_ between G and G0.
        T:=[t: t in Transversal(G0,G) | t notin G];
        S:={G0,G};
        for t in T do
            G_:=sub<G0| Generators(G) join {t}>;  
            if G_ notin S and IsAgreeable(G_) then
                // G_ is an agreeable group between G and G0, and not equal to them, that we have not dealt with yet.
                // If X_{G_} has finitely many rational points, then G_ or a smaller group should have been found and 
                // we can remove the modular curve with label k1.    
                S:=S join {G_};
                g:=GL2Genus(G_);
                if g ge 2 then                
                    Remove(~X, k1);  // removal
                    continue k1;
                else
                    assert g le 1;
                    N_:=gl2Level(G_);
                    G_:=ChangeRing(G_,Integers(N_));
                    GL2:=GL(2,Integers(N_));
                    index:=Index(GL2,G_);
                
                    // Check if group G_ already occurs in X
                    keys_:=[u: u in Keys(X) | [u[i] : i in [1..#k]] eq k ];
                    keys_:=[u: u in keys_ | X[u]`genus eq g and X[u]`N eq N_ and X[u]`index eq index];
                    for u in keys_ do
                        if IsConjugate(GL2,G_,X[u]`G) then
                            if X[u]`has_infinitely_many_points then
                                continue t;
                            else
                                Remove(~X, k1);   // removal
                                continue k1;
                            end if;
                        end if;
                    end for;

                    // Finally, check if group G_ occurs in "low_genus_rejects"
                    for M in low_genus_rejects do 
                        if M`N eq N_ and M`index eq index and IsConjugate(GL2,G_,M`G) then
                            Remove(~X, k1);    // removal
                            continue k1;   
                        end if;
                    end for;

                end if;

            end if;
        end for;


    end for;

    print "time=",Realtime(time0);
end for;

Realtime(total_time);


// some extra steps that makes saving easier.
for k in Keys(X) do
    delete X[k]`map_to_jline;
    // we are deleting these next two just to keep file sizes down.
    delete X[k]`F;
    delete X[k]`F0;
end for;


// Write modular curves found so far to a file.
I:=Open("../data-files/agreeable.dat", "w");
for k in Keys(X) do
	x:=X[k];
	WriteObject(I, x);
end for;
