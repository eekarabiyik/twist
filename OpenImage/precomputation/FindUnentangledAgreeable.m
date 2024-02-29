    /* 
        We find all the agreeable subgroups G of GL(2,Zhat), up to conjugacy, so that: 
            - G is the product of its ell-adic projections, i.e., no "entanglements",
            - X_G has genus at most 1,
            - X_G has a non-CM rational point,
            - X_H has infinitely many rational points for all subgroups H of GL(2,Zhat) that are strictly larger than G.

        For each G, we compute a model of X_G and compute the morphism from X_G to the j-line.   These are encoded by an
        associative array X which we save to file "unentangled.dat".
    */
    
    load "../main/GL2GroupTheory.m";        
    load "../main/ModularCurves.m";
    

    load "../SZ-data/GL2Invariants.m";         // Utility functions for working with subgroups of GL(2,Z/NZ)
    load "../SZ-data/RationalFunctions.m";     // Used to perform Cauchy interpolation of rational functions
    load "../SZ-data/JacobianRank.m";  // contains JacobianOfXG, used to determine genus one groups G for which Jac(X_G) has positive rank
    load "../SZ-data/g0groups.m";      // creates sl2tab and gl2tab populated with genus zero groups, here we add genus one groups
    load "../SZ-data/g1groups.m";

    /*  
        We have loaded "gl2tab" from the computations of Sutherland and Zywina.
        It is an associative array of all subgroups G of GL_2(Z_p) for some prime p, up to conjugacy, that have following properties:
            full determinant, contains -I, X_G has genus at most 1, X_G has real points, X_G has rational points if it has genus 0.
    */


    /*  
        Naming convention:
            Our groups G will given a label/key consisting of the sequence of labels from Sutherland-Zywina for the ell-adic projections 
            of G with ell in [2,3,5,7,11,13,17,19,37]
    */
        
    
    function ConstructGroup(a)
        /*  Input:
                a:  a sequence of groups with different prime power levels p^e given by labels from Sutherland-Zywina.
            Output:
                With N the product of the p^e, this function finds the largest subgroup of GL(2,Z/NZ) whose image modulo each p^e 
                is the presecribed group.  It returns N and a sequence of generators.
        */
        N:=&*[gl2tab[c]`gl2level : c in a];
        if N eq 1 then return 1, []; end if;

        G:=GL(2,Integers(N)); // start with full group and take intersections
        for c in [c: c in a | gl2tab[c]`gl2level ne 1] do
            N0:=gl2tab[c]`gl2level;
            gens0:=gl2tab[c]`gens;
            G0:=sub<GL(2,Integers(N0))|gens0>;
            G0:=gl2Lift(G0,N);
            G:=G meet G0;
        end for;
        return N, [Eltseq(g): g in Generators(G)];
    end function;

    function ContainsScalars0(a)
        /*  With conventions as in "ConstructGroup", finds the group G associated to a and check whether it contains
            all the scalar matrices.
        */
        N,gens:=ConstructGroup(a);
        if N eq 1 then return true; end if;    
        GL2:=GL(2,Integers(N));
        G:=sub<GL2|gens>;
        U,iota:=UnitGroup(Integers(N));
        return &and [ (GL2![iota(U.i),0,0,iota(U.i)]) in G : i in [1..Ngens(U)] ];
    end function;


    // Since we are looking for agreeable groups, we limit ourselves to those G that also contain the scalar matrices.
    keys0:={ k : k in Keys(gl2tab) | ContainsScalars0([k]) };

    // An element k in keys0, corresponds to a group G in GL(2,Z_p).  We define a set "allsup[k]" of those 
    // k' in keys0 that correspond to groups G', up to conjugacy, that are strictly larger than G.
    allsup:=AssociativeArray();
    allsup["1A0-1a"]:={};  // j-line case
    repeat
        keys:=[k: k in keys0 | {a: a in gl2tab[k]`msups} subset {a: a in Keys(allsup)}];
        for k in keys do
            allsup[k]:=&join{ allsup[c] join {c}: c in gl2tab[k]`msups};
        end for;
    until Keys(allsup) eq keys0;
    allsupeq:=AssociativeArray();
    for k in Keys(allsup) do allsupeq[k]:=allsup[k] join {k}; end for;


    P:=[2,3,5,7,11,13,17,19,37];  // The small primes we will keep track of.
    base:=["1A0-1a": p in P];     // label for the j-line

    total_time:=Realtime();

    // array for our modular curves
    X:=AssociativeArray();

    ToDo:={base};  // labels of modular curves we still need to address
    Done:={};      // labels already handled
    keys:=keys0;

    repeat
        // We first construct the set S of cases in "ToDo" that we can now address.

        S:={};
        for a in {a: a in ToDo} do 
            // before looking at the group with label a, we need to make sure we have handled any larger group
            C:=CartesianProduct( [allsupeq[k] : k in a] ); 
            C:= {[k:k in c]: c in C} diff {a};
            ToDo:=ToDo join (C diff Done);  // should include larger groups
            if C subset Done then   // if all larger groups already handled
                if exists{b: b in C | b in Keys(X) and X[b]`has_infinitely_many_points eq false}  or 
                   exists{b: b in C | b in Done and b notin Keys(X)}  then
                    // Do not need to deal with modular curves that factor through another modular curve with only finitely many points.
                    ToDo:=ToDo diff {a};   
                    Done:=Done join {a};
                else
                    S:=S join {a};
                end if;
            end if; 
        end for;
        
        for a in S do
            " "; 
            "a=",a;
            time0:=Realtime();
            ToDo:=ToDo diff {a};
            Done:=Done join {a};

            sl2level:=&*[gl2tab[k]`sl2level: k in a];
            index:=&*[gl2tab[k]`index: k in a];
            if [sl2level,index] notin low_genus then                
                continue a;  // Curve has genus > 1 so we will ignore it.
            end if;

            if sl2level ne 1 then
                N,gens:=ConstructGroup(a);
                G:=sub<GL(2,Integers(N))|gens>;
                if not HasLowGenus(G: sl2level:=sl2level, index:=index) then                     
                    continue a;  // Curve has genus > 1 so we will ignore it.
                end if;
            else
                N:=1;
                gens:=[];
            end if;
            
            // Initialize modular curve and assign it its label.
            M:=CreateModularCurveRec(N, gens);
            M`key:=a;

            is_agreeable:=IsAgreeable(M);
            assert is_agreeable; //check
            M`is_agreeable:=is_agreeable;  
            
            assert M`genus le 1;

            //"Genus=",M`genus;

            // Some ad hoc choices of precision for computations, i.e., how many terms we compute for our q-expansions.
            prec:=60;
            if N eq 11   then prec:=90; end if;
            if N eq 56   then prec:=90; end if;
            if N eq 49   then prec:=100; end if;
            if N ge 104 then prec:=100; end if;
            if a in {["2A0-8b", "9C0-9a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a"],
                    ["2A0-8a", "9B0-9a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a"],
                    ["2A0-8a", "9C0-9a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a"],
                    ["2C0-8a", "1A0-1a", "5B0-5a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a"],
                    ["4B0-4b", "9B0-9a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a"] } then
                prec:=80;
            end if;
            if a in {["2A0-8b", "9B0-9a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a"],
                    ["2C0-8b", "9B0-9a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a", "1A0-1a"]} then
                prec:=160;
            end if;

            is_serre_type:= N mod 2 eq 0 and #PrimeDivisors(N) gt 1 and gl2tab[a[1]]`index eq 2;
            if is_serre_type then prec:=80; end if;

            if not is_serre_type then
                // We compute a model for our modular curve via modular forms.
                M:=FindModelOfXG(M, prec); 

                // We check that it successfuly determined if the modular curve has a rational point or not.
                assert assigned M`has_point;    
            else
                // Special case where modular curve has even level and is a degree 2 cover of a modular curve with odd level.
                // These cases are the slowest using the previous approach.

                k0:=a; k0[1]:="1A0-1a";   
                // X[a]-> X[k0] has degree 2
                assert X[k0]`genus eq 0;  // should alway hold

                J:=MapTojLine(X,k0);
                M:=FindSerreTypeModel(X[k0],M,prec);
                M`key:=a;
            end if;            

            // We only care about modular curves with rational points!
            if M`has_point eq false then continue a; end if;
            
            // We now compute a morphism down to another already computed modular curve.  
            // The morphism is given by a label of the other curve and the map.   
            if M`N eq 1 then            
                M`pi:=[*[],[]*];    // j-line has no curve to map to.
            else
                // Find the label "b" of the curve to map to.
                S:=[];
                for i in [1..#a] do
                    b:=a;
                    for k in allsup[a[i]] do
                        b[i]:=k;
                        S:=S cat [b];
                    end for;
                end for;
                _,i:=Maximum([ &*[gl2tab[k]`index: k in b] :b in S]);
                b:=S[i];

                G:=M`G;
                GL2:=GL(2,Integers(M`N));
                // The label b gives a modular curve X_{G0}.  We can view G and G0 as subgroups of GL(2/NZ)
                if X[b]`N eq 1 then
                    G0:=GL2;
                else
                    G0:=gl2Lift(X[b]`G,M`N);
                end if;

                // G should be conjugate in GL2 to a subgroup G_ of G0.    
                assert exists(G_){H`subgroup : H in Subgroups(G0:OrderEqual:=#G) | IsConjugate(GL2,G,H`subgroup) };
                _,g:=IsConjugate(GL2,G,G_);
                
                phi:=FindMorphismBetweenModularCurves(M,X[b],g);
                M`pi:=[*b,phi,Eltseq(g)*];  
                
                // Some checks, may want to include g later if required.
                g:=[Integers()!a: a in Eltseq(g)];
                if X[b]`N eq 1 then
                    G_lower:=GL(2,Integers(M`N));
                else
                    G_lower:=gl2Lift(X[b]`G,M`N);
                end if;
                G_upper:=M`G;
                assert Conjugate(G_upper,GL(2,Integers(M`N))!g) subset G_lower;

            end if;

            X[a]:=M;  // Add the modular curve to our array (for now)    
            X[a]`map_to_jline:=[* MapTojLine(X,a) *];  // Morphism to j-line

            // Check if X[a] has a non-CM rational point.
            if X[a]`has_infinitely_many_points then
                X[a]`has_nonCM_point:=true;
            else
                // Case where modular curve has genus 1 and a finite number of rational points.
                // We map the rational points to the j-line and see if we get any j-invariants of non-CM elliptic curves.
                assert X[a]`has_point and X[a]`genus eq 1;            
                E:=X[a]`C; 
                A,f:=MordellWeilGroup(E);
                S:={f(a): a in A};
                
                J:=X[a]`map_to_jline[1];
                S:={J(P): P in S};
                S:={P[1]/P[2] : P in S | P[2] ne 0};  // remove cusp
                CM_jInvariants:={0, 54000, -12288000, 1728, 287496, -3375, 16581375, 8000, -32768, 
                    -884736, -884736000, -147197952000, -262537412640768000};
                S:={P: P in S | P notin CM_jInvariants};  // remove CM j-invariants
                X[a]`exceptional_jinvariants:=[j: j in S];
                X[a]`has_nonCM_point:=#X[a]`exceptional_jinvariants ne 0;
            end if;

            // Remove modular curve from list if the rational points are all cusps or CM points.
            if X[a]`has_nonCM_point eq false then
                Remove(~X, a);
                continue a;
            end if;
               

            // If the modular curve has infinitely many rational points, we need to consider smaller groups.  Add them to "ToDo".
            if X[a]`has_infinitely_many_points then
                for i in [1..#P] do
                    B:={k: k in keys | PrimeDivisors(gl2tab[k]`gl2level) eq [P[i]] and a[i] in gl2tab[k]`msups };
                    for b in B do
                        aa:=a;
                        aa[i]:=b;
                        ToDo:=ToDo join {aa};
                    end for;
                end for;                 
            end if;
        
            print "time=",Realtime(time0);
        end for;
        ToDo:=ToDo diff Done;  
        
    until ToDo eq {};


    //some extra steps to make saving to file easier (Magma currently doesn't like to save all data structures)
    for k in Keys(X) do
        delete X[k]`map_to_jline;

        // we are deleting these next two just to keep file sizes down.
        delete X[k]`F;
        delete X[k]`F0; 
    end for;


    Realtime(total_time);
    


    // Write modular curves found so far to a file.
    I:=Open("../data-files/agreeable.dat", "w");
    for k in Keys(X) do
        x:=X[k];
        WriteObject(I, x);
    end for;
