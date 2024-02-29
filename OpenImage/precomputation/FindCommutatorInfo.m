/* 
    We start by loading an associative array X of modular curves from the file "agreeable.dat".

    For those groups G in GL(2,Zhat) in the array with X_G of genus at most 1 and with infinitely many points, we compute
    the commutator subgroup [G,G] of G; it is an open subgroup of SL(2,Zhat).

    For these groups G in GL(2,Zhat), we also look at those which are maximal (up to conjugacy) with a given commutator subgroup.
    Now let G be one of these maximal groups.   We compute a normal subgroup Gc with full determinant so that the intersection
    of Gc with SL(2,Zhat) agrees with [G,G].  Note that G/Gc will be finite and abelian.   We then construct groups H_1,..,H_r lying between 
    Gc and G so that we have a natural isomorphism  G/Gc ->  G/H_1 x ... x G/H_r, where each group G/H_i is cylic of prime 
    power order.  We then update the file "agreeable.dat" with this data.

*/

load "../main/GL2GroupTheory.m";        
load "../main/ModularCurves.m";


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


total_time:=Realtime();


keys:=[k: k in Keys(X) | X[k]`genus le 1 and X[k]`has_infinitely_many_points and X[k]`is_agreeable];
T:=[X[k]`index: k in keys];
ParallelSort(~T,~keys);


// Each modular curve X[k], with k in "keys", corresponds to an open subgroup G of GL(2,Zhat).
// We now compute the commutator subgroup [G,G] in SL(2,Zhat).

for k in keys do
    if X[k]`degree ne 1 then 
        G:=X[k]`G; 
        if IsEven(X[k]`N) eq false then
            G:=gl2Lift(G,2*X[k]`N);
        end if;
    else
        G:=GL(2,Integers(2));  N:=2;
    end if;
    N0,gens0,ind0:=FindCommutatorSubgroup(G);  
    Hc:=sub<SL(2,Integers(N0)) | gens0>;   // gives the group [G,G]
    X[k]`commutator_index:=ind0; // index in SL(2,Zhat)

    // We look for a relatively small list of generators of Hc; this is done in a rather dumb way
    gens1:={};
    H:=sub<SL(2,Integers(N0)) | gens1>;
    while H ne Hc do
        m:=Maximum({#sub<SL(2,Integers(N0))|gens1 join {h}> : h in Hc | h notin H});
        assert exists(a){h: h in Hc | h notin H and #sub<SL(2,Integers(N0))|gens1 join {h}> eq m };
        gens1:=gens1 join {a};
        H:=sub<SL(2,Integers(N0)) | gens1>;
    end while;
    Hc:=H;
    X[k]`Hc:=Hc;

    gens1:=[ Eltseq(LiftMatrix(A,1)): A in gens1];
    gens1:= gens1 cat [[1,N0,0,1],[1,0,N0,1],[1-N0,-N0,N0,1+N0]];
    X[k]`Hc_gen:=gens1;
end for;


// For the subgroups G of GL(2,Zhat) coming from the modular curves with label in the sequence "keys",
// we check which are maximal, up to conjugacy, amongst those with the same commutator subgroup.
// Those that are not maximal, we call "extraneous".

for k in [k: k in Keys(X) | X[k]`genus le 1] do  
    // initialize
    X[k]`extraneous:=true; 
    X[k]`cover_with_same_commutator_subgroup:=k;
end for;

"Checking which groups are extraneous.";
keys0:=[]; // sequence for keeping track of non-extraneous cases.
for k in keys do
    extraneous:=false;
    // checking if there is a larger group in our list with the same commutator subgroup.
    for u in keys0 do
        if X[k]`commutator_index ne X[u]`commutator_index then continue u; end if;
        if X[k]`N mod X[u]`N ne 0 or X[k]`index mod X[u]`index ne 0 then continue u; end if;

        N1:=#BaseRing(X[k]`Hc); 
        N2:=#BaseRing(X[u]`Hc);
        if N1 ne N2 then continue u; end if;
        if IsConjugate( GL(2,Integers(N1)), X[k]`Hc, X[u]`Hc) eq false then continue u; end if;

        N:=X[k]`N;
        if X[u]`N eq 1 then G0:=GL(2,Integers(N)); else G0:=gl2Lift(X[u]`G,N); end if;

        HH:=[H`subgroup: H in Subgroups(G0:OrderEqual:=#X[k]`G)];
        if exists{H : H in HH | IsConjugate(GL(2,Integers(N)), H, X[k]`G)} then
            X[k]`cover_with_same_commutator_subgroup:=u;            
            extraneous:=true;
            break u;
        end if;
    end for;
        

    if extraneous eq false then 
        keys0:=keys0 cat [k]; 
        X[k]`extraneous:=extraneous;
    end if;
end for;

//   Choose open subgroup Gc of G with full determinant such that Gc meet SL(2,Zhat) eq [G,G]
"Choosing distinguished subgroups";
for k in keys0 do
    Hc:=X[k]`Hc;
    N:=LCM([X[k]`N,#BaseRing(Hc)]);  
    assert IsEven(N);    
    if X[k]`index eq 1 then 
        G:=GL(2,Integers(2));
    else
        G:=X[k]`G;
    end if;

    repeat
        Hc:=sl2Lift(Hc,N);
        G:=gl2Lift(G,N);

        A,iota:=quo<G|Hc>;
        UN,iotaN:=UnitGroup(Integers(N));
        detA:=hom<A->UN | [  Determinant(A.i @@ iota) @@ iotaN : i in [1..Ngens(A)]] >;

        BB:=[B`subgroup: B in NormalSubgroups(A:OrderEqual:=#UN)];
        BB:=[B : B in BB | detA(B) eq UN];
        BB:=[B @@ iota : B in BB];
        BB:=[B: B in BB | GL2DetIndex(B) eq 1];  // should be automatic!
        if #BB eq 0 then
            N:=2*N;  // will try again with higher level
        end if;        
    until #BB ne 0;
    if X[k]`is_entangled eq false then
        BB:=[B: B in BB | IsUnentangled(B)];
        assert #BB ne 0;
    end if;

    _,i:=Minimum([gl2Level(B): B in BB]); // will pick Gc with minimal level
    Gc:=BB[i];
    
    assert Gc meet SL(2,Integers(N)) eq Hc and Gc subset G;
    Gc:=ChangeRing(Gc,Integers(gl2Level(Gc)));
    X[k]`Gc:=Gc;  // save group Gc
end for;


"Computing decomposition into cyclic groups of prime power order";
for k in keys0 do
    Gc:=X[k]`Gc;

    N:=#BaseRing(Gc);
    if X[k]`degree eq 1 then
        G:=GL(2,Integers(N));
    else
        G:=gl2Lift(X[k]`G,N);
    end if;
    
    Q,iota:=quo<G|Gc>;
    
    ab_inv:=AbelianInvariants(AbelianGroup(Q));
    ab_inv:=&cat[ [p^Valuation(d,p): p in PrimeDivisors(d)] : d in ab_inv ];
    ab_inv:=Reverse(Sort(ab_inv));
    // Q=G/Gc is the direct product of groups Z/qZ with q in the sequence ab_inv.

    Gc_decomp:=[];
    cyclic_invariants:=[];
    
    Q0:=Q;
    for d in ab_inv do
        HH:=[H`subgroup: H in Subgroups(Q : OrderEqual:= #Q div d) ];
        HH:=[H : H in HH | IsCyclic(quo<Q|H>) ];
        HH:=[H : H in HH | Index(Q0,Q0 meet H) eq d];
        HH:=[H @@ iota : H in HH ];    assert #HH ne 0;

        // Want to consider groups that contain -I whenever possible!
        HH_:=[H : H in HH | G![-1,0,0,-1] in H];
        if #HH_ ne 0 then
            HH:=HH_;
        end if;

        // Try to make choices that give modular curves of small genus and level.
        // Current choosing minimal number of primes in level and then minimal level amongst those

        level:=[gl2Level(H): H in HH];
        m0:=Minimum(level);
        HH:=[ HH[i] : i in [1..#HH] | level[i] eq m0];

        genus:=[GL2Genus(H): H in HH];
        g:=Minimum(genus);
        HH:=[ HH[i] : i in [1..#HH] | genus[i] eq g];  

        index:=[#GL(2,BaseRing(HH[i]))/#HH[i] : i in [1..#HH] ];
        ind:=Minimum(index);
        HH:=[ HH[i] : i in [1..#HH] | index[i] eq ind];  


        H:=HH[1];
        Q0:=Q0 meet iota(H);

        Gc_decomp:=Gc_decomp cat [H];
        cyclic_invariants:=cyclic_invariants cat [d];
        
    
    end for;

    cyclic_generators:=[];
    for i in [1..#Gc_decomp] do
        H:=Gc_decomp[i];
        if G![-1,0,0,-1] notin H and Index(G,H) eq 2 then
            gen:=G![-1,0,0,-1];
        else
            assert exists(gen){g: g in G meet SL(2,BaseRing(G)) | sub<G|{g} join Generators(H)> eq G  
                and &and([g in Gc_decomp[j]: j in [1..#Gc_decomp] | j ne i] cat [true]) };
        end if;
        cyclic_generators:=cyclic_generators cat [gen];
    end for;

    X[k]`Gc_decomp:=Gc_decomp;
    X[k]`cyclic_invariants:=cyclic_invariants;
    X[k]`cyclic_generators:=cyclic_generators;

end for;

Realtime(total_time);


// some extra steps that makes saving easier.
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
    delete X[k]`F;
    delete X[k]`F0;
end for;

// Write modular curves to a file.
I:=Open("../data-files/agreeable.dat", "w");
for k in Keys(X) do
	x:=X[k];
    WriteObject(I, x);
end for;

