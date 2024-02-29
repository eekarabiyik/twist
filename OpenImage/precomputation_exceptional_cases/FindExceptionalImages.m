load "../main/FindOpenImage.m";

total_time:=Realtime();

exceptional_images:=[];

load "exceptional_image_unentangled_cases.m";
load "exceptional_image_entangled_cases.m";

load "exceptional_level_power_of_two.m";
load "exceptional_prime_level_borel.m";
load "exceptional_prime_level_misc.m";

J:={a[1]: a in exceptional_images};
assert #J eq #exceptional_images and J subset known_exceptional_jinvariants;
J0:=known_exceptional_jinvariants diff J;
assert {j: j in J0 | not FindAgreeableClosure(j)} eq {};


function NaiveGeneratorChoice(G)
    // G subgroup of SL(2,Z/N)
    N:=#BaseRing(G);
    gens:=[];

    repeat
        m:=Maximum([#sub<GL(2,Integers(N))| gens cat [a]> : a in G]);
        assert exists(b){b: b in G | #sub<GL(2,Integers(N))| gens cat [b]> eq m};
        gens:=gens cat [b];
        GG:=sub<GL(2,Integers(N))| gens>;
    until GG eq G;
    return GG;
end function;


exceptional_images1:=[];
for v in exceptional_images do 
    j:=v[1];
    j;
    a_invariants:=v[2];
    G:=v[3];
    index:=v[4];
    H:=v[5];

    H:=ChangeRing(H,Integers(sl2Level(H)));
    H:=NaiveGeneratorChoice(H);
    
    output:=[* j, a_invariants, #BaseRing(G), [Eltseq(g): g in Generators(G)], index, #BaseRing(H), [Eltseq(g): g in Generators(H)] *];
    exceptional_images1:=exceptional_images1 cat [output];
end for;


// We compute an additional group.  It is not needed to compute the image of Galois,
// its purpose is to help in the computation of its level.
for j in [1..#exceptional_images1] do
    v:=exceptional_images1[j];

    GE:=sub<GL(2,Integers(v[3])) | v[4]>;
    Hc:=sub<SL(2,Integers(v[6])) | v[7]>;

    N:=#BaseRing(Hc);
    N1:=&*[p^Valuation(v[3],p) : p in PrimeDivisors(N)];
    G:=ChangeRing(GE,Integers(N1));
    G:=AdjoinScalars(G);
    G:=ChangeRing(G,Integers(gl2Level(G)));
    assert IsAgreeable(G);

    N:=LCM(#BaseRing(G),#BaseRing(Hc));
    assert IsEven(N);        
    assert CommutatorSubgroup(gl2Lift(G,N)) eq sl2Lift(Hc,N);  
    
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
    
    if IsUnentangled(G) then
        BB:=[B: B in BB | IsUnentangled(B)];
        assert #BB ne 0;
    end if;

    levels:=[gl2Level(B): B in BB];
    _,i:=Minimum(levels); // will pick Gc with minimal level
    Gc:=BB[i];
    
    assert Gc meet SL(2,Integers(N)) eq Hc and Gc subset G;

    N1:=gl2Level(G);
    G:=ChangeRing(G,Integers(N1));
    gens1:=[ [Integers()!a: a in Eltseq(g)] :g in Generators(G)];

    N2:=gl2Level(Gc);
    Gc:=ChangeRing(Gc,Integers(gl2Level(Gc)));
    gens2:=[ [Integers()!a: a in Eltseq(g)] :g in Generators(Gc)];

    exceptional_images1[j]:=exceptional_images1[j] cat [* N1, gens1, N2, gens2 *];
end for;



// Write data to a file.
I:=Open("../data-files/exceptional_images.dat", "w");
for y in exceptional_images1 do
    WriteObject(I, y);
end for;

Realtime(total_time);
