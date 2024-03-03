/* 
    We start by loading an associative array X of modular curves from the file "agreeable.dat".

    For each modular curve X_G with genus at least 2, we compute a model defined over Q.  Each such modular curve 
    maps to a curve X_B where G is a maximal subgroup of B and X_B has infinitely many rational points.   Our model
    for X_G is given as minimal polynomial over Q(X_B) of some primitive element of the extension Q(X_G)/Q(X_B). 

    We save the updated associative array to the file "agreeable.dat".
*/

load "../main/GL2GroupTheory.m";        
load "../main/ModularCurves.m";

// Load limbs
I:=Open("../data-files/agreeable.dat", "r");
X:=AssociativeArray();
repeat
	b,y:=ReadObjectCheck(I);
	if b then
		X[y`key]:=y; 
	end if;
until not b;
for k in [k: k in Keys(X) | X[k]`genus le 1] do
    X[k]`map_to_jline:=[* MapTojLine(X,k) *];
end for;


total_time:=Realtime();


keys:=[k: k in Keys(X) | X[k]`genus ge 2];  // looking at modular curves of higher genus
keys:=Sort(keys);

for i in [1..#keys] do 
    k:=keys[i];
    b:=X[k]`pi[1];  
    // the modular curve X[k] maps down to the modular curve X[b] which has infinitely many points
    assert X[b]`genus le 1 and X[b]`has_infinitely_many_points;

    " ";
    print "i=",i;
    k;
    [X[k]`genus,X[k]`N];    

    index:=X[k]`index/X[b]`index;

    // Some ad hoc choices of precision for working with q-expansions.  
    prec:=50;
    if k[6] eq "13A0-13a" then prec:=100; end if;
    if k[3] eq "5A0-5a" and index gt 2 and X[k]`N ge 60 then prec:=80; end if;
    if k[3] eq "5A0-5a" and index ge 4 and X[k]`N ge 60 then prec:=120; end if;

    if k[2] eq "9C0-9a" and index eq 3 then prec:=80; end if;
    if k[1] in {"2B0-2a","2C0-8b","4B0-8a"} and k[2] eq "9B0-9a" and X[k]`N ge 72 then prec:=80; end if;
    if k[1] in {"4A0-4a"} and k[2] eq "9A0-9a" and X[k]`N ge 72 then prec:=100; end if;
    if k[1] in {"8B0-8a","8B0-8d"} and k[2] eq "3A0-3a" and X[k]`N ge 48 then prec:=80; end if;

    "prec=",prec;

    // We now compute a polynomial P so that the function field of X[k] is obtained from
    // the function field of X[b] by adjoining an element with minimimal polynomial P.

    // We covert P into a sequence arising from its coefficients (this is so Magma can handle it when we save to file).
    // See "FindCoverOfModularCurve" for more detail on its output.

    if X[b]`genus eq 0 then
        time flag,P:=FindCoverOfModularCurve(X[b],X[k],prec);        
        assert flag and IsIrreducible(P);

        Pol<t>:=PolynomialRing(Rationals());
        P0:=[ Pol!Coefficient(P,i): i in [0..Degree(P)] ];
    else
        R<x,y,z>:=PolynomialRing(Rationals(),3);
        time flag,P:=FindCoverOfModularCurve(X[b],X[k],prec : simplify_serre_type:=false);

        L:=FunctionField(X[b]`C);    
        c:=[ Coefficient(P,i) : i in [0..Degree(P)]];
        c:=[ ProjectiveRationalFunction(f) : f in c];
        P0:=&cat[ [ R!Numerator(f),R!Denominator(f)] : f in c ];
    end if;

    X[k]`high_genus_model:=P0;
    X[k]`is_serre_type_model:= not flag;

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


// Write modular curves with updated models to file
I:=Open("../data-files/agreeable.dat", "w");
for k in Keys(X) do
	x:=X[k];
    WriteObject(I, x);
end for;
