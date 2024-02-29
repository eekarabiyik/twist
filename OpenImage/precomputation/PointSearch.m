
load "../main/FindOpenImage.m";


// j-invariants of CM elliptic curves E/Q
CM_jInvariants:={0, 54000, -12288000, 1728, 287496, -3375, 16581375, 8000, -32768, -884736, -884736000, -147197952000, -262537412640768000};

// set will contain all exceptional j-invariants we find.
Jnew:={};
total_time:=Realtime();

// add known j-invariants arising from non-CM points on modular curves of prime power level
// (these are from the paper of Rouse-Sutherland-(Zureick-Brown))
    exceptionaljs := [
    <2, -2^18*3*5^3*13^3*41^3*107^3/17^16, 16, [[7,9,7,14], [5,6,1,11], [3,13,10,13]], "16.64.2.1">,
    <2, -2^21*3^3*5^3*7*13^3*23^3*41^3*179^3*409^3/79^16, 16, [[7,9,7,14], [5,6,1,11], [3,13,10,13]], "16.64.2.1">,
    <2, 257^3/2^8, 16, [[9,4,8,13], [9,1,6,5], [13,11,10,7]], "16.96.3.335">,
    <2, 17^3*241^3/2^4, 16, [[3,8,4,1], [9,2,0,15], [13,5,14,1]], "16.96.3.343">,
    <2, 2^4*17^3, 16, [[3,7,10,5], [13,11,10,13], [11,1,6,9]], "16.96.3.346">,
    <2, 2^11, 16, [[13,7,10,1], [5,15,2,15], [9,9,14,7]], "16.96.3.338">,
    <2, -3^3*5^3*47^3*1217^3/(2^8*31^8), 32, [[13,21,22,11], [1,29,22,31], [9,15,8,11], [7,18,0,19]], "32.96.3.230">,
    <2, 3^3*5^6*13^3*23^3*41^3/(2^16*31^4), 32, [[13,28,6,11], [7,31,22,25], [25,9,22,23], [21,16,18,23]], "32.96.3.82">,
    <5, 2^4*3^2*5^7*23^3, 25, [[19,22,4,0], [22,17,22,23]], "25.50.2.1">,
    <5, 2^12*3^3*5^7*29^3/7^5, 25, [[0,18,16,10], [1,20,20,18]], "25.75.2.1">,
    <7, 3^3*5*7^5/2^7, 7, [[0,1,1,0], [3,0,0,6]], "7.56.1.2">,
    <11, -11*131^3, 11, [[6,5,0,4], [1,7,0,10]], "11.60.1.3">,
    <11, -11^2, 11, [[6,8,0,8], [8,0,0,9]], "11.60.1.4">,
    <13, 2^4*5*13^4*17^3/3^13, 13, [[1,8,8,0], [7,6,0,9]], "13.91.3.2">,
    <13, -2^12*5^3*11*13^4/3^13, 13, [[1,8,8,0], [7,6,0,9]], "13.91.3.2">,
    <13, 2^18*3^3*13^4*127^3*139^3*157^3*283^3*929/(5^13*61^13), 13, [[1,8,8,0], [7,6,0,9]], "13.91.3.2">,
    <17, -17*373^3/2^17, 17, [[15,0,0,12], [8,13,0,12]], "17.72.1.2">,
    <17, -17^2*101^3/2, 17, [[14,9,0,9], [13,14,0,13]], "17.72.1.4">,
    <37, -7*11^3, 37, [[8,30,0,3], [27,18,0,18]], "37.114.4.1">,
    <37, -7*137^3*2083^3, 37, [[2,35,0,11], [2,36,0,6]], "37.114.4.2">
    ];
Jnew := Jnew join { r[2] : r in exceptionaljs };


" ";
"Step 1: Look at points of small height on genus 1 modular curves";

// We now check points of small height on modular curves of genus 1 with infinitely many points
keys1:=[k:k in Keys(X) | X[k]`genus eq 1 and X[k]`has_infinitely_many_points];

bound :=20;  // THIS QUANTITY CAN BE INCREASED TO LOOK FOR MORE POINTS (BUT IT TAKES LONGER)

for k in keys1 do
    k;
    jmap:=X[k]`map_to_jline[1];

    A,f:=MordellWeilGroup(X[k]`C);
    torsion:={f(a): a in TorsionSubgroup(A)};
    basis:=[f(A.i): i in [1..Ngens(A)]| Order(A.i) eq 0]; // basis of E(Q)/E(Q)_tors
    assert #basis eq Rank(X[k]`C);

    // we construct the points on the modular curve we will check        
    pts:={X[k]`C!0};
    for i in [1..#basis] do
        pts:={P+e*basis[i]: P in pts, e in [-bound..bound]};
    end for;
    pts:={P+t:P in pts, t in torsion};

    js:={jmap(P): P in pts};
    js:={j[1]/j[2]: j in js | j[2] ne 0} diff CM_jInvariants;
    for j in js do        
        b:=FindAgreeableClosure(j : assume_uniformity_conjecture:=true, use_exceptional_data:=false);
        if b eq false and j notin Jnew then
            //"Found point that needs to be considered separately", j;
            Jnew:=Jnew join {j};
        end if;
    end for;
end for;



// Check all points on modular curves of genus 1 with finitely many points!   This will add many j-invariants!
keys:=[k:k in Keys(X) | X[k]`genus eq 1 and X[k]`has_infinitely_many_points eq false];
for k in keys do
    A,f:=MordellWeilGroup(X[k]`C);
    assert Rank(X[k]`C) eq 0;
    jmap:=X[k]`map_to_jline[1];
    J:={jmap(f(a)) : a in A};
    J:={P[1]/P[2]: P in J | P[2] ne 0} diff CM_jInvariants;
    Jnew:=Jnew join J;
end for;


"Step 2: Look at points of small height on genus 0 modular curves";
// Check points of small height on modular curves of genus 0 with infinitely many points
keys0:=[k:k in Keys(X) | X[k]`genus eq 0 and X[k]`has_infinitely_many_points];
n:=15; // THIS QUANTITY CAN BE INCREASED TO LOOK FOR MORE POINTS (BUT IT TAKES LONGER)
low_height_pts_on_P1:={[a,b]: a in [-n..n], b in [1..n]} join {[1,0]};

for k in keys0 do
    k;
    jmap:=X[k]`map_to_jline[1];
    for P in low_height_pts_on_P1 do        
        j:=jmap(X[k]`C!P);
        if j[2] ne 0 and j[1]/j[2] notin CM_jInvariants then
            b:=FindAgreeableClosure(j[1]/j[2] : assume_uniformity_conjecture:=true, use_exceptional_data:=false);
            if b eq false then
                Jnew:=Jnew join {j[1]/j[2]};
            end if;            
        end if;

    end for;
end for;


"Step 3: Look for points of small height on some high genus modular curves that cover P1 (this can be slow depending on search space)";
keys:=[k: k in Keys(X) | X[k]`genus ge 2];  // looking at modular curves of higher genus
for k in keys do
	b:=X[k]`pi[1];
	if X[b]`genus ne 0 then continue k; end if;
	assert X[b]`has_infinitely_many_points;

    P0:=X[k]`high_genus_model;

    // First look at hyperelliptic curve case.
    if #P0 eq 3 then   
        assert P0[2] eq 0 and P0[3] eq 1;
        PolQ<t>:=PolynomialRing(Rationals());                
        f:=-PolQ!P0[1];
        assert IsSeparable(f);
        C:=HyperellipticCurve(f);
        
        // We first check if our modular curve has local points
        p:=0;
        repeat
            p:=NextPrime(p);
            if not IsLocallySolvable(C,p) then
                X[k]`has_nonCM_point:=false;  
                continue k;
            end if;
        until p+1 gt 2*X[k]`genus*Sqrt(p) and p gt Maximum(PrimeDivisors(X[k]`N));
            
        S:=Points(C: Bound:=10^5);  //10^5 // THIS QUANTITY CAN BE INCREASED TO LOOK FOR MORE POINTS (BUT IT TAKES LONGER)
        assert PointsAtInfinity(C) subset S;
       
        J:=X[b]`map_to_jline[1];
        S:={J([P[1],P[3]]): P in S};
        S:={P[1]/P[2]: P in S | P[2] ne 0 and P[1]/P[2] notin CM_jInvariants};
        Jnew:=Jnew join S;
    end if;

    // Curve X[k] not a degree 2 cover of X[b]
    if #P0 ne 3 then
        Polx<x>:=PolynomialRing(Rationals());
        Poly<y>:=PolynomialRing(Polx);
        f:=&+[Evaluate(P0[i],x)*y^(i-1)  : i in [1..#P0]];
        S:={[a[1],1]: a in Roots(Discriminant(f))} join {[1,0]};

        Pol2<x,y>:=PolynomialRing(Rationals(),2);
        f:=&+[Evaluate(P0[i],x)*y^(i-1)  : i in [1..#P0]];
        C:=Curve(AffineSpace(Rationals(),2),f);  
        
        if Genus(C) eq 6 then 
            continue k; 
            // We have one genus 6 curve whose plane model is too complicated to look for points with.
            // We separately computed its canonical model and only found two rational points;
            // they are singular points of our current model and have already been found.
        end if;
        
        pts:=PointSearch(C,10^5); // THIS QUANTITY CAN BE INCREASED TO LOOK FOR MORE POINTS (BUT IT TAKES LONGER)
        S:=S join {[P[1],1]: P in pts};

        S:={(X[b]`map_to_jline[1])(P): P in S};
        S:={P[1]/P[2]: P in S | P[2] ne 0 and P[1]/P[2] notin CM_jInvariants};
        S:=S diff Jnew;
        J0:=S;

        for j in S do
            E:=EllipticCurveWithjInvariant(j);
            E:=MinimalTwist(E);  // can replace with quadratic twist since -I is in all groups considered
            N:=X[k]`N;       
            for p in [p: p in PrimesUpTo(10000) | p notin BadPrimes(E) and N mod p ne 0] do
                a:=TraceOfFrobenius(E,p);
                if [Integers(N)!a,Integers(N)!p] notin X[k]`trdet then
                    J0:=J0 diff {j};
                    break p;
                end if;
            end for;
        end for;

        Jnew:=Jnew join J0;
    end if;

end for;
 
"Exceptional j-invariants found:",Jnew; " ";


"Step 4: Check that the singular points on our high genus models of modular curves do not hide rational non-CM points";
keys:=[k: k in Keys(X) | X[k]`genus ge 2];  

// First look at models over a genus 0 curve
for k in keys do
	b:=X[k]`pi[1];
	if X[b]`genus ne 0 then continue k; end if;

	assert X[b]`has_infinitely_many_points;
    assert X[k]`is_serre_type_model eq false;
    jmap:=X[b]`map_to_jline[1];

	L<t>:=PolynomialRing(Rationals());
    Pol<u>:=PolynomialRing(L);
	P0:=X[k]`high_genus_model;
    P:=&+[ (L!P0[i])*u^(i-1): i in [1..#P0]];  // model of X[k]   

    // j-invariants lying below questionable points of our model, i.e., 
    // evaluation model at t in Q, gives polynomial P in Q[u] that is inseparable or of 
    // smaller degree than expected
    J:=[ jmap([r[1],1]): r in Roots(L!(Discriminant(P))) cat Roots(L!LeadingCoefficient(P))];
    
    // also consider point at infinity
    if Degree(P) eq 2 then
        // Case where we have a nice hyperelliptic model
        assert Coefficient(P,1) eq 0 and IsMonic(P);
        f:=-Coefficient(P,0);
        assert IsSquarefree(f);
        C:=HyperellipticCurve(f);            
        if #PointsAtInfinity(C) ne 0 then
            J:=J cat [ jmap([1,0]) ];
        end if;
    else
        J:=J cat [ jmap([1,0]) ];
    end if;

    J:={j[1]/j[2]: j in J | j[2] ne 0} diff CM_jInvariants;

    // Looking at many small primes, we try to rule out rule rational points on our high genus 
    // model for j in J, by considering traces of Frobenius (to rule out the smaller Galois image this entails)
    J0:={};
    for j in J do
        E:=EllipticCurveWithjInvariant(j);
        E:=MinimalTwist(E);  // can replace with quadratic twist since -I is in all groups considered
        N:=X[k]`N;       
        for p in [p: p in PrimesUpTo(10000) | p notin BadPrimes(E) and N mod p ne 0] do
            a:=TraceOfFrobenius(E,p);
            if [Integers(N)!a,Integers(N)!p] notin X[k]`trdet then
                J0:=J0 join {j};
                break p;
            end if;
        end for;
    end for;

    J:=J diff J0;
    J:=J diff Jnew;
    if #J ne 0 then 
        "Found points that needs to be considered separately:", J; 
        // None occur, but if they did, they would need to be dealt with separately.    
        //Jnew:=Jnew join J;
    end if;
end for;

// Now looking at our modular curves of higher genus lying over an elliptic curve.
keys:=[k: k in Keys(X) | X[k]`genus ge 2];  
// Genus 1 base curve cases
for k in keys do
	b:=X[k]`pi[1];
	if X[b]`genus ne 1 then continue k; end if;

	assert X[b]`has_infinitely_many_points;
	L<x,y>:=FunctionField(X[b]`C);
	
	P0:=X[k]`high_genus_model;
	P0:=[ Evaluate(P0[2*i-1],[x,y,1])/Evaluate(P0[2*i],[x,y,1]) : i in [1..#P0 div 2] ];
	if  X[k]`is_serre_type_model then   
		assert #P0 eq 3 and P0[2] eq 0;
		J:=(X[b]`map_to_jline[1])([x,y,1]);
		J:=J[1]/J[2];
		P0[1]:=P0[1] * (J-1728);
	end if;
	Pol<u>:=PolynomialRing(L);
	P:=&+[ P0[i]*u^(i-1): i in [1..#P0]];  
    // model of X[k] given by P in L[u]=Q(x,y)[u]
	
    // find rational points p0 of genus 1 modular curve X[b] such that one of the coefficients of P has a pole at p0
    // or specializing P at p0 gives a separable polynomial in Q[u] of the same degree.
	Delta:=Discriminant(P);	
	support:={};
	support:=support join {RepresentativePoint(p0):p0 in Support(Divisor(Delta)) | Degree(p0) eq 1};
    support:=support join {RepresentativePoint(p0):p0 in Support(LeadingCoefficient(P)) | Degree(p0) eq 1};
    for c in [c: c in Coefficients(P) | c ne 0] do
        support0:=Support(Divisor(c));
        support:=support join {RepresentativePoint(p0) : p0 in support0 | Degree(p0) eq 1 and Valuation(c,p0) lt 0};
    end for;
    support:=support join {X[b]`C!0};

	for p0 in support do
		Q:=(X[b]`map_to_jline[1])(p0);
		if Q[2] eq 0 or Q[1]/Q[2] in CM_jInvariants then 
            continue p0; // only interested in non-CM points
        end if; 
        j:=Q[1]/Q[2];                
                
        // alter model so that it is hopefully now smooth at p0        
        pi:=UniformizingParameter(p0);
        P1:=P;
        deg:=Degree(P1);
        while Minimum([Valuation(c,p0): c in Coefficients(P1)]) lt 0 do                    
            P1:=Evaluate(P1,u/pi)*pi^deg;
        end while;
        while &and[ Valuation(Coefficient(P1,i),p0) ge deg-i   : i in [0..deg]] do
            P1:=Evaluate(P1,u*pi )/pi^deg;    
        end while;                            
        PolQ<w>:=PolynomialRing(Rationals());
        P1:=&+[ Evaluate(Coefficient(P1,i),p0) * w^i : i in [0..deg]];
        if IsSeparable(P1) eq false or HasRoot(P1) or Degree(P1) ne Degree(P) then
            if j notin Jnew then
                //Jnew:=Jnew join {j};
                "Found j-invariant that needs to be considered separately",j;
                // None occur, but if they did, they would need to be dealt with separately.
            end if;
        end if;
    end for;
end for;

" ";
"Step 5: For the cyclic covers we construct, keep track of any j-invariants where the cylic group does not act faithfully on the fibers.";

keys:=[k:k in Keys(X) | assigned X[k]`cyclic_models];
for k in keys do
    for i in [1..#X[k]`cyclic_models] do

        models:=X[k]`cyclic_models[i];
        if X[k]`genus eq 0 then
            Pol<t>:=PolynomialRing(Rationals());
            models:=[Evaluate(ProjectiveRationalFunction(f),[t,1]): f in models];            
            assert &and[Denominator(f) eq 1 : f in models];
            models:=[Pol!f: f in models];
            R:=[r[1]: r in Roots(GCD([Pol!Numerator(f): f in models]))];            
            J:={(X[k]`map_to_jline[1])([r,1]) : r in R};
            J:={j[1]/j[2]: j in J | j[2] ne 0} diff CM_jInvariants;
            J:=J diff Jnew;
            if J ne {} then
                "Found j-invariant(s) that needs to be considered separately", J;
                // None occur, but if they did, they would need to be dealt with separately.
            end if;
        elif X[k]`genus eq 1 then
            L<x,y>:=FunctionField(X[k]`C);
            //models_:=[Evaluate(f[1],[x,y,1])/Evaluate(f[2],[x,y,1]) : f in models];
            models_:=[L!f: f in models];
            assert &and[c ne 0: c in models_];
            S:=&meet[ {RepresentativePoint(p0): p0 in Support(Divisor(c)) | Degree(p0) eq 1 } : c in models_];
            J:={(X[k]`map_to_jline[1])(p0): p0 in S};
            J:={j[1]/j[2]: j in J | j[2] ne 0} diff CM_jInvariants;
            J:=J diff Jnew;
            if J ne {} then
                "Found j-invariant(s) that needs to be considered separately", J;
            end if;            

            S:=&join[ {RepresentativePoint(p0): p0 in Support(Divisor(c)) | Degree(p0) eq 1 and Valuation(c,p0) lt 0 } : c in models_];
            J:={(X[k]`map_to_jline[1])(p0): p0 in S};
            J:={j[1]/j[2]: j in J | j[2] ne 0} diff CM_jInvariants;
            J:=J diff Jnew;            
            if J ne {} then
                "Found j-invariant(s) that needs to be considered separately", J;
            end if;            
        end if;

    end for;
end for;

// Checks if all the exceptional j-invariants found have already been taken into account!
assert Jnew subset known_exceptional_jinvariants;

Realtime(total_time);


