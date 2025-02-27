//AttachSpec("../Modular/EarlierCode/magma.spec");   // Andrew Sutherland's group theory package

// load Cummins-Pauli data for congruence subgroups of genus at most 24  
filename:="../Modular/CPdata/CPdata.dat";  
I:=Open(filename, "r"); 
_,cp_data:=ReadObjectCheck(I); 

/*  
    The following is the list of all congruence subgroups of SL(2,Z), up to conjugacy in GL(2,Z),
    that contain -I, have genus at least 3, and have gonality 2.  They are given by their 
    Cummins-Pauli label.  Congruence subgroups of genus 1 and 2 always have gonality 2.
*/
gonality_equals_2:=[ "8B3", "10B3", "12C3", "12D3", "12E3", "12F3", "12G3", "12H3", "12K3", 
    "12L3", "14A3", "14C3", "14F3", "15F3", "15G3", "16B3", "16C3", "16D3", "16E3", "16F3", 
    "16I3", "16J3", "16M3", "16S3", "18A3", "18C3", "18F3", "18G3", "20C3", "20F3", "20G3", 
    "20H3", "20I3", "20J3", "20M3", "20O3", "21A3", "21B3", "21D3", "24A3", "24B3", "24C3", 
    "24G3", "24I3", "24K3", "24L3", "24M3", "24S3", "24U3", "24V3", "24W3", "28C3", "28E3", 
    "30B3", "30G3", "30J3", "30K3", "30L3", "32B3", "32C3", "32D3", "32H3", "32K3", "32M3", 
    "33C3", "34B3", "35A3", "36E3", "36F3", "36G3", "39A3", "40D3", "40E3", "40F3", "40I3", 
    "41A3", "42E3", "48C3", "48E3", "48F3", "48H3", "48I3", "48J3", "48M3", "50A3", "54A3", 
    "60C3", "60D3", "64A3", "96A3", "18B4", "25A4", "25D4", "32B4", "36C4", "42A4", "44B4", 
    "47A4", "48C4", "50A4", "50D4", "10A5", "14C5", "16G5", "18A5", "24A5", "24D5", "26A5", 
    "30C5", "30F5", "36A5", "36B5", "36H5", "40A5", "42A5", "44B5", "45A5", "45C5", "46A5", 
    "48A5", "48E5", "48F5", "48G5", "48H5", "50A5", "50D5", "50F5", "52B5", "54A5", "57A5", 
    "58A5", "59A5", "60A5", "96A5", "48A6", "71A6", "32E7", "48N7", "56B7", "64D7", "82B7", 
    "96A7", "93A8", "50A9", "50D9", "96B9", "48B11", "72A11", "96B11"];

/*  
    The following is the list of all congruence subgroups of SL(2,Z), up to conjugacy in GL(2,Z),
    that contain -I, have genus at least 5, and have gonality 3.  They are given by their 
    Cummins-Pauli label.  Congruence subgroups of genus 3 and 4 that do not have gonality 2
    have gonality 3.
*/
gonality_equals_3:=[ "54C5", "16A6", "18A6", "18D6", "24D6", "27A6", "28D6", "28E6", 
    "30C6", "32A6", "36C6", "36H6", "36J6", "36K6", "39A6", "45D6", "54A6", "54B6", "56D6", 
    "64A6", "84A6", "108A6", "27B7", "27C7", "30D7", "42M7", "24A8", "24B8", "36H8", "36I8", 
    "36J8", "36K8", "48A8", "48C8", "48E8", "72F8", "72G8", "84A8", "96A8", "108A8", "108B8", 
    "144A8", "15A10", "36A10", "36C10", "42G10", "72A10", "75A10", "108A10", "108C10", "108A12"];

/*  
    The following is the list of all congruence subgroups of SL(2,Z), up to conjugacy in GL(2,Z),
    that contain -I and for which the canonical model is isomorphic to a smooth plane quinitic. 
    They are given by their Cummins-Pauli label.  
*/
smooth_plane_quintic:=["75A6","75D6"];


/*
    A record of type "ModularCurveRec" encodes information about the curve X_G where G is a subgroup of GL(2,Z/NZ).   
    The curve X_G is smooth, projective and geometrically irreducible, and defined over the number field K_G=Q(zeta_N)^det(G).
*/

ModularCurveRec := recformat<
    G, H :GrpMat,  

    N, index, degree, det_index, genus, v2, v3, vinf, sl2level, gl2level, k, dimMk, dimSk :RngIntElt,   

    cusps, widths, regular, cusp_orbits, cusp_to_orbit, F, F0,  psi, mult, prec, prec_sturm, modular_form_data :SeqEnum,  

    has_neg_one,  is_unentangled: BoolElt,                                                              
      
    model_degree : RngIntElt,  //write description

    KG: FldNum, 
    KG_degree: RngIntElt,
    KG_integral_basis, KG_integral_basis_cyclotomic    : SeqEnum,

    conversion_matrices: List,

    CPname :MonStgElt,

    Gm_mod_H, Gm_mod_H_pairs, Gm_mod_H_det, cosets_det : SeqEnum,


    // The below entries are currently unused and should be pruned.
    C:Crv, 
    map_to_jline, pi :List,
    has_point, has_infinitely_many_points, has_nonCM_point,is_agreeable,extraneous, is_serre_type_model :BoolElt,
    commutator_index, f, trdet, pts :RngIntElt,   
    key,gens, exceptional_jinvariants, Gc_decomp, high_genus_model, cyclic_invariants, cyclic_models, cyclic_generators, cover_with_same_commutator_subgroup : SeqEnum,
    Hc, Gc, Hc_gen :GrpMat
>;	 

/*                            
 DESCRIPTION OF SOME OF THE ENTRIES:
    _______________________________________________________
    
    G           : A subgroup of GL(2,Z/NZ). We will sometimes view it as an open subgroup of GL(2,Zhat).
                    We will usually adjust G so that N is its level.
    N           : The above integer N.
    index       : Index of G in GL(2,Z/NZ).
    det_index   : Index of det(G) in the unit group of Z/NZ.
    H           : The intersection of G with SL(2,Z/NZ) which we can view as an open subgroup of SL(2,Zhat).
                    The group H will be given modulo its level in SL(2,Zhat).
    gl2level    : The level of G viewed as a subgroup of GL(2,Zhat)
    sl2level    : The level of H viewed as a subgroup of SL(2,Zhat).
    has_neg_one : Boolean that is true when G contains -I.
    KG          : The number field Q(zeta_N)^det(G).
    KG_degree   : Degree of KG over Q.
    KG_integral_basis               : An integral basis of KG.
    KG_integral_basis_cyclotomic    : The same integral basis given in Q(zeta_N).

    is_unentangled : Boolean that is true if G is "unentangled", i.e, as a subgroup of GL(2,Zhat) is the 
                        direct product of its p-adic projections.
    _______________________________________________________

    Let X_Gamma:=Gamma\H^* be the smooth compact Riemann surface, where Gamma=Gamma_G is the congruence subgroup of SL_2(Z)
    consisting of matrices whose image modulo N lie in G.  We can identify the complex points X_G(C) with X_Gamma.

    genus       : Genus of X_G.

    v2          : Number of elliptic points of order 2 for X_Gamma.
    v3          : Number of elliptic points of order 3 for X_Gamma.
    vinf        : Number of cusps of X_Gamma.
    degree      : Index of \pm Gamma in SL(2,ZZ). 
    
    cusps       : A sequence of matrices A in SL(2,Z) so that A*infty represent the cusps of X_Gamma.
    regular     : A sequence of booleans (ordered the same as "cusps") indicating whether the corresponding cusp is regular.
    widths      : Sequence consisting of the widths of the cusps (ordered the same as "cusps").
    
    cusp_orbits     : Orbits of cusps of X_G under the action of the absolute Galois group of KG.
    cusp_to_orbit   : Given a cusp, gives the index of its orbit.

    CPname      : If congruence subgroup Gamma has genus at most Gamma, then CPname is the Cummins-Pauli label of \pm Gamma.
    _______________________________________________________
    
    k           : An integer > 1 that will be a weight of a space of modular forms.
    dimMk       : Dimension of M_k(Gamma) over C;  same as dimension of M_{k,G}:=M_k(Gamma(N),Q(zeta_N))^G over KG.
    dimSk       : Dimension of S_k(Gamma) over C.
    
    prec        : A seqeuence of positive integers which keeps track of how many terms of q-expansions have been computed at the cusps.
    prec_sturm  : An sequence occurring in our version of Sturm's bound.

    F           : A sequence giving a basis of M_{k,G} as a Q-vector space.  The first dimMk elements will give a basis over C.

       Each F[i] is a modular form; it is given as a sequence of q-expansions at the cusps (with respect to the matrices in "cusps").
       Each q-expansion is a power series in the variable qw:=q^(1/e) with coefficients in Q(zetaN), where w is the width of the cusp being considered. 
       
    F0          : Same as above, but for the Q-subspace of M_{k,G} given by prescribed vanishing conditions at the cusps (for example, cusp forms).
                    The first #F0/KG_degree terms will be a bsisi over C.
    mult        : A sequence keeping track of the vanishing conditions imposed.

    psi         :  Whenever we compute a model for X_G in some projective space P^n, we use this entry to record the defining equations.

*/
  	     

function LiftMatrix(A,n)
 /* 
    Input: 
        A: matrix in GL(2,Z/NZ) with N>1,
        n: an integer that is congruent to det(A) modulo N.
    Output:
        A matrix B in M(2,Z) with det(B)=n whose reduction modulo N is A.
 */
    N:=#BaseRing(Parent(A));
    a:=Integers()!A[1,1]; b:=Integers()!A[1,2];
    c:=Integers()!A[2,1]; d:=Integers()!A[2,2];

    // The matrix [a,b;c,d] is congruent to A modulo N.
    // We now alter our choices so that a and c are relatively prime.
    if a eq 0 then a:=N; end if;
    if c eq 0 then c:=N; end if;
    if GCD(a,c) ne 1 then
        M:=&*[p: p in PrimeDivisors(a) | GCD(p,N) eq 1];
        ZM:=Integers(M);
        t:=Integers()!( (1-c)*(ZM!N)^(-1));
        c:=c+N*t;
        assert GCD(a,c) eq 1;
    end if;
    g:= (n-(a*d-b*c)) div N;  
    _,x0,y0:=Xgcd(a,c);
    x:=g*x0; y:=g*y0;  
    B:=Matrix([[a,b-N*y],[c,d+N*x]]);
    assert GL(2,Integers(N))!B eq A and Determinant(B) eq n;  // check!
    return B;
end function;

intrinsic CreateModularCurveRec(G::GrpMat, H::GrpMat) -> Rec
    {
    Input:
        G   : an open subgroup of GL(2,Zhat)
	    H   : the open subgroup of SL(2,Zhat) that is the intersection of G with SL(2,Zhat)

    Output:  
        A record of type "ModularCurveRec" that encodes the modular curve X_G with some 
        basic and useful invariants computed.
    }

    // We reduce G modulo its level
    gl2level:=GL2Level(G); 
    N:=gl2level;
    G:=GL2Project(G,gl2level);
    if not assigned G`Order then G`Order:=GL2Order(G); end if;

    //We reduce H modulo its level
    m:=SL2Level(H);    
    H:=SL2Project(H,m);
    if not assigned H`Order then H`Order:=SL2Order(H); end if;

    // Our modular curve
    X:=rec<ModularCurveRec |  N:=N, G:=G, H:=H, sl2level:=m, gl2level:=gl2level>;

    // To compute many of our quantities, we can adjoin -I to H; we call the group H0.    
    if SL2ContainsNegativeOne(H) then
        X`has_neg_one:=true;
        H0:=H;
    else
        X`has_neg_one:=false;
        H0:=SL2IncludeNegativeOne(H);  
        H0`SL:=true;
    end if;
    H0`Order:=SL2Order(H0); 

    X`index:=GL2Index(G);
    X`degree:=SL2Index(H0);   
    X`det_index:=GL2DeterminantIndex(G);

    if m eq 1 then
        X`cusps:=[Matrix([[1,0],[0,1]])];
        X`cusp_orbits:=[[1]];
        X`cusp_to_orbit:=[1];
        X`vinf:=1;
        X`widths:=[1];
        X`regular:=[true];
        X`v2:=1;
        X`v3:=1;
        X`genus:=0;
    else
        // main case        
        SL2:=SL2Ambient(m);
        T,phi:=RightTransversal(SL2, H0);  
        psi:=map<T->[1..#T] | {<T[i],i>: i in [1..#T]} >;
        f:=phi*psi;  

        // Compute the cusps and their widths
        B:=SL2![1,1,0,1];
        sigma:=Sym(#T)![f(t*B): t in T];   // permutation that describes how B acts on the set H0\SL2 via right multiplication  
        C:=CycleDecomposition(sigma);
        cusps0:=[Rep(c): c in C];
        cusps :=[ T[i] : i in cusps0]; 
        cusps:=[ LiftMatrix(A,1): A in cusps];  // each cusp given as a matrix in SL(2,Z)
        
        X`cusps:=cusps; 
        X`vinf:=#cusps; // number of cusps
        
        widths0:=[#c: c in C];  // Widths for group H0
        X`regular:= [ SL2!cusps[i]*(SL2![1,widths0[i],0,1])*(SL2!cusps[i])^(-1) in H : i in [1..X`vinf] ];
        assert &+widths0 eq X`degree;
        X`widths:=widths0;
        for i in [1..X`vinf] do  
            if not X`regular[i] then 
                X`widths[i]:= 2*X`widths[i]; 
                // We adjust the width for irregular cusps
            end if; 
        end for;

        // Compute number of elliptic points of order 2
        B:=SL2![0,1,-1,0];
        C:=CycleDecomposition(Sym(#T)![f(t*B): t in T]); 
        X`v2:=#[c: c in C | #c eq 1];

        // Compute number of elliptic points of order 3
        B:=SL2![0,-1,1,1];
        C:=CycleDecomposition(Sym(#T)![f(t*B): t in T]);
        X`v3:=#[c: c in C | #c eq 1];

        // Genus of X_H.   See Prop 1.40 of Shimura, "Introduction to the arithmetic theory of automorphic functions".
        X`genus:=Integers()!( 1 + X`degree/12 - X`v2/4 - X`v3/3 - X`vinf/2 );   


        //  We have already computed the cusps of X_G.
        //  We now compute the Galois orbits of the cusps under the action of Gal(Q(zeta_N)/K_G).
        SL2:=SL2Ambient(X`sl2level);
        GL2:=GL2Ambient(X`sl2level);
        U:=GL2DeterminantImage(X`G);
        s:=[];
        for j in [1..Ngens(U)] do
            u:=U.j;
            d:=u[1,1];
            b:=GL2![1,0,0,d];
            flag:=exists(g){g: g in G | Determinant(g) eq d}; //slow?
            
            sigma:=[FindCuspData(X,SL2!((GL2!g)^(-1)*GL2!X`cusps[i]*b))[1]: i in [1..X`vinf]];
            s:=s cat [sigma];
        end for;
        S:=sub<SymmetricGroup(X`vinf)|s>;
        phi:=hom<U->S|s>;
        X`cusp_orbits:=[[i:i in O]: O in Orbits(S)];  // orbits of cusps under the actions of Gal_(K_G).

        X`cusp_to_orbit:=[ [j: j in [1..#X`cusp_orbits] | i in X`cusp_orbits[j] ][1] : i in [1..X`vinf]];
        // The i-th cusp will lies in the n-th orbit of cusps, where n=X`cusp_to_orbit[i]
    end if;

    if gl2level eq 1 then
        X`is_unentangled:=true;
    else
        X`is_unentangled:= #G eq prod([ GL2Order( GL2Project(G,p^Valuation(N,p)) ) : p in PrimeDivisors(N) ]);
    end if;

    // We now compute the number field K_G and some related quantities.
    KN<z>:=CyclotomicField(N);
    deg_KG:= GL2DeterminantIndex(G);
    if deg_KG gt 1 then
        // Find an explicit description of the field K_G
        
        T:=[Integers()!u[1,1]: u in GL2DeterminantImage(G)];
        L:=sub<KN|[KN!1]>;
        i:=0;
        while Degree(L) lt deg_KG do
            i:=i+1;
            a:=&+[ Conjugate(z^i,t): t in T ]; // will lie in K_G
            L:=sub<KN| Generators(L) cat [a]>;
        end while;
        L:=OptimizedRepresentation(L); //improve presentation of field
        if Degree(L) ne 1 then        
            L<a>:=L;
        end if;
        assert L subset KN;

        X`KG:=L; 
        X`KG_degree:=Degree(X`KG);
        assert X`KG_degree eq AbsoluteDegree(X`KG) and X`KG_degree eq deg_KG;

        // We fix an integral basis for KG and also keep track of it in KN
        // We do an LLL so that it has small coefficients in Z[zetaN]
        OO:=RingOfIntegers(X`KG);
        A:=ChangeRing(Matrix([Eltseq(KN!a): a in Basis(OO)]),Integers());
        A:=LLL(A:Proof:=false);

        X`KG_integral_basis_cyclotomic:=[KN!Eltseq(a): a in Rows(A)];
        X`KG_integral_basis:=[X`KG!a: a in X`KG_integral_basis_cyclotomic];
    else
        X`KG:=CyclotomicField(1); // the rationals as a number field!
        X`KG_degree:=1;
        X`KG_integral_basis_cyclotomic:=[CyclotomicField(1)!1];
        X`KG_integral_basis:=[CyclotomicField(1)!1];
    end if;    


    if X`genus le 24 then
        // We compute a Cummins-Pauli label if the curve has genus at most 24.

        // Our group H0 corresponds to an open subgroup of SL(2,Zhat) and we are interested in them up to conjugacy in GL(2,Zhat).
        // The congruence subgroups of Cummins and Pauli correspond to open subgroups of SL(2,Zhat) that are given up to
        // conjugacy in the group generated by SL(2,Zhat) and [-1,0; 0,1].
        // In particular, many Cummins-Pauli labels could be applied to our groups (we just choose the first one).

        N0:=SL2Level(H0);
        H0:=SL2Project(H0,N0);
        I:=[i: i in [1..#cp_data] | cp_data[i]`genus eq X`genus and cp_data[i]`level eq N0 and 
                                    cp_data[i]`index eq SL2Index(H0) and Sort(cp_data[i]`cusps) eq Sort(widths0)];
        assert #I ne 0;

        if #I eq 1 then
            X`CPname:=cp_data[I[1]]`name;
        else
            GL2:=GL2Ambient(N0);
            SL2:=SL2Ambient(N0);
            GG:=sub<GL2|Generators(SL2) join {GL2![-1,0,0,1]}>;
            GG`Order:=GL2Order(GG);
            for i in I do
                H1:=sub<SL2|cp_data[i]`matgens>;
                H1`Order:=GL2Order(H1);
                if IsConjugate(GG,H0,H1) then
                    X`CPname:=cp_data[i]`name;
                    break i;
                end if;
            end for;
            assert assigned X`CPname;
        end if;
    end if;

    // The following are some group theoretic computations that will be used for computing modular forms.
    // The are also used whenever we increase the precision of modular curves, so we will precompute them.
    if X`sl2level gt 2 then
        m:=X`sl2level;
        H:=SL2Project(X`H,m);
        G:=X`G;
    else
        m:=4;
        H:=GL2Lift(SL2Project(X`H,X`sl2level),4);
        G:=GL2Lift(X`G,LCM(4,X`gl2level));
    end if;
    H`Order:=SL2Order(H);
    G`Order:=GL2Order(G);
    Gm:=GL2Project(G,m);
    GL2:=GL2Ambient(m);

    Gm_mod_H,phi:=Transversal(Gm,H);
        bb:=[ [ g*(GL2!X`cusps[e])*GL2![1,0,0,1/Determinant(g)] : e in [1..X`vinf]] : g in Gm_mod_H ];
    Gm_mod_H_pairs:=[ [FindCuspData(X,bb[i][e]) : e in [1..X`vinf]] :  i in [1..#Gm_mod_H]];   
    Gm_mod_H_det:=[ Integers()!Determinant(g): g in Gm_mod_H];
    N:=#BaseRing(G);
    G_mod_H:=Transversal(G,SL2Lift(H,N));
    cosets_det:=[[Integers()!Determinant(g): g in G_mod_H | phi(Gm!g) eq Gm_mod_H[j]]: j in [1..#Gm_mod_H]];
    X`Gm_mod_H:=Gm_mod_H;
    X`Gm_mod_H_pairs:=Gm_mod_H_pairs; 
    X`Gm_mod_H_det:=Gm_mod_H_det;
    X`cosets_det:=cosets_det;

    return X;
end intrinsic;

intrinsic CreateModularCurveRec(N::RngIntElt, gens::SeqEnum) -> Rec
    {CreateModularRec where G has level dividing N and its image in GL(2,Z/NZ) is generated by gens}
    return CreateModularCurveRec(sub<GL2Ambient(N)|gens>);
end intrinsic;

intrinsic CreateModularCurveRec(G::GrpMat) -> Rec   
    {CreateModularCurveRec with H computed directly}
    H:=SL2Intersection(G);
    _,H:=SL2Level(H);
    return CreateModularCurveRec(G,H);
end intrinsic; 

intrinsic ModularFormToSequence(M:: Rec, f::SeqEnum, mult::SeqEnum, N::RngIntElt : OverQ:=false) -> SeqEnum
    {
        Consider a modular form f for the modular curve M whose coefficients lie in Q(zeta_N), and let
        mult be a sequence of nonnegative integers with the same numbering as the cusps of M.

        Returns a finite sequence in Q(zeta_N) that consists of the first mult[i]+1 terms of the q-expansion of f
        at the i-th cusp of M for all i (with a chosen ordering).

        If "OverQ" is true, uses a basis of Q(zeta_N) over Q to obtain a matrix with rational entries instead.
    }
    ee:=[M`sl2level div w: w in M`widths];
    A:=Sort(&cat[ [[j*ee[i],i]: j in [0..mult[i]]] :  i in [1..M`vinf]]);
    KN<z>:=CyclotomicField(N);
    R<qw>:=PowerSeriesRing(KN);
    f:=[R!a: a in f];
    if not OverQ then
            return [ Coefficient(f[a[2]],a[1] div ee[a[2]]) : a in A];
    else 
            return &cat[ Eltseq(Coefficient(f[a[2]],a[1] div ee[a[2]])) : a in A];
    end if;
end intrinsic;
        
intrinsic SequenceToModularForm(M,v,mult,N : OverQ:=false) -> Rec
    {
        This is the reverse process of the function "ModularFormToSequence".
    }
    v:=Eltseq(v);
    ee:=[M`sl2level div w: w in M`widths];
    A:=Sort(&cat[ [[j*ee[i],i]: j in [0..mult[i]]] :  i in [1..M`vinf]]);
    KN<z>:=CyclotomicField(N);
    R<qw>:=PowerSeriesRing(KN);
    ephiN:=EulerPhi(N);

    f:=[O(qw^(1+mult[i])) : i in [1..M`vinf]];
    c:=1;
    for a in A do
        if not OverQ then
            f[a[2]]:=f[a[2]]+ v[c]*qw^(a[1] div ee[a[2]]);
            c:=c+1;
        else
            f[a[2]]:=f[a[2]]+ (KN!v[c..c+ephiN-1])*qw^(a[1] div ee[a[2]]);
            c:=c+ephiN;
        end if;
    end for;

    // Check
    v_:=ModularFormToSequence(M,f, mult,N : OverQ:=OverQ);
    assert #v eq #v_;
    assert v eq v_;

    return f;
end intrinsic;

intrinsic EisensteinFormsWeight1(N, prec) -> Assoc
    {
    Input:
        N:      an integer > 2
        prec:   a positive integer
    Output:
       An array E indexed by pairs [a,b] with a and b in Z/NZ.  
       The term of E indexed by [a,b] is 2N times the q-expansion of the Eisenstein series E_(a,b)^1 up to O(qN^(prec));
       it is given as a power series in qN:=q^(1/N) with coefficients in the cyclotomic field Q(zeta_N).

       For the definition of the Eisenstein series see section 2 of "Fourier expansion at cusps" by Brunault and Neururer.
       Remark: the extra factor of 2N ensures that all the coefficients are integral.
    }
    ZN:=Integers(N); 
    M:=RSpace(ZN,2); 
    K<z>:=CyclotomicField(N);
    OK:=RingOfIntegers(K); 
    zeta:=OK!z;
    R<qN>:=PowerSeriesRing(OK);
        
    powers_of_zeta_list:=[zeta^i: i in [0..N-1]];
    function power_of_zeta(i)
        return powers_of_zeta_list[(i mod N)+1];
    end function;

    E:=AssociativeArray(); 
    for a in [0..N-1] do       
        for b in [0..N-1] do
            e:=O(qN^(prec));

            I:=[1..(prec-1-a) div N];
            if a ne 0 then I:=[0] cat I; end if;
            for d in I do
                m:=a+N*d;
                for n in [1..(prec-1) div m] do
                    e:= e + power_of_zeta( b*n) * qN^(m*n);
                end for;
            end for;

            I:=[1..(prec-1+a) div N];
            for d in I do
                m:=-a+N*d;
                for n in [1..(prec-1) div m] do
                    e:= e - power_of_zeta(-b*n) * qN^(m*n);
                end for;
            end for;

            e:=2*N*e;  // scale by factor of 2N

            // Add appropriate constant term.
            if a eq 0 and b ne 0 then  e:=e + OK!( N*(1+power_of_zeta(b))/(1-power_of_zeta(b)) ); end if;
            if a ne 0 then e:=e + N-2*a; end if;
            E[M![a,b]]:=e;  
        end for;
    end for;
    return E;
end intrinsic;

intrinsic FindCuspData(M,A) -> SeqEnum
    { 
        Consider a modular curve M=X_G given by a subgroup G of GL_2(Zhat).  
        Let H be the intersection of G with SL(2,Zhat).    

        Input:   
                M   : a record of type "ModularCurveRec"
                A   : a matrix in SL(2,Zhat) given modulo an integer divisible by M`sl2level.

        Output:  a triple of integers [i,j,e] such that A and 
                        e * M`cusps[i] * [1,1;0,1]^j 
                lie in the same coset H\SL(2,Zhat), where cusps[i] is the fixed matrix in SL(2,Z)
                describing the i-th cusp of M and e is 1 or -1.  

                When G contains -I, we always choose e=1.       
    }

    H:=M`H;  
    m:=M`sl2level;  
    if m eq 1 then
        return [1,0,1]; // easy when only one coset
    end if;

    SL2:=SL2Ambient(m);  
    cusps:=[SL2!a: a in M`cusps];
    B:=SL2![1,1,0,1];  
    A:=SL2!A;

    // Brute force search!
    j:=0;  
    repeat 
        for i in [1..#cusps] do
            if cusps[i]*B^j*A^(-1) in H then
                return [i,j,+1];
            elif -cusps[i]*B^j*A^(-1) in H then
                return [i,j,-1];
            end if;
        end for;
        j:=j+1;
    until false;
end intrinsic;

intrinsic SturmPrecision(k::RngIntElt,M::Rec) -> FldRatElt  
    {    
        Input: an integer k>1 and a record M that corresponds to a modular curve.

        Let Gamma be the congruence subgroup corresponding to the modular curve.  For a 
        modular form f on Gamma of weight k>1, let Z_f be the total number of zeros of f, counted with 
        multiplicities, at the cusps of the modular curve.

        Output: a rational number B such that Z_f>B if and only if f=0.
    }
    if IsEven(k) then
        B:=k/2*(2*M`genus-2)+M`v2*Floor(k/4)+M`v3*Floor(k/3)+ k/2*M`vinf;
    else
        B:=k/2*(2*M`genus-2)+M`v2*Floor(k/2)/2+M`v3*Floor(2*k/3)/2+ k/2*M`vinf;  
    end if;
    return B;
end intrinsic;

intrinsic FindModularFormsWithVanishingConditions(M::Rec, mult::SeqEnum : lll:=[true,true], saturation:=true) -> Rec
    {
    Input:  
        M    : a record of type "ModularCurveRec" with a Q-basis M`F of M_(k,G) already computed.
        mult : is a sequence of nonnegative integers of the same length as cusps:=M`cusps

    Let V be the Q-subspace of M_(k,G) consisting of modular forms so that the vanishing of f at 
    the i-th cusp cusps[i]*infty is at least mult[i] for all i.   

    (the parameters "lll" and "saturation" give some control on how LLL and Saturation is done; these should pprobably be left alone!)

    Output: 
            Returns the record M with the entry M`F0 being a basis of the Q-vector space V
            with the same conventions as the basis M`F of M_(k,G).   

            Let d be the dimension of V over K_G (we will have d=#M`F0 div M`KG_degree).
            The first d modular forms in the sequence M`F0 will be a basis of V over K_G (moreover, 
            they are linearly independent over Cthe complex numbers).
            
    The precision of all modular forms will be increased on the fly if required to enforce vanishing conditions.
    }
    if Type(lll) eq Type(true) then 
        lll:=[lll,lll];
    end if;

    N:=M`N;
    if M`sl2level gt 2 then
        m:=M`sl2level;  
    else
        m:=4;
    end if;
                
    cusps:=M`cusps;
    widths:=M`widths;
    M`mult:=mult;

    error if &or[m lt 0: m in mult], "Multiplicities need to be positive."; 
    error if not assigned M`F or not assigned M`k, "Need modular forms computed before imposing vanishing conditions.";

    if &and[m eq 0: m in mult] or #M`F eq 0 then 
        // vanishing condition impose no constraints
        M`F0:=M`F; return M; 
    end if;  

    delete M`F0;
    ee:=[m div w: w in M`widths];
  
    // We increase the precision of modular forms computed before proceeding.
    prec:=[mult[i]+1 : i in [1..M`vinf]];
    if &and[prec[i] le M`prec[i]: i in [1..M`vinf]] eq false then
        M:=IncreaseModularFormPrecision(M,prec);
    end if;

    // For each Gal_(K_G)-orbit of cusps, we need only impose the vanishing conditions at a single
    // cusp (the rest will be automatic).  We thus consider an analogous sequence mult1.
    mult1:=[0: i in [1..M`vinf]];
    for O in M`cusp_orbits do
        max,j:=Maximum([mult[i]: i in O]); 
        mult1[O[j]]:=max;
    end for;
    assert &and[mult1[i] lt M`prec[i] : i in [1..M`vinf]];


    // ====== We now construct a Q-basis FF of V. ======

    // The matrix C has the vanishing conditions we need to impose.
    C:=Matrix([ModularFormToSequence(M,f,[a-1: a in mult1],N : OverQ:=true) : f in M`F]);
    C:=LCM([Denominator(C[i,j]): i in [1..Nrows(C)], j in [1..Ncols(C)]]) *C;
    C:=ChangeRing(C,Integers());

    B:=KernelMatrix(C);
    if Nrows(B) eq 0 then M`F0:=[];  return M; end if;   // If V=0, we are done.
    if lll[1] then
        B:=LLL(B :Proof:=false);
    end if;
    FF:= [ [&+[B[i,j]*M`F[j][e]: j in [1..Ncols(B)]]: e in [1..M`vinf]] : i in [1..Nrows(B)]];
    C1:=B; // Remember B for later.


    // Starting with our modular forms FF, we construct a matrix with the goal of
    // finding an improved basis FF of V.
    mult1:=[M`prec_sturm[i]-1 : i in [1..M`vinf]];
    B0:=Matrix([ModularFormToSequence(M,f,mult1,N : OverQ:=true) : f in FF]);
    B1:=LCM([Denominator(B0[i,j]):i in [1..Nrows(B0)], j in [1..Ncols(B0)]])*B0;
    B1:=ChangeRing(B1,Integers());
    if saturation then B1:=Saturation(B1); end if;
    if lll[2] then B1:=LLL(B1 : Proof:=false); end if;

    // We order our modular forms so that the first few rows of B1 are linearly independent over K_G.
    d:=#FF div M`KG_degree;
    assert d*M`KG_degree eq #FF;
    FF_temp:=[SequenceToModularForm(M,v,mult1,N : OverQ:=true) : v in Rows(B1)];
    Q:=Matrix([ModularFormToSequence(M,f,mult1,N : OverQ:=false) : f in FF_temp]);
    KN<z>:=CyclotomicField(N);
    ON:=RingOfIntegers(KN);
    Q:=ChangeRing(Q,ON);
    p:=2;
    repeat
        repeat
            p:=NextPrime(p);
        until N mod p ne 0 and GL2Order(M`G) mod p ne 0;
        P:=Factorization(ideal<ON|[p]>)[1][1];
        FF_P,iota:=ResidueClassField(P);
        Q_red:=ChangeRing(Q,iota);
    until Rank(Q_red) eq d;
    I:=[];
    b:=[];
    for i in [1..Nrows(Q_red)] do
        b_:=b cat [Q_red[i]];
        if Rank(Matrix(b_)) gt #b then
            I:=I cat [i];
            b:=b_;
        end if;
        if #b eq d then
            break i;
        end if; 
    end for;
    assert #I eq d; 
    B1:=Matrix([B1[i]: i in I] cat [B1[i]: i in [1..Nrows(B1)] | i notin I]);
    
    // The matrix C2 belows encodes how to go from the current FF to an improved version.
    _,U0:=EchelonForm(B0);
    _,U1:=EchelonForm(ChangeRing(B1,Rationals()));
    C2:=U1^(-1)*U0;
    
    M`F0:= [ [&+[C2[i,j]*FF[j][e]: j in [1..#FF]]: e in [1..#cusps]] : i in [1..Nrows(C2)]];
    
    // Keep track of data so we may increase the precision later without redoing the above computations.
    M`conversion_matrices:=[* M`conversion_matrices[i]: i in [1..2] *] cat [*C1, C2*];
 
    // Check:
    for i in [1..M`vinf] do
        assert &and[Valuation(f[i]) ge mult[i] : f in M`F0];
    end for;

    return M;
end intrinsic;

intrinsic FindCuspForms(M::Rec : lll:=true, saturation:=true) -> Rec
    {Applies "FindModularFormsWithVanishingConditions" with mult:=[1,1,...,1]}
    return FindModularFormsWithVanishingConditions(M,[1: i in [1..#M`cusps]] : lll:=lll, saturation:=saturation);
end intrinsic;

intrinsic EvaluateAtMonomialsOfDegree(F,d) -> Assoc
    {  Input
            F : a sequence of n>0 elements in some ring
            d : a positive integer.
        Output:
            An array A such that for nonnegative integers e_1,..,e_n that sum to d,
            A[[e_1,..,e_d]] is the product of F[i]^(e_i).

        This function could be greatly improved but it is better than the most naive implementation.
    }
    assert #F ne 0;
    A:=AssociativeArray();
    B:=AssociativeArray();
    B[[]]:= Parent(F[1])!1;
    for i in [1..#F] do
        // Compute F[i]^j with j from 0 to d
        v:=[Parent(F[i])!1];  for j in [1..d] do v := v cat [v[#v]*F[i]]; end for;
        B0:=AssociativeArray();
        for k in Keys(B) do
            d0:=&+(k cat [0]);
            if i lt #F then
                for j in [0..(d-d0)] do
                    B0[k cat [j]]:= B[k] * v[j+1];
                end for;
            end if;
            if i eq #F then
                A[k cat [d-d0]]:= B[k] * v[d-d0+1];
            end if;
        end for;
        B:=B0;
    end for;
    return A;
end intrinsic;

intrinsic FindRelationsOverKG(M::Rec, F::SeqEnum,d::RngIntElt : OverQ:=false, lll:=true, dim_only:=false, Proof:=false, k:=-1) -> SeqEnum
 { Input: 
        M:  a record describing the modular curve X_G
        F:  a finite sequence of modular forms in some M_(k,G) 
            (each modular form is given as a sequence of q-expansions corresponding to the cusps of the modular curve).
            We further assume all the q-expansions have coefficients in Q(zeta_N), where N=M`N.
        d:  a positive integer

    With F=[f_1,..,f_n], let V be the K_G-vector space consisting of homomogeneous polynomials P in K_G[x_1,..,x_n]
    of degree d with P(f_1,..,f_n)=0.

    Output:
        -   A basis "psi" of a K_G-vector space of homogenous degree d polynomials in K_G[x_1,..,x_n] that contains 
            a basis of V (and might be larger).
            If modular forms in F are computed to a high enough precision, psi will actually be a basis of V.
        
        -   A boolean b that is true when the parameter "Proof" is set to true and an application of the Sturm bound
            verifies that psi is a basis of V.  When "Proof" is set to true, the parameter "k" needs to be the weight of the modular forms.
        
        An integer t so that for each h in psi, the sum of the orders of the zeros of h(f_1,..,f_n) at the cusps 
        is at least t. (This integer and Sturm's bound can sometimes be used to prove vanishing and verify that psi 
        is a basis of V)  

    When "OverQ" is true, a basis of V as a Q-vector space is returned instead.
    When "lll" is true, we use the LLL algorithm to try to make the polynomials nicer.

    When "dim_only" is true, the function instead returns only the cardinality of psi (this can be be faster
    than actually computing psi)
 }

    I:=[O[1]: O in M`cusp_orbits];
    // We only need to check for relations using a single cusp in each Gal_(K_G)-orbit of the cusps.

    N:=M`N;
    m:=M`sl2level;
    widths:=M`widths;

    KN:=CyclotomicField(N);
    R<qw>:=PowerSeriesRing(KN);
    F:=[[R!a: a in f] : f in F]; 

    n:=#F;
    if n eq 0 then return [],true; end if;
    Pol<[x]>:=PolynomialRing(KN,n);
    
    // Substitute modular forms into monomials of degree d; only keep track of cusps i in I.
    A:=[ EvaluateAtMonomialsOfDegree([f[i]: f in F],d) : i in I ];

    // Change precisions of q-expansions in A so that precision depends only on the cusp.
    prec0:=[ Minimum([AbsolutePrecision(A[i][s]):s in Keys(A[i]) ]) : i in [1..#I]];
    for i in [1..#I] do
        for s in Keys(A[i]) do
            A[i][s]:=ChangePrecision(A[i][s], prec0[i]);
        end for;
    end for;

    monic_powers:=Sort([k:k in Keys(A[1])]); 
    mon:=Sort([a: a in monic_powers | &+a eq d]); // labels for monomials of degree d
    monomials:=[ &*[x[i]^a[i]:i in [1..n]] : a in mon]; //monomials of degree d

    beta1:=[];  
    for l in [1..#mon] do
        for j in [1..M`KG_degree] do
            beta1:=beta1 cat [[M`KG_integral_basis_cyclotomic[j]*A[i][mon[l]] : i in [1..#I]]];
        end for;
    end for;

    B:=[];
    ephi:=EulerPhi(N);
    for i in [1..#I] do
        for j in [0..prec0[i]-1] do
            for l in [1..ephi] do
                v:=[Coefficient(f[i],j)[l] : f in beta1];
                B:=B cat [Vector(v)];
            end for;
        end for;
    end for;
    
    B:=Matrix([LCM([Denominator(a): a in Eltseq(B[i])])*B[i]: i in [1..#B]]);
    B:=ChangeRing(B,Integers());    
    r:=Rank(B);

    if dim_only then
        dim:=Ncols(B) - r;  //dim over Q
        assert dim mod M`KG_degree eq 0;
        if OverQ then
            return dim;
        end if;
        return dim div M`KG_degree;
    end if;
    
    // Find a prime so that B mod p has the same rank as B
    p:=0;
    repeat
        p:=NextPrime(p);
        B_red:=ChangeRing(ChangeRing(B,Integers()),GF(p));
    until Rank(B_red) eq r;
    C:=EchelonForm(Transpose(B_red));
    assert Rank(C) eq r;
    pivots:=[ Minimum([j: j in [1..Ncols(C)] | C[i,j] ne 0]) :  i in [1..r]];

    B:=Matrix([B[i]: i in pivots]); // chose rows of B that span a space of the same dimension

    C:=[v: v in Basis(NullspaceOfTranspose(ChangeRing(B,Rationals())))];    

    if #C eq 0 then
        return [],true; // No nonzero relations
    end if;

    C:=Saturation(Matrix(C));
    if lll then
        C:=LLL(C:Proof:=false); 
    end if;
    assert Nrows(C) eq Ncols(B) - r;

    // Compute psi
    Pol_KG<[x]>:=PolynomialRing(M`KG,n);
    monomials:=[ &*[x[i]^a[i]:i in [1..n]] : a in mon];
    beta:=[];
    for l in [1..#mon] do
        for j in [1..M`KG_degree] do
            beta :=beta  cat [ M`KG_integral_basis[j]*monomials[l] ];
        end for;
    end for;
    psi:=[&+[C[i,j]*beta[j]: j in [1..Ncols(C)]]: i in [1..Nrows(C)]];

    // CHECKS: can remove (TODO)
    tests:=[ [ &+[C[i,j]*beta1[j][e]: j in [1..Ncols(C)]] : e in [1..#I]] : i in [1..Nrows(C)]];
    assert &and[IsWeaklyZero(f): f in &cat tests];


    if M`KG_degree gt 1 and OverQ eq false then
        assert #psi mod M`KG_degree eq 0;
        r:=#psi div M`KG_degree;
        // Want psi so that the first r polynomials are linearly independent over K_G.
        // We achieve this by first looking modulo a suitable prime ideal.

        B:=Matrix([ [MonomialCoefficient(pol,m): m in monomials] : pol in psi]);
        O_KG:=RingOfIntegers(M`KG);  
        B:=ChangeRing(B,O_KG);
        p:=1;
        repeat
            p:=NextPrime(p);
            P:=Factorization(ideal<O_KG|[p]>)[1][1];
            FF_P,iota:=ResidueClassField(P);
            B_red:=ChangeRing(B,iota);
        until Rank(B_red) eq r;
        I1:=[];
        b:=[];
        for i in [1..Nrows(B_red)] do
            b_:=b cat [B_red[i]];
            if Rank(Matrix(b_)) gt #b then
                I1:=I1 cat [i];
                b:=b_;
            end if;
            if #b eq r then
                break i;
            end if; 
        end for;
        psi:=[psi[i]: i in I1];
    end if;

    proved:=false;
    if Proof and k gt 0 then
        vanishing_lower_bound:=Minimum([ &+[#M`cusp_orbits[e]*AbsolutePrecision(&+[C[i,j]*beta1[j][e]: j in [1..Ncols(C)]]) : e in [1..#I]] : i in [1..Nrows(C)]]);

        if vanishing_lower_bound gt SturmPrecision(k*d,M) then
            // enough terms of q-expansions have been computed to ensure we have found all quadratic relations
            proved:=true;
        end if;
    end if;
    
    return psi, proved;
end intrinsic;

intrinsic FindCanonicalModel(M::Rec : lll:=[true,true,true,true,true], prec0:=0, prec_delta:=10) -> Rec
 {      
    Input:
            M:  a record of type ModularCurveRec (for example produced as output of CreateModularCurveRec) that
                corresponds to a modular curve X_G with genus g at least 3.
    
    Output: An updated record M.
            The first g elements of M`F0 will be a basis f_1,..,f_g of the K_G-subspace of M_(k,G) consisting
            of cusps forms.  These cusp forms define the canonical map
                            X_G -> P^(g-1)_(K_G); 
            the image is a curve C which is defined by the equations in the sequence M`psi.  Moreover, M`psi
            consists of homomogeneous polynomials that generated the ideal of C.

    The set psi will actually generate the ideal of K_G[x_1,..,x_g] arising from C.
    The homogeneous polynomials in psi will all have degree 2 or 3 except in the case where X_G has genus 3
    and is not geometrically hyperelliptic (in this case psi consists of a single quartic).

    If "lll" is true, we use the LLL algorithm to hopefully make the model nicer.
    The quantities "prec0" and "prec_delta" are technical parameters for the starting precision and increasing precision.
 }
    if Type(lll) eq Type(true) then lll:=[lll,lll,lll,lll,lll]; end if;

    g:=M`genus;
    error if g lt 2, "Curve must have genus at least 2";

    K:=M`KG;
    if M`KG_degree eq 1 then
        K:=Rationals();
    else
        K:=M`KG;
    end if;
    Pol<[x]>:=PolynomialRing(K,g);

    // Compute modular forms of weight 2 if needed.
    if not assigned M`k or M`k ne 2 or not assigned M`F then    
        M:=FindModularForms(2,M : lll:=[lll[1],lll[2]]);
    end if;
    // Compute cusp forms
    M:=FindCuspForms(M: lll:=[lll[3],lll[4]]);

    if g eq 2 then
        M`model_degree:=1;
        M`psi:=[];
        return M;
    end if;

    if g eq 3 and M`CPname notin gonality_equals_2 then
        // For a nonhyperelliptic curve of genus 3, the canonical model will be a smooth plane quartic!
        M`model_degree:=2*M`genus-2;
        prec:=Minimum([ (M`sl2level div M`widths[i])*M`prec[i] : i in [1..M`vinf]]);
        prec:=Maximum(prec,prec0);
        repeat
            F:=[M`F0[i]: i in [1..g]];        
            d:=FindRelationsOverKG(M, F, 4 : dim_only:=true);         
            if d ne 1 then
                // Increase precision if we found too many relations
                prec:=prec+prec_delta;
                M:=IncreaseModularFormPrecision(M,prec);
            end if;   
        until d eq 1;        
        I4:=FindRelationsOverKG(M, F, 4 : lll:=lll[5]);  
        I4:=[Pol!p: p in I4];
        M`psi:=I4;
        return M;
    end if;

    // We know the dimension of quadratic relations.
    if g le 24 and M`CPname in gonality_equals_2 then
        d2:=(g-1)*(g-2) div 2;
    else
        d2:=((g-2)*(g-3)) div 2;
    end if;

    prec:=Minimum([ (M`sl2level div M`widths[i])*M`prec[i] : i in [1..M`vinf]]);
    prec:=Maximum(prec,prec0);
    repeat
        F:=[M`F0[i]: i in [1..g]];        
        d:=FindRelationsOverKG(M, F,2 : dim_only:=true);         
        if d ne d2 then
            // Increase precision if we found too many relations
            prec:=prec + prec_delta;
            M:=IncreaseModularFormPrecision(M,prec);
        end if;   
    until d eq d2;

    // Actually compute relations this time
    I2:=FindRelationsOverKG(M, F, 2 : lll:=lll[5]);
    I2:=[Pol!p: p in I2];

    // If curve is hyperelliptic, then its canonical curve is cut out by quadratic relations
    if M`genus le 24 and M`CPname in gonality_equals_2 then
        //M`model_degree:=2*M`genus-2;  // TODO, check
        M`psi:=I2;
        return M;
    end if;

    // The curve is nonhyperelliptic and we know exactly when the polynomials I2 cut out the canonical curve.
    M`model_degree:=2*M`genus-2;
    if M`genus gt 4 and (M`genus gt 24 or M`CPname notin gonality_equals_3 cat smooth_plane_quintic) then
        M`psi:=I2;
        return M;
    end if;

  
    // Our model now requires cubic polynomials as well.
    mon:=MonomialsOfWeightedDegree(Pol,3);
    V:=RSpace(K,#mon); // space of cubic homogeneous polynomials over K
    BasisV:=[mon[i]:i in [1..#mon]];
    W:=sub<V| [V![MonomialCoefficient(x[i]*p,m): m in mon] : i in [1..g], p in I2]>;
    // cubic homogenous polynomials that vanish on the canonical curve arising from quadratic relations
    assert Dimension(W) eq ((g-3)*(g^2+6*g-10) div 6) - (g-3);
/*
    // We now construct a complement Wc of W in V
    Wc:=sub<V|[]>; 
    for v in Basis(V) do
        Wc_:=Wc + sub<V|[v]>;
        if Dimension(Wc_) gt Dimension(Wc) and Dimension(Wc_ meet W) eq 0 then
            Wc:=Wc_;
            if Dimension(W)+Dimension(Wc) eq Dimension(V) then
                break v;
            end if;
        end if;
    end for;
    pol:=[ &+[v[i]*mon[i] : i in [1..#mon]] : v in Basis(Wc)]; // basis of complement
    */
     repeat

        M:=IncreaseModularFormPrecision(M,prec);

        F:=[M`F0[i]: i in [1..g]];      
        prec:=prec+prec_delta; 

        FF:=[ [Evaluate(m,[f[i]: f in F]) : i in [1..M`vinf]] : m in BasisV ];
        I3,found:=FindRelationsOverKG(M,FF,1: Proof:=true, k:=3*M`k);

    until found;
    I3:=[Pol!Evaluate(p,BasisV): p in I3];
    /*
    repeat
        F:=[M`F0[i]: i in [1..g]];
        //h:=[ [Evaluate(p,[f[i]: f in F]): i in [1..M`vinf]] :  p in pol ];        
        d:=FindRelationsOverKG(M,F,3 : dim_only:=true);
        if d lt g-3 then
            // Increase precision if we have not found enough cubic relations.
            prec:=prec + prec_delta; 
            M:=IncreaseModularFormPrecision(M,prec);
        end if;
    until d ge g-3;

    // Actually compute relations this time
    I3:=FindRelationsOverKG(M,F,3 : lll:=lll[5]);  
    I3:=[ Pol!l : l in I3 ];
*/
    M`psi:=I2 cat I3;
    return M;
end intrinsic;


intrinsic FindModelOfXG(M::Rec : G0:=1, prec0:=0, prec_delta:=10) -> Rec
    {  
        Input:       
                M:      a record of type "ModularCurveRec" (for example produced as output of CreateModularCurveRec) that 
                        corresponds to a modular curve X_G.    Function assumes that G contains -I.

        Output: 
                An updated record M is returned with an explicit model computed.   The polynomials cutting out the model
                can be found in M`psi.

                Details:
                The model is found by computing a K_G-subspace V of M_(k,G) given by extra vanishing conditions at the cusps.
                The k is a positive even integer stored as M`k and the multiplicity at the cusps is given by M`mult (with the same 
                ordering of cusps as given by M).   A Q-basis of V is given by M`F0.

                Let n be the dimension of V as a K_G-vector space; it agrees with #M`F0/M`KG_degree.  The first n terms
                            f_1,..,f_n 
                of M`F0 is a K_G-basis of V.   The set of polynomials M`psi generats the ideal of K_G[x_1,...,x_n] consisting of 
                polynomials P for which P(f_1,...,f_n)=0.   The ideal cuts out the model in P^(n-1)_(K_G).

                The set M`psi will always consist of homogeneous polynomials of degree 2 and 3.  
                We use the canonical model whenever possible.

            
        If desired, the parameter G0 can be set to be an open subgroup of GL(2,Zhat) for which G=M`G is a normal subgroup.  
        We then choose our model so that G0 acts on V.   This makes it easy later to compute the automorphisms of our curve coming from G0/G.

        The quantities "prec0" and "prec_delta" are technical parameters for the starting precision and increasing precision.
    }

    // We compute the canonical model when possible (ie, the modular curve is not hyperelliptic and has genus at least 3)
    if M`genus ge 3 and (M`genus gt 24 or M`CPname notin gonality_equals_2) then
        M:= FindCanonicalModel(M);
        return M;
    end if;

    //  We increase our even weight k until Riemann-Roch guarantees an embedding of XG using M_{k,G}.
    //  (We currently assume that -I in G, odd weights might be useful otherwise...)
    k:=0;
    repeat
        k:=k+2;
        degD:= (k*(2*M`genus-2)) div 2 + Floor(k/4)*M`v2 + Floor(k/3)*M`v3 + (k div 2)*#M`cusps;
    until degD ge 2*M`genus+1;
    
    // Compute modular forms of weight k.
    M:=FindModularForms(k,M);  
    cusps:=M`cusps;

    N:=M`N;
    GL2:=GL2Ambient(N); 
    SL2:=SL2Ambient(N);
    G:=M`G;

    assert GL2ContainsNegativeOne(G);  // We assume that -I lies in G

    if Type(G0) ne GrpMat then
        G0:=G;  // If not set by user ahead of time
    else
        N0:=GL2Level(G0); 
        assert N mod N0 eq 0;
        G0:=GL2Lift(GL2Project(G0,N0),N);
        assert G subset G0;
        assert IsNormal(G0,G);
    end if;

    m:=M`sl2level;
    SL2:=SL2Ambient(m);
    GL2:=GL2Ambient(m);

    // Computes the action of det(G0) on the cusps of X_G.  
    // When det(G0)=det(G), this corresponds to the action of Gal(K_G(zeta_N)/K_G) on the cusps.
    if #M`cusps gt 1 then
        U:=GL2DeterminantImage(G0);
        s:={};
        for u in Generators(U) do
            d:=u[1,1];
            b:=GL2![1,0,0,d];
            flag:=exists(g){g: g in G | Determinant(g) eq d}; //OK for now, but could implement better if slow.
            sigma:=[FindCuspData(M,SL2!((GL2!g)^(-1)*GL2!cusps[i]*b))[1]: i in [1..M`vinf]];
            s:=s join {sigma};
        end for;
        
        // Let H and H0 be the intersection of G and G0, respectively, with SL(2,Z/N).  
        // We now computes the action of H0/H on the cusps of X_G.
        H0:=SL2Intersection(G0); 
        Q,iotaQ:=quo<H0|SL2Lift(M`H,N)>;
        for g_ in Generators(Q) do
            g:= SL2!(g_ @@ iotaQ);
            sigma:=[FindCuspData(M,SL2!(g^(-1)*SL2!cusps[i]))[1]: i in [1..#M`cusps]];
            s:=s join {sigma};
        end for;

        S:=sub<SymmetricGroup(M`vinf)|s>;
        ind:=[[i:i in O]: O in Orbits(S)];  // orbits of cusps under the actions of G0 and Gal_Q.
    else
        ind:=[[1]];
    end if;


    /*  We now compute a sequence "mult" of nonnegative integers that give the vanishing conditions 
        we want to impose at the cusps.  It is chosen so the integers depend only on the Galois orbit of the cusps
        and so that the degree of the the corresponding sheaf is at least 2*genus+1.   We try to choose our
        integers so that the degree is minimal and so that we do not have to compute too many terms of the
        q-expansions.
    */
            function linear_integral_solutions(m,n)
                /* Given a tuple m=(m_1,...m_n) of positive integer and a nonnegative integer n,
                    this computes (by brute force) the set of solutions to 
                        m_1 x_1 + ... + m_n x_n
                    in nonnegative integers. */                
                if #m eq 1 then
                    if n mod m[1] eq 0 then
                        return [[n div m[1]]];
                    end if;
                    return [];
                end if;
                S:=[];
                for i in [0..n div m[1]] do
                    S0:=linear_integral_solutions([m[j]: j in [2..#m]],n-m[1]*i);
                    S:=S cat [ [i] cat s : s in S0];
                end for;
                return S;
            end function; 

    for n in Reverse([0..degD-(2*M`genus+1)]) do
        S:=linear_integral_solutions([#O: O in ind],n);
        if #S ne 0 then
            break n;
        end if;
    end for;

    _,i0:=Minimum([ Maximum([s[j]/M`widths[ind[j][1]]: j in [1..#ind]]) : s in S]);
    s:=S[i0];
    mult:=[0: i in [1..M`vinf]];
    for i in [1..#ind] do
        for j in ind[i] do
            mult[j]:=s[i];
        end for;
    end for;
    M`mult:=mult;  // Our vanishing conditions

    // We now impose the vanishing conditions;  M`F0 will give the basis of modular forms that satisfy the conditions.
    M:=FindModularFormsWithVanishingConditions(M,mult);  

    F:=[M`F0[i]:i in [1..#M`F0 div M`KG_degree]]; // basis over K_G
    n:=#F;  

    if M`KG_degree eq 1 then
        K:=Rationals();
    else
        K:=M`KG;
    end if;
    Pol<[x]>:=PolynomialRing(K,n);

    assert degD-&+mult ge 2*M`genus+1;
    assert degD-&+mult-M`genus+1 eq n;

    M`model_degree:=degD-&+mult;

    // We look for quadratic relations first
    ee:=[m div w: w in M`widths];
    prec1:=Maximum([prec0] cat [(M`prec[i]+1)* ee[i] : i in [1..M`vinf]]);
    repeat
        prec:=[(prec1-1) div ee[i]: i in [1..M`vinf]];

        M:=IncreaseModularFormPrecision(M,prec);
        F:=[M`F0[i]:i in [1..#M`F0 div M`KG_degree]];

        prec1:=prec1+prec_delta; 

        I2,found:=FindRelationsOverKG(M,F,2: Proof:=true, k:=k);  // Proof set to true.
        I2:=[Pol!p: p in I2];
    until found;

    if degD-&+mult gt 2*M`genus+1 then
        M`psi:=I2;
        return M;
    end if;
    assert degD-&+mult eq 2*M`genus+1;
    
      // Now look for cubic relations
    monomials_degree_3:=MonomialsOfWeightedDegree(Pol,3);
    V:=KSpace(K,#monomials_degree_3);
    pol:=[x[i]*p: i in [1..n], p in I2];
    W:=sub<V|[ V![ MonomialCoefficient(p,m) : m in monomials_degree_3]: p in pol ]>;
    // W is space of cubic relations coming from quadratic relations
    W0:=W;
    BasisV:=[monomials_degree_3[i]: i in [1..#monomials_degree_3]];
    // Find a linearly independent sequence "beta" that spans a complement of W in V.
    i:=1;
    beta:=[];
    while Dimension(W0) ne Dimension(V) do
        W1:=W0+sub<V|V.i>;
        if Dimension(W1) gt Dimension(W0) then
            beta cat:=[monomials_degree_3[i]];
            W0:=W1;
        end if;
        i:=i+1;
    end while;

    // We look for cubic relations
    ee:=[m div w: w in M`widths];
    prec1:=Maximum([prec0] cat [(M`prec[i]+1)* ee[i] : i in [1..M`vinf]]);
    //prec1:=Maximum(prec0,Minimum(M`prec));
    repeat

        prec:=[(prec1-1) div ee[i]: i in [1..M`vinf]];
        M:=IncreaseModularFormPrecision(M,prec);

        F:=[M`F0[i]:i in [1..#M`F0 div M`KG_degree]];        
        prec1:=prec1+prec_delta; 

        FF:=[ [Evaluate(m,[f[i]: f in F]) : i in [1..M`vinf]] : m in BasisV ];
        I3,found:=FindRelationsOverKG(M,FF,1: Proof:=true, k:=3*k);

    until found;
    I3:=[Pol!Evaluate(p,BasisV): p in I3]; // cubic relations

    M`psi:=I2 cat I3;
    return M;   
end intrinsic;

intrinsic ConvertModularFormExpansions(M1, M2, F, g : wt:=0) -> SeqEnum
    {
        Input:
            M1, M2  : modular curves corresponding to X_G1 and X_G2, respectively, where Gi is an open subgroup of GL(2,Zhat).                  
            g       : a matrix in GL(2,Zhat)  (given as a matrix in GL(2,Z/N) where N is divisible by the level of G1)
            F       : a sequence of (weakly) modular form on M1=X_G1; each modular forms is given as a sequence consisting of 
                        its q-expansion at the cusps of M1 (using M1`cusps).                     
            wt      : the weight of each modular form in F; though we only use the value of wt modulo 2.

        We assume that for each modular form f in F, f*g is a modular form on M2=X_G2.   

        Output: the sequence of modular forms f*g of M2=X_G2 with f in F.
        
        Note:   If the wrong weight "wt" is given, the resulting output might be off by a sign.
    }

    N1:=M1`N;
    N2:=M2`N;   
     
    KN1<zeta_N1>:=CyclotomicField(N1);
    R1<qw>:=PowerSeriesRing(KN1);

    KN2<z>:=CyclotomicField(N2);
    R2<qw>:=PowerSeriesRing(KN2);

    if N1 eq 1 then
        assert M1`vinf eq 1;
        return [ [ Evaluate(R2!f[1],qw^(M2`widths[i])) : i in [1..M2`vinf]] : f in F];
    end if;
    assert N1 ne 1; 

    GL2:=GL2Ambient(N1);
    g:=GL2!g; 
    d:=Integers()!Determinant(g);
    data:=[ FindCuspData(M1, g*GL2!M2`cusps[i]*(GL2![1,0,0,d])^(-1) ) : i in [1..M2`vinf] ];

    powers_of_zetaN1_list:=[zeta_N1^i: i in [0..N1-1]];
    function power_of_zetaN1(i)
        return powers_of_zetaN1_list[(i mod N1)+1];
    end function;

    F_new:=[];
    for f in F do
        f_new:=[];
        for i2 in [1..M2`vinf] do
            i1:=data[i2][1];
            j :=data[i2][2];
            sgn:=data[i2][3];

            w1:=M1`widths[i1];
            w2:=M2`widths[i2];

            h:=R1!f[i1];

            e1:=N1 div w1;
            h:= ChangePrecision(sgn^wt * R1![ power_of_zetaN1(e1*j*i) * Coefficient(h,i) : i in [0..AbsolutePrecision(h)-1]],AbsolutePrecision(h));

            //zeta_w1:=zeta_N1^(N1 div w1);
            //h:=sgn^wt * Evaluate(h,zeta_w1^j*qw);   
            //assert IsWeaklyEqual(h,h_new); 

            h_new:=&+[ power_of_zetaN1((k-1)*d) * R1![Coefficient(h,i)[k]: i in [0..AbsolutePrecision(h)-1]] : k in [1..EulerPhi(N1)]];
            h:=ChangePrecision(h_new,AbsolutePrecision(h));

            //h:=R1![Conjugate(Coefficient(h,l),d): l in [0..AbsolutePrecision(h)-1]] + O(qw^AbsolutePrecision(h));

            p:=Floor(w2*(AbsolutePrecision(h)-1)/w1);
            h:=R1![ IsDivisibleBy(w1*b,w2) select Coefficient(h,(w1*b) div w2) else KN1!0 : b in [0..p]] + O(qw^(p+1));

            f_new cat:= [R2!h];
        end for;
        F_new cat:= [f_new];
    end for;
    return F_new;

end intrinsic;

intrinsic FindModularForms(k::RngIntElt, M::Rec : lll:=[true,false], saturation:=[true,true], prime_tolerance:=5) -> Rec
    {
    Input   
            k:  an integer > 1,
            M:  a modular curve given by a record of type "ModularCurveRec" (for example produced as output of 
                CreateModularCurveRec)  associated to an open subgroup G of GL(2,Zhat).  Let N be the level of G.

    Output:
            The record M with M`F updated to consist of a basis of the space of modular forms 
                        M_(k,G) := M_k(Gamma(N),Q(zeta_N))^G 
            as a vector space over Q.   

            Let d be the dimension of M_(k,G) over K_G (note: d=#M`F div M`KG_degree).
            The first d modular forms in the sequence M`F will be a basis of M_(k,G) over K_G (moreover, they are 
            linearly independent over C).
            
            A modular form is given as a sequence consisting of its q-expansion at each cusp (with the ordering of cusps
            coming from M`cusps).  Enough terms of the q-expansions of each modular form is computed so that it is 
            uniquely determined in M_(k,G).
            
            [M is returned with the following entries computed/updated:  k, dimMk, dimSk, prec_sturm, prec, F]

            The technical parameters "lll" and "saturation" can adjust when the function takes saturations and applies LLL to matrices.
            The technical parameter "prime_tolerance" is for adjusting how often we consider new primes when computing
            rank of matrices via reduction.

    }

    if Type(lll) eq Type(true) then lll:=[lll,lll]; end if;
    if Type(saturation) eq Type(true) then saturation:=[saturation,saturation]; end if;

    require k gt 1 : "Need weight at least 2.";
    delete M`F; //Remove any modular form data previously computed
    delete M`F0; 
    delete M`prec;
    delete M`modular_form_data;

    M`k:=k; 
    cusps:=M`cusps;
    widths:=M`widths;
    vinf:=M`vinf;

    // We first compute the dimensions of M_k(Gamma_G) and S_k(Gamma_G), respectively, over C.
    if k eq 2 then
        d:=M`genus+vinf-1;  // Shimura (Introduction to the arithmetic theory of automorphic_functions, Theorem 2.23)
        d0:=M`genus;
    elif IsEven(k) then
        d:=(k-1)*(M`genus-1) + (k/2)*vinf + M`v2*Floor(k/4) + M`v3*Floor(k/3);
        d0:=(k-1)*(M`genus-1) + (k/2-1)*vinf + M`v2*Floor(k/4) + M`v3*Floor(k/3);
    elif SL2ContainsNegativeOne(M`H) then
        d:=0; d0:=0;
    else
        u:=#{i: i in [1..#M`regular]| M`regular[i]};  u_:=#M`regular-u;
        d:=(k-1)*(M`genus-1)+(k/2)*u +(k-1)/2*u_ + M`v2*Floor(k/4) + M`v3*Floor(k/3);
        d0:=(k-1)*(M`genus-1)+((k-2)/2)*u +(k-1)/2*u_ + M`v2*Floor(k/4) + M`v3*Floor(k/3);
    end if;
    M`dimMk:=Integers()!d; 
    M`dimSk:=Integers()!d0;

    // When M_{k,G} = 0, the basis is empty and we are done!
    if M`dimMk eq 0 then      
        M`F:=[]; 
        M`prec_sturm:=1;
        M`prec:=[1: i in [1..M`vinf]]; 
        return M;
    end if;

    if M`sl2level gt 2 then
        m:=M`sl2level;
        H:=SL2Project(M`H,m);
        G:=M`G;
    else
        m:=4;
        H:=GL2Lift(SL2Project(M`H,M`sl2level),4);
        G:=GL2Lift(M`G,LCM(4,M`gl2level));
    end if;
    H`Order:=SL2Order(H);
    G`Order:=GL2Order(G);
    /*  At first the q-expansions at each cusp will be given as a power series in q^(1/m).

        We need m at least 3 so that our construction of modular forms in terms of 
        Eisenstein series will always work.
    */

    SL2:=SL2Ambient(m); 
    cusps:=[SL2!A: A in cusps];
        
    Km<zetam>:=CyclotomicField(m);  // This is also the field K_H
    Om:=RingOfIntegers(Km);

    // We compute all powers of zetam now (this saves time later!)
    powers_of_zetam_list:=[(Om!zetam)^i: i in [0..m-1]];
    function power_of_zetam(i)
        return powers_of_zetam_list[(i mod m)+1];
    end function;

    /*
        We will compute q-expansions at the cusps up to O(qm^(Prec)) with Prec chosen large enough 
        to distinguish elements of M_{k,H}, where qm=q^(1/m).

        We use a Sturm bound which bounds the order of vanishing at the cusps by Riemann-Roch.
    */
    sturm:=SturmPrecision(k,M);
    b0:=m*sturm/M`degree;     
    Prec :=Ceiling(b0);  
    if Prec eq b0 then 
        Prec:=Prec+1; 
    end if;
    M`prec_sturm:=[Ceiling(w*Prec/m) : w in M`widths]; 

    /*  We start constructing modular forms!

        Consider an element a=(a_1,...,a_k) in (Z/NZ)^(2k) = ((Z/NZ)^2)^k.
 
        To a, we construct the modular form f_a in M_{k,H} that is the sum of the functions  
                        E[a_1*h]*...*E[a_k*h, 
        over all h in H.   Note: f_a need not lie in M_{k,G}.  

        Using the action of G on M_{k,H}, as a vector space over K_G, we obtain from f_a many elements of M_{k,H}.  Galois descent 
        can be used to ensure the existence of a basis of M_{k,G} over K_G once we have enough modular forms.
                     
        We will compute modular forms until we find a basis for M_{k,H} over K_G; they will also be linearly independent over Km.

        We check that modular forms are linearly independent by checking independence modulo a large enough prime ideal of the ring 
        of integers of Km.   This is a little messy and we will consider more prime as we proceed searching for modular forms.
    */    
    
    // Reduction of G modulo m and a minimal sequence of generators; these are needed for the action of G on modular forms we find
    Gm:=GL2Project(G,m);
        Q,iQ:=quo<Gm|H>;
        A_,i_:=AbelianGroup(Q);
    gens_Gm_mod_H:=[(A_.i @@ i_) @@ iQ: i in Reverse([1..Ngens(A_)])];  // elements of Gm that generate Gm/H
    gens_Gm_mod_H_det:=[ Integers()!Determinant(g): g in gens_Gm_mod_H];

    // Data that we compute once and will reuse.
    GL2:=GL2Ambient(m);
    bb:=[ [ g*cusps[e]*GL2![1,0,0,1/Determinant(g)] : g in gens_Gm_mod_H] : e in [1..M`vinf] ];
    gens_Gm_mod_H_pairs:=[ [FindCuspData(M,bb[e][i]) : e in [1..M`vinf]] :  i in [1..#gens_Gm_mod_H]];   

    ee:=[m div w: w in M`widths];    
    R_Om<qw>:=PowerSeriesRing(Om);  

    function RightActionOnModularForm(f,triples,d)
        /* We have a modular form f with q-expansions given at the cusps;
           there is a matrix A with determinant 1 that produced "triple" using the function "FindCuspData";
           d is an integer.
           This function computes the q-expansions of f*B where B=A*[1,0;0,d].
        */
            R:=Parent(f[1]);
            ff:=[];
            for e in [1..M`vinf] do
                a1:=triples[e][1];
                a2:=triples[e][2];
                sgn:=triples[e][3];
                assert widths[e] eq widths[a1];                 
                f1:=sgn^M`k *  R_Om![power_of_zetam(ee[a1]*a2*i) * Coefficient(f[a1],i) : i in [0..(Prec-1) div ee[a1]]];
                f1:= &+[ power_of_zetam(m1*d) * R_Om![Coefficient(f1,i)[m1+1] : i in [0..(Prec-1) div ee[a1]]] : m1 in [0..EulerPhi(m)-1] ];
                ff cat:= [f1];
            end for;
            return ff;
    end function;

    E:=EisensteinFormsWeight1(m, Prec);  // Compute Eisenstein series of weight 1 and level m. 
 
    ConjH:=[Conjugate(H, A) :  A in cusps];     // Groups A^(-1)*H*A with A running over matrices in cusps.
    if SL2ContainsNegativeOne(H) then 
        e:=-1; 
    else 
        e:=1; 
    end if;
    U:=[sub<SL2| [[e,0,0,e], [1,M`widths[i],0,1]]> : i in [1..M`vinf]];  
    // The group U[i] will fix the q-expansion at the i-th cusp.


    RR:=[ [a^(-1): a in Transversal(ConjH[i],U[i])] : i in [1..M`vinf] ];      
    // RR[i] is a set of representatives of the cosets ConjH[i]/U[i].

    F1:=[]; //sequence of modular forms so far in M_{k,H}
    found_modular_forms:=[];  // sequence of the a's used construct f in F1
    B:=[];  // info of F1 in terms of vectors
    S:={};  // The set of a's we have already tried

    /*  
        We will need to compute the rank of matrices with coefficients in Om.
        Our approach is to compute the rank of its reduction at several small primes;
        the following keeps track of this info.
    */
    p:=2;       // Current prime
    Iota:=[];   // Sequence of embeddings of finite fields arising from our p
    counter:=0; // Keeps track of number of primes used; needed so we can occasionally consider more

    mult:=[(Prec-1) div ee[i] : i in [1..M`vinf]]; // precision needed at cusps

    V:=[];
    W:=[];
    W_tot:=[* *];
    WW:=[* *];

    handled:=[];
    conjugates:=[];

    // As we construct modular forms, we record all the computed coefficients for later use.
    vector_of_constructed_modular_forms:=[];

    done:=false;
    count:=0;
    while not done do   
        if count mod prime_tolerance eq 0 then  
            //TODO:  choose p so that residue field is smaller?

            // We compute the rank of matrices modulo more primes as we proceed without success.  
            // We consider prime ideals P of Om=Z[zeta_m].  We take it relative to m
            // and the cardinality of H.  
            repeat
                p:=NextPrime(p);
            until m mod p ne 0 and GL2Order(H) mod p ne 0;
            P:=Factorization(ideal<Om|[p]>)[1][1];
            FF_P,iota:=ResidueClassField(P);
            Iota cat:= [iota];
            
            V:=V cat [KSpace(FF_P,&+[a+1: a in mult])];
            W_tot:= W_tot cat [* sub<V[#V]|[]> *];
            WW:=WW cat [* [**] *];
            handled:=handled cat [[]];
        end if;
        count:=count+1;

        a:=random{a: a in RSpace(Integers(m),2*k) | a notin S and &and[ a[2*i-1] ne 0 or a[2*i] ne 0 : i in [1..k] ] };  
        //TODO: FIX: pretty quick but will freeze if set becomes empty (incredible unlikely!)

        S:=S join {a};
        a:=[ RSpace(Integers(m),2)![a[2*i-1],a[2*i]] : i in [1..k] ];

        // We construct the modular form arising from a.                 
        ff:=[];
        for i in [1..M`vinf] do             
            f:=&+[ &*[E[a[e]*tmp2]:e in [1..k]] where tmp2:=cusps[i]*h : h in RR[i]  ];                  
            e:=m div M`widths[i]; 
            m1:=(Prec-1) div e;  
            f:=#U[i] * &+[Coefficient(f,e*j)*qw^j : j in [0..m1]] + O(qw^(m1+1));
            ff:= ff cat [f];           
        end for;

        // We record the constructed modular form ff of M_{k,H}
        F1:=F1 cat [ff];
        found_modular_forms cat:= [ a ];
        v:=ModularFormToSequence(M,ff, mult,m);
        v:=Vector([Om!a: a in v]);
        vector_of_constructed_modular_forms cat:= [v];

        /*  There is a right action of Gm on M_{k,H} which we apply to ff to hopefully get many elements 
            of M_{k,H}.

            We keep track of the ongoing modular forms constructed until we have enough to span M_{k,H}.
            There is a bit of bookkeeping since we are proving linear independence of modular forms by reducing
            modulo an increasing large set of prime ideal of the ring of integers of Km.
        */
        conjugates:=conjugates cat [AssociativeArray()];
        assert #conjugates eq count;
        conjugates[count][[]]:=ff;
        for j in [1..#Iota] do // index of our prime ideals used
            for l in [1..count] do // index of our a's considered
                if l in handled[j] then
                    continue l;
                end if;
                v:=vector_of_constructed_modular_forms[l];
                v:=ChangeRing(v,Iota[j]);
                W:=sub<V[j]|[v]>;
                T:=[[]];
                for i in [1..#gens_Gm_mod_H] do
                    for b_ in T do
                        b0:=b_;
                        b:=b_ cat [1];                    
                        done_action:=false;
                        repeat
                            T:=T cat [b];
                            if b notin Keys(conjugates[l]) then                        
                                conjugates[l][b]:=RightActionOnModularForm( conjugates[l][b0], gens_Gm_mod_H_pairs[i], gens_Gm_mod_H_det[i]);
                            end if;                            
                            v:=Vector([Om!a: a in ModularFormToSequence(M,conjugates[l][b], mult,m)]);
                            v:=ChangeRing(v,Iota[j]);
                            if v notin W then 
                                W:=W + sub<V[j]|[v]>;
                            else
                                done_action:=true;
                            end if;
                            b0:=b;
                            b[#b]+:=1;
                        until done_action;
                    end for;            
                end for;
                handled[j]:=handled[j] cat [l];
                WW[j]:=WW[j] cat [* W *];
                W_tot[j]:=W_tot[j]+W;
            end for;
        end for;

        dim_seq:=[Dimension(W_tot[j]): j in [1..#Iota]];        
        done:=M`dimMk in dim_seq;
        // We are done when we have found a basis of M_{k,H} over Km (by reducing modulo a prime).
    end while;


    dims:=[];
    _,j:=Maximum(dim_seq);
    I:=[];
    U:=sub<V[j]|[]>;
    while Dimension(U) lt M`dimMk do
        U_:=[* W+U : W in WW[j] *];
        _,i:=Maximum([Dimension(W): W in U_]);
        U:=U_[i];
        dims:=dims cat [Dimension(U)];
        I:=I cat [i];
    end while;

    F1:=[F1[i]: i in I];
    found_modular_forms:=[found_modular_forms[i]: i in I];
    W_tot:=[W_tot: i in I];

    orbits:=[ [RightActionOnModularForm(f, M`Gm_mod_H_pairs[i], M`Gm_mod_H_det[i]): i in [1..#M`Gm_mod_H]] : f in F1 ];

    N:=#BaseRing(G); // Will be M`N when M`sl2level is at least 3
    KN<z>:=CyclotomicField(N);
    ON:=RingOfIntegers(KN);
    powers_of_z_list:=[(ON!z)^i: i in [0..N-1]];
    function power_of_z(i)
        return powers_of_z_list[(i mod N)+1];
    end function;

    R_ON<qw>:=PowerSeriesRing(ON); 

    constructed_modular_forms:=AssociativeArray();
    constructed_vectors:=AssociativeArray();

    basis_indices:=[];

    p:=Characteristic(Codomain(Iota[1]));
    P:=Factorization(ideal<ON|[p]>)[1][1];
    FF_P,iota:=ResidueClassField(P);

    done:=false;
    B:=[];

    repeat
        for j in [0..EulerPhi(N) div M`KG_degree -1] do
        
            for i in [1..#F1] do            
                if [i,j] in basis_indices then continue i; end if;  //this case already being used
        
                if [i,j] notin Keys(constructed_vectors) then
                    scalars:=[ &+[ power_of_z(d*j): d in M`cosets_det[l]] : l in [1..#M`Gm_mod_H] ];
                    fj:=[ &+[ scalars[l] * R_ON!orbits[i][l][e] : l in [1..#M`Gm_mod_H]]  :  e in [1..M`vinf] ];
                    constructed_modular_forms[[i,j]]:=fj;                
                    constructed_vectors[[i,j]]:=[ON!a: a in ModularFormToSequence(M,fj,mult,N)];
                end if;

                v:=constructed_vectors[[i,j]];
                B_:=ChangeRing(Matrix(B cat [v]),iota); 

                if Rank(B_) gt #B then
                    basis_indices:=basis_indices cat [[i,j]];
                    B:=B cat [v];
                    if #basis_indices eq M`dimMk then   
                        done:=true;
                        break j;
                    end if;
                end if;

            end for;
        end for;

        if not done then
            // something went wrong with our choice of prime p; we choose another!
            repeat
                p:=NextPrime(p);
                P:=Factorization(ideal<ON|[p]>)[1][1];
                FF_P,iota:=ResidueClassField(P);
            until N mod p ne 0 and GL2Order(M`G) mod p ne 0 and Rank(ChangeRing(Matrix(B),iota)) eq #B;
        end if;

    until done;

    assert #basis_indices eq M`dimMk;
    // We now have constructed a basis of M_{k,G} over K_G.
    F:=[constructed_modular_forms[a] : a in basis_indices];
   
    // Recorded the data of the modular forms constructed (can be used to increase precision of q-expansions)
    M`modular_form_data:=[ &cat[Eltseq(ChangeRing(a,Integers())): a in found_modular_forms[b[1]]] cat [b[2]] : b in basis_indices];


    mult:=[(Prec-1) div ee[i] : i in [1..M`vinf]]; 
    B0:=Matrix([ModularFormToSequence(M,f,mult,N : OverQ:=true) : f in F]);
    B1:=LCM([Denominator(B0[i,j]): i in [1..Nrows(B0)], j in [1..Ncols(B0)]])*B0;
    B1:=ChangeRing(B1,Integers());    
    if saturation[1] then
        B1:=Saturation(B1);
    end if;
    if lll[1] then
        B1:=LLL(B1 : Proof:=false);
    end if;

    // the following might be improved upon
    _,U0:=EchelonForm(B0);
    _,U1:=EchelonForm(ChangeRing(B1,Rationals()));
    C:=U1^(-1)*U0;
    //assert B1 eq C*B0;
    M`conversion_matrices:=[*C*];  // Record matrix for later computations.

    F:=[ SequenceToModularForm(M,v,mult,N : OverQ:=true) : v in Rows(B1) ];

    if M`KG_degree eq 1 then
        M`conversion_matrices:=M`conversion_matrices cat [* IdentityMatrix(Rationals(),M`dimMk) *];
        FF:=F;
    else
        // We want a basis of modular forms over Q.  This takes more work when KG is not Q.
        
        FF:=&cat[[[M`KG_integral_basis_cyclotomic[l]*f[i]: i in [1..M`vinf]]: l in [1..M`KG_degree]] : f in F];
        B0:=Matrix([ModularFormToSequence(M,f,mult,N : OverQ:=true) : f in FF]);

        B1:=LCM([Denominator(B0[i,j]): i in [1..Nrows(B0)], j in [1..Ncols(B0)]])*B0;
        B1:=ChangeRing(B1,Integers());
        if saturation[2] then
            B1:=Saturation(B1);
        end if;
        if lll[2] then 
            B1:=LLL(B1 :Proof:=false);  
        end if;

        // We want the first M`dimMk modular forms to be a basis over K_G.
        FF_:=[SequenceToModularForm(M,v,mult,N: OverQ:=true) : v in Rows(B1)];
        Q:=Matrix([ModularFormToSequence(M,f,mult,N) : f in FF_]);   //Matrix over KN
        Q_red:=ChangeRing(ChangeRing(Q,ON),iota); 
        assert Rank(Q_red) eq M`dimMk;
        I:=[];
        b:=[];
        for i in [1..Nrows(Q_red)] do
            b_:=b cat [Q_red[i]];
            if Rank(Matrix(b_)) gt #b then
                I:=I cat [i];
                b:=b_;
            end if;
            if #b eq M`dimMk then
                break i;
            end if; 
        end for;
        assert Rank(Matrix([Q_red[i]: i in I])) eq M`dimMk;
        B1:=Matrix([B1[i]: i in I] cat [B1[i]: i in [1..Nrows(B1)] | i notin I]);
        B1:=ChangeRing(B1,Rationals());
        FF:=[SequenceToModularForm(M,v,mult,N: OverQ:=true) : v in Rows(B1)];
        assert #FF eq M`KG_degree*M`dimMk;

        _,U0:=EchelonForm(B0);
        _,U1:=EchelonForm(ChangeRing(B1,Rationals()));
        C:=U1^(-1)*U0;
        //assert B1 eq C*B0;

        M`conversion_matrices:=M`conversion_matrices cat [*C*]; //record for later computations
    end if;

    M`F:=FF;
    M`prec:=[ Minimum([AbsolutePrecision(f[i]): f in M`F]) : i in [1..M`vinf] ];

    return  M;
end intrinsic;

intrinsic IncreaseModularFormPrecision(M::Rec, prec::SeqEnum) -> Rec
    {
    Input   M:      a modular curve given as a record of type "ModularCurveRec" for which 
                    M`F is defined and consist of modular forms (as outputted by "FindModularForms").
            prec:   a sequence of positive integers; one integer for each cusp.

    Output:
            Returns M with the q-expansions of the modular forms in M`F extended so that they are computed 
            at least up to O(q^(prec[i]/w_i) at the i-th cusp of M, where w_i is the width of the i-th cusp.  

            This also extends the modular forms in M`F0 if present.
    }

    if not assigned M`k or not assigned M`F then
        // nothing to do
        return M; 
    end if;
    assert assigned M`prec;

    // For our approach, we want to increase the precision so that it agrees at all cusps in the same Gal_(K_G)-orbit.
    for O in M`cusp_orbits do
        max:=Maximum([prec[i]: i in O]);
        for i in O do  
            prec[i]:=max;
        end for;
    end for;

    if #M`F eq 0 then
        // 0-dimensional space of modular forms
        M`prec:=[Maximum(M`prec[i],prec[i]) : i in [1..M`vinf]];
        return M;
    end if;

    // We keep track of the cusps for which we need to improve the q-expansions
    I:=[i: i in [1..M`vinf] | prec[i] gt M`prec[i]];
    if #I eq 0 then 
        return M; // q-expansions already have enough terms!
    end if;
    
    prec1:=[ i in I select Maximum(prec[i],1) else 1 : i in [1..M`vinf]];   

    if M`sl2level gt 2 then
        m:=M`sl2level;
        H:=SL2Project(M`H,m);
        G:=M`G;
    else
        m:=4;
        H:=GL2Lift(SL2Project(M`H,M`sl2level),4);
        G:=GL2Lift(M`G,LCM(4,M`gl2level));
    end if;
    H`Order:=SL2Order(H);
    G`Order:=GL2Order(G);


    N:=#BaseRing(G);  // Will be M`N when M`sl2level is at least 3
    k:=M`k;
    cusps:=M`cusps;
    widths:=M`widths;

    GL2:=GL2Ambient(m);
    SL2:=SL2Ambient(m);     
    ee:=[m div w: w in M`widths]; 
        
    Km<zetam>:=CyclotomicField(m);  // This is also the field K_H
    Om:=RingOfIntegers(Km);
    powers_of_zetam_list:=[(Om!zetam)^i: i in [0..m-1]];
    function power_of_zetam(i)
        // Output is just "zetam^i" but is faster.
        return powers_of_zetam_list[(i mod m)+1];
    end function;

    KN<z>:=CyclotomicField(N);
    ON:=RingOfIntegers(KN);
    powers_of_z_list:=[(ON!z)^i: i in [0..N-1]];
    function power_of_z(i)
        return powers_of_z_list[(i mod N)+1];
    end function;
    R_ON<qw>:=PowerSeriesRing(ON); 
    R_Om<qw>:=PowerSeriesRing(Om); 
    R_KN<qw>:=PowerSeriesRing(KN);
    
    function RightActionOnModularForm(f,pairs,d)
            R:=Parent(f[1]);
            ff:=[];
            for e in [1..M`vinf] do
                a1:=pairs[e][1];
                a2:=pairs[e][2];
                assert widths[e] eq widths[a1]; 
                sgn:=pairs[e][3];
                f1:=ChangePrecision(sgn^M`k *  R_Om![power_of_zetam(ee[a1]*a2*i) * Coefficient(f[a1],i) : i in [0..AbsolutePrecision(f[a1])-1]], AbsolutePrecision(f[a1]));
                f1:= ChangePrecision(&+[ power_of_zetam(m1*d) * R_Om![Coefficient(f1,i)[m1+1] : i in [0..AbsolutePrecision(f1)-1]] : m1 in [0..EulerPhi(m)-1] ],AbsolutePrecision(f1));
                ff cat:= [f1];
            end for;
            return ff;
    end function;
    

    // Compute Eisenstein series of weight 1 and level m to required increased precision     
    E:=EisensteinFormsWeight1(m, Maximum([prec1[i]*(m div M`widths[i]) : i in [1..M`vinf]]));  

    cusps1:=[SL2Ambient(m)!a: a in cusps];
    ConjH:=[Conjugate(H, A) :  A in cusps1];     // Groups A^(-1)*H*A with A running over matrices in cusps.
    if SL2ContainsNegativeOne(H) then e:=-1; else e:=1; end if;
    U:=[sub<SL2| [[e,0,0,e], [1,M`widths[i],0,1]]> : i in [1..#cusps]];
    if SL2ContainsNegativeOne(H) eq false then
        U:=[U[i] meet ConjH[i] : i in [1..#cusps]];
    end if;
    RR:=[ [a^(-1): a in Transversal(ConjH[i],U[i])] : i in [1..#cusps] ];  // RR[i] is a set of representatives of the cosets ConjH[i]/U[i].

    R_Km<qw>:=PowerSeriesRing(Km);  
    F:=[];
    orbits:=AssociativeArray();

    /* 
        We now compute a basis of M_{k,H} over K_m with increased precision.  We use a basis has already 
        been constructed and is given by "M`modular_form_data".   
    */
    for data in M`modular_form_data do
        a:=[ ChangeRing(Vector([data[2*i-1],data[2*i]]),Integers(m)) : i in [1..k] ];
        j:=data[2*k+1];
    
        if a notin Keys(orbits) then
            // We construct the modular form arising from a.                 
            ff:=[];
            for i in [1..#cusps] do  
                e:=m div M`widths[i];                 
                
                f:=&+[ &*[ ChangePrecision( E[a[e]*tmp2], prec1[i]*m div M`widths[i]):e in [1..k]] where tmp2:=cusps1[i]*h : h in RR[i]  ]; 
                f:=ChangePrecision(#U[i] * &+[Coefficient(f,e*j)*qw^j : j in [0..prec1[i]-1]], prec1[i]);

                ff:= ff cat [f];            
            end for;
            orbits[a]:=[RightActionOnModularForm(ff, M`Gm_mod_H_pairs[i], M`Gm_mod_H_det[i]): i in [1..#M`Gm_mod_H]];
        end if;

        scalars:=[ &+[ power_of_z(d*j): d in M`cosets_det[l]] : l in [1..#M`Gm_mod_H] ];
        fj:=[ R_KN!(&+[ scalars[l] * R_ON!orbits[a][l][e] : l in [1..#M`Gm_mod_H]])  :  e in [1..M`vinf] ];  // could be sped up with tricks
        F:=F cat [fj];
    end for;

    A:=Matrix([ModularFormToSequence(M,f, [p-1: p in prec1],M`N :OverQ:=true) : f in F]);
    C:=M`conversion_matrices[1];  // matrix already found that makes our basis look nicer
    A:=C*A;
    F:=[SequenceToModularForm(M,v, [p-1: p in prec1],M`N :OverQ:=true) : v in Rows(A)];

    if M`KG_degree gt 1 then
        F:=&cat[[[M`KG_integral_basis_cyclotomic[l]*f[i]: i in [1..M`vinf]]: l in [1..M`KG_degree]] : f in F];
        A:=Matrix([ModularFormToSequence(M,f, [p-1: p in prec1],M`N :OverQ:=true) : f in F]);
        C:=M`conversion_matrices[2];
        A:=C*A;
        F:=[SequenceToModularForm(M,v, [p-1: p in prec1],M`N :OverQ:=true) : v in Rows(A)];
    end if;

    // Update using the highest precision estimate available at each cusp.
    M`F:=[  [ AbsolutePrecision(F[j][e]) ge AbsolutePrecision(M`F[j][e]) select F[j][e] else M`F[j][e] : e in [1..M`vinf] ]  : j in [1..#M`F] ];
    
    // Update the improved precisions
    M`prec:=[Minimum([AbsolutePrecision(f[i]): f in M`F]) : i in [1..M`vinf]];

    assert &and[ M`prec[i] ge prec[i] : i in [1..M`vinf]];

    // Update the precision of modular forms with vanishing conditions (if they exist)
    if assigned M`F0 and #M`F0 ne 0 then
        if #M`F0 eq #M`F and #M`conversion_matrices eq 2 then 
            M`F0:=M`F; 
        else
            assert #M`conversion_matrices eq 4;
            C1:=ChangeRing(M`conversion_matrices[3],Rationals());
            C2:=ChangeRing(M`conversion_matrices[4],Rationals());
            // The above already computed matrices tell us how to recover M`F0 from M`F
            B:=C2*C1*A;
            F0:=[SequenceToModularForm(M,v, [p-1: p in prec1],M`N :OverQ:=true) : v in Rows(B)];

            // Update using the highest precision estimate available at each cusp.
            M`F0:=[  [ AbsolutePrecision(F0[j][e]) ge AbsolutePrecision(M`F0[j][e]) select F0[j][e] else M`F0[j][e] : e in [1..M`vinf] ]  : j in [1..#M`F0] ];
        end if;
    end if;

    return M;   
end intrinsic;

intrinsic IncreaseModularFormPrecision(M::Rec, prec::RngIntElt) -> Rec  
    {
        Same as other version but q-expansions at all cusps are computed up to O(q^(prec/m)), where
        m=M`sl2level and prec is a nonnegative integer.
    }
    return IncreaseModularFormPrecision(M,[Ceiling(M`widths[i]*prec/M`sl2level): i in [1..M`vinf]]);
end intrinsic;

intrinsic AutomorphismOfModularForms(M::Rec,F::SeqEnum,g::GrpMatElt : OverQ:=false, k:=0)-> SeqEnum 
    {
        Input:  a modular curve M=X_G, a sequence F of modular forms in M_(k,G) for some k>1 that are linearly 
                independent over K_G, and a matrix g in GL(2,Zhat) that lies in the normalizer of G and acts on the K_G-vector 
                V space spanned by F.
                (The parameter "k" is an integer congruent to k modulo 2.)

        Output: the matrix C that describes the action of g on V in terms of the basis F; it will be a
                square matrix with entries in K_G.

        When "OverQ" is set to true, then it performs as described above except with K_G replaced by Q.
    }
    Fnew:=ConvertModularFormExpansions(M,M,F,g : wt:=k);
   
    mult:=[(M`prec_sturm[i]-1) * (M`sl2level div M`widths[i]) : i in [1..M`vinf]];    // improve mult?
    A:=Matrix([ModularFormToSequence(M,f, mult,M`N : OverQ:=OverQ) : f in F]);
    B:=Matrix([ModularFormToSequence(M,f, mult,M`N : OverQ:=OverQ) : f in Fnew]);   
    
    C:=Solution(A,B); 
    // Is this fast enough? Can compute in a different way if needed.

    if OverQ then
        C:=ChangeRing(C,Rationals());
    else
        C:=ChangeRing(C,M`KG);
    end if;

    return C;
end intrinsic;

intrinsic FindMorphismCanonical(M,M0)-> SeqEnum 
    {
        Input: Modular curves M and M0 corresponding to open subgroups G and G0 of 
                GL(2,Zhat), respectively.  Assume that G is a subgroup of G0 and 
                hence we have a natural morphism X_G -> X_G0.

                When X_G and X_G0 are both given by a canonical model, this morphism 
                is just a linear projection.
        Output: The tuple of linear polynomials corresponding to the projection.
    }

    is_canonical :=M`genus ge 3 and M`k eq 2 and Set(M`mult) eq {1};
    is_canonical0:=M0`genus ge 3 and M0`k eq 2 and Set(M0`mult) eq {1};
    assert is_canonical;
    assert is_canonical0;

    h:=ConvertModularFormExpansions(M0,M,[M0`F0[i]: i in [1..M0`genus]],[1,0,0,1]);
    mult:=[ Minimum([AbsolutePrecision(f[i]):f in M`F0 cat h])-1 : i in [1..M`vinf] ];
    
    F:=[M`F0[i]: i in [1..M`genus]];
    F:=&cat[[ [b*f[i]: i in [1..M`vinf]] : b in M`KG_integral_basis_cyclotomic ] : f in F];
    A:=[ ModularFormToSequence(M, f, mult, M`N : OverQ:=true) : f in F ];
    A:=Matrix(A);
    if Rank(A) ne M`KG_degree*M`genus then
        // Not enough terms of q-expansions of modular forms on M0.
        // We increase precision and try again.
        M0:=IncreaseModularFormPrecision(M,[i+2:i in M0`prec]);  //ad hoc
        return FindMorphismCanonical(M,M0);
    end if;

    B:=[ ModularFormToSequence(M, f, mult, M`N : OverQ:=true) : f in h ];
    B:=Matrix(B);

    C:=Solution(A,B);

    D:=[[ &+[C[e,M`KG_degree*(j-1)+i]*M`KG_integral_basis[i] : i in [1..M`KG_degree]] : j in [1..M`genus]] : e in [1..#h]];
    D:=Matrix(D);
    
    //CHECKS  TODO:remove
    for i in [1..#h] do
    for e in [1..M`vinf] do
        assert IsWeaklyZero(h[i][e] - &+[D[i,j]*M`F0[j][e]: j in [1..M`genus]]);
    end for;
    end for;

    Pol<[x]>:=PolynomialRing(M`KG,M`genus);

    morphism:=[&+[D[i,j]*x[j]: j in [1..M`genus]] : i in [1..#h]];
    return morphism;
end intrinsic;


intrinsic FindMorphism(M,M0 : homogeneous:=true, prec0:=0, prec_delta:=10, Id:=[*[]*], mon1:=[* *])-> SeqEnum
    {
        Warning: this function is still very experimental!

        Input: 
                Modular curves M and M0 corresponding to open subgroups G and G0 of 
                GL(2,Zhat), respectively.  Assume that G is a subgroup of G0 and 
                hence we have a natural morphism X_G -> X_G0 defined over K_G.  
                Assume also that G contains -I.

                We assume that models of X_G and X_G0 have already been computed.
        Output: With respect to their model, we give a tuple of homomogenous polynomials 
                that corresponds to the morphism.

        Suppose that the parameter "homogenous" is set to false and the model of X_G or X_G0 is not canonical. Then a tuple of 
        the form [1,F_1,...,F_n] is returned with F_i in the function field of X_G. 
        Clearing denominators will give a tuple of homogenous polynomials as above.   The 
        function works by computing these F_i first and this express may me nicer for many purposes.

        The parameters "prec0" and "prec_delta" are for initial precision and how much to increase it when more is needed;
        these should be left alone at first.
        The parameters "Id" and "mon1" should be left alone; they are for keeping computations when we apply the function
        recursively.
    }
    assert M`N mod M0`N eq 0;
    assert M`G subset GL2Lift(M0`G,M`N);

    assert assigned M`psi and assigned M`model_degree and assigned M`F0;
    assert assigned M0`psi and assigned M0`model_degree and assigned M0`F0;

    is_canonical :=M`genus ge 3 and M`k eq 2 and Set(M`mult) eq {1};
    is_canonical0:=M0`genus ge 3 and M0`k eq 2 and Set(M0`mult) eq {1};
    if is_canonical and is_canonical0 then
        // When both models are canonical, the morphism is a linear projection.
        return FindMorphismCanonical(M,M0);
    end if;

    // We will look for a morphism defined over K_G.   For many of the computations,
    // it will be useful to work modulo a well chosen prime Q.
    //TODO: choice??  ensure no issues
    OO:=RingOfIntegers(M`KG);
    disc:=Integers()!Discriminant(M`KG);
    q:=2;
    repeat
        q:=NextPrime(q);
    until M`N mod q ne 0 and disc mod q ne 0;    
    Q:=Factorization(ideal<OO|[q]>)[1][1];
    FF_Q,iota:=ResidueClassField(Q);

    // We increase the precision
    prec:=Minimum([ (M`sl2level div M`widths[i])*M`prec[i] : i in [1..M`vinf]]  cat [ (M0`sl2level div M0`widths[i])*M0`prec[i] : i in [1..M0`vinf]]);
    prec:=Maximum(prec,prec0);
    M:=IncreaseModularFormPrecision(M,prec);
    M0:=IncreaseModularFormPrecision(M0,prec);

    // Modular forms describing model of M0 converted to M
    h:=ConvertModularFormExpansions(M0,M,M0`F0,[1,0,0,1]); 

    deg_h:=M0`model_degree * (M`index div M0`index);
    // Consider the quotient of two modular forms in the sequence h;
    // then "deg_h" bounds the total number of zeros and poles as a rational function on M

    n:=#M`F0 div M`KG_degree;
    K:=M`KG;
    Pol_K<[y]>:=PolynomialRing(K,n); 

    // ideal of Pol_K given by our model of M
    // I_gen:=[Pol_K!p: p in M`psi];
    // Now work over finite field instead!

    Pol_FF<[x]>:=PolynomialRing(FF_Q,n);
    I_gen:=[Pol_FF!pol :pol in M`psi];
 
    M_has_canonical_model:=M`genus ge 3 and M`k eq 2 and Set(M`mult) eq {1};

    if M_has_canonical_model eq false then
        //For now, we compute the Hilbert series when we do not have a canonical model.
        //TODO: check running time
        I:=ideal<Pol_FF|I_gen>;
        Rs<t>:=PowerSeriesRing(Rationals());
        HS:=HilbertSeries(Submodule(I));
    end if;

    /*  
        Idea:
            Let f_1,..,f_r be the basis of modular forms that give rise to the model of M.
            Let h_1,..,h_s be the basis of modular forms that give rise to the model of M0.
            For i=2,..s, we consider h_i/h_1 which gives a rational functions on M.  We will have
                    h_i/h_1 = F_1(f_1,..,f_r)/F_2(f_1,..,f_r)
            where F_1,F_2 are homomogenous polynomials of the same degree d.
            We start with d=0 and increase d until we find such a relation!

            Observations:
                We need only look at F_1 and F_2 in the space of homogenous polynomials of 
                degree d modulo the space of degree d relations of M.

                We can look at the q-expansion of the cusps for the expression:
                    h_i*F_2(f_1,..,f_r) - h_1*F_1(f_1,..,f_r);
                since these are cusp forms, enough vanishing will prove that it is 0. 
    */



    d:=0;
    
    Id  :=[* *];
    mon1:=[* *];

    mon :=[* *];
    AA:=[* *];

    /*
        Consider the ideal I in Pol_K corresponding to the model of the curve M.
        For each integer m, we have the graded component I_m of degree m.

        We compute a sequence "Id" so that Id[m] is a basis of I_m over M`KG.
        We compute a sequence "mon1" so that mon1[m] is a basis of (Pol_K)_m/I_m.
    */
    #Id;
    M_F0:=[M`F0[i]: i in [1..#M`F0 div M`KG_degree]];
    assert #M_F0 * M`KG_degree eq #M`F0;

    morphism:=[];  //Keep track of F_1/F_2 


    for r in [2..#M0`F0 div M0`KG_degree] do
        done:=false;

        while not done do
            d:=d+1;
       
            if M_has_canonical_model then
                if d ge 2 then
                    dQ:=Binomial(M`genus+d-1,d)-(2*d-1)*(M`genus-1);
                    // dimension of homogeneous relations of degree d              
                else
                    dQ:=0;
                    // dimension of homogeneous relations of degree d 
                end if;
            else
                dQ:=Integers()!Coefficient(Rs!Evaluate(HS,t+O(t^(d+1))),d);
                // dimension of homogeneous relations of degree d 
            end if;

            //Find the next Id (if needed)
            if #Id eq d-1 then
                mon:= mon cat [* MonomialsOfWeightedDegree(Pol_FF,d) *];
                assert #mon eq d;
                //A:=[ Vector([MonomialCoefficient(p,m) : m in mon[d]]) : p in I_gen | Degree(p) eq d];  

                B:=[ [MonomialCoefficient(p,m) : m in mon[d]] : p in I_gen | Degree(p) eq d];  

                if d gt 1 and dQ ne 0 then
                    B:=B cat [[MonomialCoefficient(x[i]*p,m) : m in mon[d]] :  i in [1..n], p in Id[d-1]];
                    B:=Matrix(B);
                    C:=EchelonForm(Transpose(B));
                    //assert Rank(C) eq dQ;  TODO: CHECK?!
                    pivots:=[ Minimum([j: j in [1..Ncols(C)] | C[i,j] ne 0]) :  i in [1..dQ]];
                    B:=[B[i]: i in pivots]; // chose rows of B that span a space of the same dimension

                end if;

                assert #B eq dQ;
                AA:=AA cat [* B *];
                Id:=Id cat [* [ Pol_FF!(&+[w[i]*mon[d][i]: i in [1..#mon[d]]]) : w in B] *];
            end if;
            
            if #mon1 lt d then //ERAY WHAT IS GOING ON HERE
                if d*M`model_degree ge deg_h then

                    // Find a basis mon1[d] of (Pol_K)_d/I_d. 
                    V:=KSpace(FF_Q,#mon[d]);
                    W:=sub<V|AA[d]>;
                    mon_:=[];
                    for p in mon[d] do
                        v:=Vector([MonomialCoefficient(p,m) : m in mon[d]]);
                        if v notin W then
                            W:=W + sub<V|[v]>;
                            mon_:=mon_ cat [p];
                        end if;
                        if Dimension(W) eq Dimension(V) then
                            break p; 
                        end if;
                    end for;
                    assert Dimension(W) eq Dimension(V);
                    exponents_mon_:=[Exponents(m): m in mon_];
                    mon1:= mon1 cat [* [&*[y[i]^a[i]: i in [1..n]] : a in exponents_mon_] *];
                else
                    mon1:=mon1 cat [* [] *];
                end if;
            end if;         


            if d*M`model_degree ge deg_h then
                
                B:=[];
                J:=Sort([O[1]:O in M`cusp_orbits]); 
                for j in J do
                    beta:=[Evaluate(m,[f[j]: f in M_F0]) : m in mon1[d]];
                    beta:=&cat[ [b*f: b in M`KG_integral_basis_cyclotomic] : f in beta];

                    s:=[h[1][j]*b : b in beta] cat [-h[r][j]*b : b in beta];
                    e:=Minimum([AbsolutePrecision(f): f in s]);
                    B:=B cat [ [ Coefficient(f,i)[k]: f in s] : i in [0..e-1], k in [1..EulerPhi(M`N)] ];  
                    //could use coefficients over smaller field here
                end for;
            

                B:=Matrix(B);
                B:=ChangeRing(Denominator(B)*B,Integers());

                C:=Matrix(Basis(NullspaceOfTranspose(B)));
                C:=LLL(C : Proof:=false);
                S:=[ [&+[v[M`KG_degree*(i-1)+j] * M`KG_integral_basis[j]*mon1[d][i]: i in [1..#mon1[d]], j in [1..M`KG_degree]],
                      &+[v[M`KG_degree*(i-1)+j + #mon1[d]*M`KG_degree] * M`KG_integral_basis[j]*mon1[d][i]: i in [1..#mon1[d]], j in [1..M`KG_degree]]] : v in Rows(C)];
                      
                if #S ge 1 then
                    // number of poles is at most  
                    upper_bound_on_number_of_poles:= d*M`model_degree + deg_h;

                    a:=S[1];
                    zeros:=0;
                    for j in J do
                        den:=Evaluate(a[2],[f[j]: f in M_F0]);
                        if IsWeaklyZero(den) or IsWeaklyZero(h[1][j]) then 
                            continue j; 
                        end if;
                        num:=Evaluate(a[1],[f[j]: f in M_F0]);
                        //h[r][j]*den - h[1][j]*num;
                        v:=Valuation(num/den  - h[r][j]/h[1][j])-1; 
                        if v ge 1 then 
                            orbit_size:= #M`cusp_orbits[M`cusp_to_orbit[j]];
                            zeros:=zeros+ v * orbit_size;
                        end if;                    
                    end for;
              
                    if zeros le upper_bound_on_number_of_poles then
                        // Not enough info to provable find morphism.
                        // We increase precision and try again
                        return FindMorphism(M,M0 :homogeneous:=homogeneous, prec0:=prec+prec_delta, prec_delta:=prec_delta, Id:=Id, mon1:=mon1);
                    end if;

                    done:=true;
                end if;
            end if;
        end while;

        a:=S[1];
        morphism:=morphism cat [a];
    end for;
    
    if not homogeneous then
        return [1] cat [a[1]/a[2]: a in morphism];
    end if;

    morphism:= [&*([1] cat [morphism[j][2]: j in [1..#morphism]]) : i in [1..#morphism]]
    cat [ morphism[i][1]* &*([1] cat [morphism[j][2]: j in [1..#morphism] | j ne i]) : i in [1..#morphism]];

    Pol_K<[x]>:=PolynomialRing(K,n); 
    morphism:=[Pol_K!f: f in morphism];

    return morphism;
end intrinsic;




//func element given by a seq of expansions at the cusps.
//want to write it as a ratio

intrinsic FindRatio(M,M0, tryingdegs : homogeneous:=true, prec0:=0, prec_delta:=10, Id:=[* *], mon1:=[* *],mon:=[* *],AA:=[* *])-> SeqEnum
    {
        Warning: this function is still very experimental!

        Input: 
                Modular curves M and M0 corresponding to open subgroups G and G0 of 
                GL(2,Zhat), respectively.  Assume that G is a subgroup of G0 and 
                hence we have a natural morphism X_G -> X_G0 defined over K_G.  
                Assume also that G contains -I.

                We assume that models of X_G and X_G0 have already been computed.
        Output: With respect to their model, we give a tuple of homomogenous polynomials 
                that corresponds to the morphism.

        Suppose that the parameter "homogenous" is set to false and the model of X_G or X_G0 is not canonical. Then a tuple of 
        the form [1,F_1,...,F_n] is returned with F_i in the function field of X_G. 
        Clearing denominators will give a tuple of homogenous polynomials as above.   The 
        function works by computing these F_i first and this express may me nicer for many purposes.

        The parameters "prec0" and "prec_delta" are for initial precision and how much to increase it when more is needed;
        these should be left alone at first.
        The parameters "Id" and "mon1" should be left alone; they are for keeping computations when we apply the function
        recursively.
    }

    M0:=FindModularForms(3,M0);
    prec:=Minimum([ (M`sl2level div M`widths[i])*M`prec[i] : i in [1..M`vinf]]) ;
    prec:=Maximum(prec,prec0);
    M0:=IncreaseModularFormPrecision(M0,prec);
    assert assigned M`psi and assigned M`model_degree and assigned M`F0;
     E6list:=[];
    for c in [1..#M0`cusps] do
        w:=M0`widths[c];
        FFFF<qw> := LaurentSeriesRing(Rationals());
        E6 := Eisenstein(6,qw : Precision := Ceiling((M0`prec[c]+2*w)/w));
        E6 := Evaluate(E6,qw^w);
        E6list:=E6list cat [E6];
    end for;
        "E6";
        E6list;
        modforms3 := [ M0`F[1][c]^2 : c in [1..#M0`cusps]]; // weight 6

        f:=ConvertModularFormExpansions(M, M0, [modforms3],[1,0,0,1])[1];
        "f is";
        f;
        modforms3_new := [f[t]/E6list[t]: t in [1..#M`cusps]];
        toc:=modforms3_new;
        "toc is";
        toc;

    // We will look for a morphism defined over K_G.   For many of the computations,
    // it will be useful to work modulo a well chosen prime Q.
    //TODO: choice??  ensure no issues
    OO:=RingOfIntegers(M`KG);
    disc:=Integers()!Discriminant(M`KG);
    q:=2;
    repeat
        q:=NextPrime(q);
    until M`N mod q ne 0 and disc mod q ne 0;    
    Q:=Factorization(ideal<OO|[q]>)[1][1];
    FF_Q,iota:=ResidueClassField(Q);

    // We increase the precision
    prec:=Minimum([ (M`sl2level div M`widths[i])*M`prec[i] : i in [1..M`vinf]]) ;
    prec:=Maximum(prec,prec0);
    M:=IncreaseModularFormPrecision(M,prec);

    // Modular forms describing model of M0 converted to M
    printf "prec is %o\n",prec;

    //deg_h:=M0`model_degree * (M`index div M0`index);
    deg_toc:=M`model_degree * tryingdegs;
    // Consider the quotient of two modular forms in the sequence h;
    // then "deg_h" bounds the total number of zeros and poles as a rational function on M

    n:=#M`F0 div M`KG_degree;
    K:=M`KG;
    Pol_K<[y]>:=PolynomialRing(K,n); 

    // ideal of Pol_K given by our model of M
    // I_gen:=[Pol_K!p: p in M`psi];
    // Now work over finite field instead!

    Pol_FF<[x]>:=PolynomialRing(FF_Q,n);
    I_gen:=[Pol_FF!pol :pol in M`psi];
 
  
        //For now, we compute the Hilbert series when we do not have a canonical model.
        //TODO: check running time
        I:=ideal<Pol_FF|I_gen>;
        Rs<t>:=PowerSeriesRing(Rationals());
        HS:=HilbertSeries(Submodule(I));


    /*  
        Idea:
            Let f_1,..,f_r be the basis of modular forms that give rise to the model of M.
            Let h_1,..,h_s be the basis of modular forms that give rise to the model of M0.
            For i=2,..s, we consider h_i/h_1 which gives a rational functions on M.  We will have
                    h_i/h_1 = F_1(f_1,..,f_r)/F_2(f_1,..,f_r)
            where F_1,F_2 are homomogenous polynomials of the same degree d.
            We start with d=0 and increase d until we find such a relation!

            Observations:
                We need only look at F_1 and F_2 in the space of homogenous polynomials of 
                degree d modulo the space of degree d relations of M.

                We can look at the q-expansion of the cusps for the expression:
                    h_i*F_2(f_1,..,f_r) - h_1*F_1(f_1,..,f_r);
                since these are cusp forms, enough vanishing will prove that it is 0. 
    */



    d:=0;
    
    //Id  :=[* *];
    //mon1:=[* *];

    //mon :=[* *];
    //AA:=[* *];

    /*
        Consider the ideal I in Pol_K corresponding to the model of the curve M.
        For each integer m, we have the graded component I_m of degree m.

        We compute a sequence "Id" so that Id[m] is a basis of I_m over M`KG.
        We compute a sequence "mon1" so that mon1[m] is a basis of (Pol_K)_m/I_m.
    */

    M_F0:=[M`F0[i]: i in [1..#M`F0 div M`KG_degree]];
    assert #M_F0 * M`KG_degree eq #M`F0;

    morphism:=[];  //Keep track of F_1/F_2 


    
        done:=false;

        while not done do
            d:=d+1;
            printf "increased d to %o\n",d;

                dQ:=Integers()!Coefficient(Rs!Evaluate(HS,t+O(t^(d+1))),d);
                // dimension of homogeneous relations of degree d 

            //Find the next Id (if needed)
            if #Id eq d-1 then
                mon:= mon cat [* MonomialsOfWeightedDegree(Pol_FF,d) *];
                assert #mon eq d;
                //A:=[ Vector([MonomialCoefficient(p,m) : m in mon[d]]) : p in I_gen | Degree(p) eq d];  

                B:=[ [MonomialCoefficient(p,m) : m in mon[d]] : p in I_gen | Degree(p) eq d];  

                if d gt 1 and dQ ne 0 then
                    B:=B cat [[MonomialCoefficient(x[i]*p,m) : m in mon[d]] :  i in [1..n], p in Id[d-1]];
                    B:=Matrix(B);
                    C:=EchelonForm(Transpose(B));
                    //assert Rank(C) eq dQ;  TODO: CHECK?!
                    pivots:=[ Minimum([j: j in [1..Ncols(C)] | C[i,j] ne 0]) :  i in [1..dQ]];
                    B:=[B[i]: i in pivots]; // chose rows of B that span a space of the same dimension

                end if;

                assert #B eq dQ;
                AA:=AA cat [* B *];
                Id:=Id cat [* [ Pol_FF!(&+[w[i]*mon[d][i]: i in [1..#mon[d]]]) : w in B] *];
            end if;
            
            if #mon1 lt d then //ERAY WHAT IS GOING ON HERE
                if d*M`model_degree ge deg_toc then

                    // Find a basis mon1[d] of (Pol_K)_d/I_d. 
                    V:=KSpace(FF_Q,#mon[d]);
                    W:=sub<V|AA[d]>;
                    mon_:=[];
                    for p in mon[d] do
                        v:=Vector([MonomialCoefficient(p,m) : m in mon[d]]);
                        if v notin W then
                            W:=W + sub<V|[v]>;
                            mon_:=mon_ cat [p];
                        end if;
                        if Dimension(W) eq Dimension(V) then
                            break p; 
                        end if;
                    end for;
                    assert Dimension(W) eq Dimension(V);
                    exponents_mon_:=[Exponents(m): m in mon_];
                    mon1:= mon1 cat [* [&*[y[i]^a[i]: i in [1..n]] : a in exponents_mon_] *];
                else
                    mon1:=mon1 cat [* [] *];
                end if;
            end if;         


            if d*M`model_degree ge deg_toc then
                
                B:=[];
                J:=Sort([O[1]:O in M`cusp_orbits]); 
                for j in J do
                    beta:=[Evaluate(m,[f[j]: f in M_F0]) : m in mon1[d]];
                    beta:=&cat[ [b*f: b in M`KG_integral_basis_cyclotomic] : f in beta];

                    s:=[E6list[j]*b : b in beta] cat [-f[j]*b : b in beta];
                    e:=Minimum([AbsolutePrecision(f): f in s]);
                    B:=B cat [ [ Coefficient(f,i)[k]: f in s] : i in [0..e-1], k in [1..EulerPhi(M`N)] ];  
                    //could use coefficients over smaller field here
                end for;
            

                B:=Matrix(B);
                B:=ChangeRing(Denominator(B)*B,Integers());

                C:=Matrix(Basis(NullspaceOfTranspose(B)));
                C:=LLL(C : Proof:=false);
                S:=[ [&+[v[M`KG_degree*(i-1)+j] * M`KG_integral_basis[j]*mon1[d][i]: i in [1..#mon1[d]], j in [1..M`KG_degree]],
                      &+[v[M`KG_degree*(i-1)+j + #mon1[d]*M`KG_degree] * M`KG_integral_basis[j]*mon1[d][i]: i in [1..#mon1[d]], j in [1..M`KG_degree]]] : v in Rows(C)];
                      
                if #S ge 1 then
                    // number of poles is at most  
                    upper_bound_on_number_of_poles:= d*M`model_degree + deg_toc;
                    "sda";
                    upper_bound_on_number_of_poles;
                    a:=S[1];
                    "wht is this";
                    S;
                    "first term";
                    print(a);
                    zeros:=0;
                    for j in J do
                        den:=Evaluate(a[2],[f[j]: f in M_F0]);
                        if IsWeaklyZero(den) then 
                            continue j; 
                        end if;
                        num:=Evaluate(a[1],[f[j]: f in M_F0]);
                        //h[r][j]*den - h[1][j]*num;
                        v:=Valuation(num/den  - toc[j])-1; 
                        if v ge 1 then 
                            orbit_size:= #M`cusp_orbits[M`cusp_to_orbit[j]];
                            zeros:=zeros+ v * orbit_size;
                        end if;                    
                    end for;
                    "zeros";
                    zeros;
                    if zeros le upper_bound_on_number_of_poles then
                        // Not enough info to provable find morphism.
                        // We increase precision and try again
                        "bidaha";
                        return FindRatio(M,M0,tryingdegs :homogeneous:=homogeneous, prec0:=prec+prec_delta, prec_delta:=prec_delta, Id:=Id, mon1:=mon1,mon:=mon,AA:=AA);
                    end if;

                    done:=true;
                end if;
            end if;
        end while;

        a:=S[1];
        morphism:=morphism cat [a];
        print(morphism);

    
    if not homogeneous then
        return [a[1]/a[2]: a in morphism];
    end if;

    morphism:= [&*([1] cat [morphism[j][2]: j in [1..#morphism]]) : i in [1..#morphism]]
    cat [ morphism[i][1]* &*([1] cat [morphism[j][2]: j in [1..#morphism] | j ne i]) : i in [1..#morphism]];

    Pol_K<[x]>:=PolynomialRing(K,n); 
    morphism:=[Pol_K!f: f in morphism];

    return morphism;
end intrinsic;






intrinsic ModularFormToSequence(M:: Rec, f::SeqEnum, mult::SeqEnum, N::RngIntElt : OverQ:=false) -> SeqEnum
    {
        Consider a modular form f for the modular curve M whose coefficients lie in Q(zeta_N), and let
        mult be a sequence of nonnegative integers with the same numbering as the cusps of M.

        Returns a finite sequence in Q(zeta_N) that consists of the first mult[i]+1 terms of the q-expansion of f
        at the i-th cusp of M for all i (with a chosen ordering).

        If "OverQ" is true, uses a basis of Q(zeta_N) over Q to obtain a matrix with rational entries instead.
    }
    ee:=[M`sl2level div w: w in M`widths];
    A:=Sort(&cat[ [[j*ee[i],i]: j in [0..mult[i]]] :  i in [1..M`vinf]]);
    KN<z>:=CyclotomicField(N);
    R<qw>:=PowerSeriesRing(KN);
    f:=[R!a: a in f];
    if not OverQ then
            return [ Coefficient(f[a[2]],a[1] div ee[a[2]]) : a in A];
    else 
            return &cat[ Eltseq(Coefficient(f[a[2]],a[1] div ee[a[2]])) : a in A];
    end if;
end intrinsic;
