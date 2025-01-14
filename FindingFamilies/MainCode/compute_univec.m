// Code for computing model of universal elliptic curve for subgroups of 
// GL2(Zhat) that does not contain -I 
FAM := LoadFamilies(["FamilyDataFiles/Gon1.dat", "FamilyDataFiles/Gon2.dat"]);

intrinsic ComputeUnivECModels(H::GrpMat) -> SeqEnum[RngMPolElt]
    {
        Computes a model for the universal elliptic curve over X_H, assuming H does not contain -I
    }
    // Step 1: Compute a model for X_G, where G = <H, -I>, 
    // and j: X_G -> X(1)

    G := GL2IncludeNegativeOne(H);
    T := SL2Intersection(G);
    psi,Mat,jmap,hyper,g := FindModel(G, T, FAM);

    // Step 2: Find a weight three modular form f in M_3(H), and 
    // express f^2/E_6 as an element of Q(X_G)

    return jmap;
end intrinsic; 