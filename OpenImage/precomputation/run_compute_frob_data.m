// Precompute Frobenius data that will make it easier to compute images of Galois for elliptic curves.
// The file "run_all.m" must be run first!

load "ComputeFrobData.m";
PreComputationOfFrobData("../data-files/frob_data.dat",101);