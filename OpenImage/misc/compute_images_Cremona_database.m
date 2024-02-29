/* 
    The code in this family goes through all the non-CM elliptic curves E/Q in Cremona's database and
    computes the image of rho_E.

*/
// magma -t 32 "compute_images_Cremona_database.m" &


load "../main/FindOpenImage.m";
D:=CremonaDatabase();   

max:=LargestConductor(D);
t:=Realtime();

for N in [1..max] do

    if N mod 1000 eq 0 then 
        100.0*N/max,"%         ",N; // occasionally update what percentage we are done
        Realtime(t); 
        t:=Realtime(); " ";        
    end if;

    for E in EllipticCurves(D,N) do
        
        j:=jInvariant(E);
        if j in CM_jInvariants then continue E; end if;
        
        GE,index,HE:=FindOpenImage(E);
        gens1:=[ [Integers()!a: a in Eltseq(GE.i)] : i in [1..Ngens(GE)]];
        gens2:=[ [Integers()!a: a in Eltseq(HE.i)] : i in [1..Ngens(HE)]];

        v:=[* CremonaReference(D, E), index, #BaseRing(GE), gens1, #BaseRing(HE), gens2 *];
        
        /*
            For our elliptic curve E/Q, the list v has the following entries
                - v[1] is the Cremona label for E
                - v[2] is the index of the image of rho_E in GL(2,Zhat)
                - v[3] is a positive integer and v[4] is a sequence that consists of sequences of integers of length 4 so that the group
                        GE:=sub< GL(2,Integers(v[3])) | v[4] >
                  lifted in GL(2,Zhat) is the image of rho_E  (up to conjugacy).
                - v[5] is a positive integer and v[6] is a sequence that consists of sequences of integers of length 4 so that the group
                        HE:=sub< SL(2,Integers(v[5])) | v[6]>
                  lifted in SL(2,Zhat) is the intersection of the lift of GE with SL(2,Zhat).
        */

        // *** LATER: at this point save "v" to file ***

    end for;


end for;
