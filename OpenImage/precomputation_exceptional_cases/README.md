
After our main computations, we are left with 86 special j-invariants to consider.  Of these, 81 actually are exceptional, i.e., the agreeable closure for elliptic curves E/Q with these j-invariants gives rise to a modular curve with only finitely many rational points.   In this folder, we deal with these remaining cases.   These are one-time computations that will be used by our algorithms.  We assume that the precomputations in the folder `../precomputation` have already been run.

There are two main files to run:
- `FindExceptionalAgreeableClosures.m`  : computes the agreeable closures for our special j-invariants.  The data is recorded to `../data-files/agreeable_closures_exceptional.dat`

- `FindExceptionalImages.m`  : computes the Galois image for a fixed elliptic curve with an exceptional j-invariant.  The data is recorded to `../data-files/exceptional_images.dat`

Warning: the first file took several hours to finish on my machine.   The group theory is involved is particularly slow (I could optimize it a lot, but this is not a big deal since it is a one-time computations).

