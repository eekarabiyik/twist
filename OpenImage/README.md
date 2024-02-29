# OpenImage

This is code for the preprint: [Explicit open images for elliptic curves over Q](https://arxiv.org/abs/2206.14959v1)

The main function is `FindOpenImage` in `main\FindOpenImage.m` which takes as input a non-CM elliptic curve E over Q and returns the image of its adelic Galois image; this is an open subgroup G of GL(2,Zhat) that is uniquely determined up to conjugacy.  The group G is returned as its image in GL(2,Z/NZ), where N is the level of G.   It also returns the index of G in GL(2,Zhat) and a group giving the intersection of G with SL(2,Zhat).

Results returned are guaranteed to be correct.   Errors will always occur if E gives rise to an unknown exceptional rational point on certain high genus modular curves.

Magma version at least 2.27 is required to read the data files.

Please contact me with any suggestions or issues.