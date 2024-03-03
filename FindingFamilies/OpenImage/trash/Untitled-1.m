
load "FindOpenImage.m";

E:=EllipticCurve("78838c2");
E:=EllipticCurve("81585be1");
G,ind,H:=FindOpenImage(E);
time FindLevels(G,ind,H);

