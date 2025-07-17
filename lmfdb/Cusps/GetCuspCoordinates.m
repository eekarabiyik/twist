//assuming the output of FindModel and ComputePlaneModel

cusps:=CuspOrbits(Gcong);

Cs := L;//L is the list of plane models
if psi eq [] then X:=Curve(ProjectiveSpace(Rationals(),1),[]); else
X := Curve(Proj(Universe(psi)), psi); end if;
C := 0; // stupid magma needs this defined even if not used.
if #Cs gt 0 then
    C := Curve(Proj(Parent(Cs[1][1])), Cs[1][1]);//Universe???
end if;
ans := [* *];
cusps := [orb[1] : orb in cusps];
cyclevel:=LCM([famG`M`N,#BaseRing(G)]);
F0:=F0Twister(famG`M`F0, MAT^(-1),cyclevel);
 for i in [1..#cusps] do
	    CuspUpdateCoordinates(~cusps[i], X, F0);
end for;
for cusp in cusps do
    K := cusp`field;
    P1K := ProjectiveSpace(K, 1);
    XK := ChangeRing(X, K);
    pt := XK!Eltseq(cusp`coords);
    Append(~ans, <model_type, pt>);
    if #Cs gt 0 then
        CK := ChangeRing(C, K);
        T := ChangeRing(Universe(Cs[1][2]), K);
        CprojK := map<XK -> CK| [T!f : f in Cs[1][2]]>;
        Append(~ans, <2, pt @ CprojK>);//this is plane model?
    end if;
end for;
LMFDBWriteCuspCoords(ans, label);
ReportEnd(label, "pushing forward cusps", t0);
