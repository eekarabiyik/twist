//This is just a trial that works. There are a lot of curves here of various genera. Low genus (less than or equal to 2)
//usually work. Higher genus takes too much time. The divisors are the problem.   

AttachSpec("./spec");
AttachSpec("./UnivEllCurve/main/univspec");
load "./UnivEllCurve/main/listofcurves.m";
grouplist:=[];
for i in  [1..#L] do
    list:=L[i];
    G:=sub<GL2Ambient(list[1])|list[2]>;
    assert not -Id(GL2Ambient(list[1])) in G;
    g:=GL2Genus(G);
    g;
    grouplist:= grouplist cat [G];
end for;

univmodels:=AssociativeArray();

for i in [1..#grouplist] do
    "Start";
    G:=grouplist[i];
    "Genus";
    g:=GL2Genus(G);
    g;
    G1:= GL2IncludeNegativeOne(G);
    M:=FindModelOfXG(CreateModularCurveRec(G1));
    a,j:=AbsoluteJmap(M);
    M0:=CreateModularCurveRec(G);
    inputringo := Parent(j[1]);
    rank:=Rank(inputringo);
    PP:=ProjectiveSpace(Rationals(),rank-1);
    C:=Curve(PP,M`psi);
    "Models computed";
    ratio_map:=FindRatio(M,M0);
    "Ratio computed";
    //j;
    //ratio_map;
    UnivModel:=FindUnivECModel(M0,C,j,ratio_map);
    "Final Result";
    UnivModel;
    univmodels[i]:=<UnivModel,#BaseRing(G),[Eltseq(a): a in Generators(G)]>;
    fp := Open("data.txt", "w");

    for t in Keys(univmodels) do
        Puts(fp, Sprint(univmodels[t]));
    end for;

    Flush(fp);
    delete fp;




end for;



