//This is just a trial that works. There are a lot of curves here of various genera. Low genus (less than or equal to 2)
//usually work. Higher genus takes too much time. The divisors are the problem.   

AttachSpec("./spec");
AttachSpec("./UnivEllCurve/main/univspec");
load "./UnivEllCurve/main/univspec/listofcurves.m";
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
    ratt:=FindRatio(M,M0,2);
    "Ratio computed";
    //j;
    //ratt;
    UnivModel:=FindUnivECModel(M0,C,j,[ratt[2],ratt[1]]);
    "Final Result";
    UnivModel;
    univmodels[i]:=<UnivModel,#BaseRing(G),[Eltseq(a): a in Generators(G)]>;
    fp := Open("/home/eekarabiyik/univellcurve/datadahaguzel.txt", "w");

    for t in Keys(univmodels) do
        Puts(fp, Sprint(univmodels[t]));
    end for;

    Flush(fp);
    delete fp;


    // fpp := Open("/home/eekarabiyik/univellcurve/data.dat", "w");
    // for t in univmodels do
    //     WriteObject(fpp, t);
    // end for;
    // delete fpp;

end for;



