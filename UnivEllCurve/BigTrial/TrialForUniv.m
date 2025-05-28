ChangeDirectory("/homes/ek693/Main/FindingFamilies");
AttachSpec("../spec");
FAM:=LoadFamilies(["/homes/ek693/Main/UnivEllCurve/unelcurvestuff/FamilyUniv.dat"]);
load "/homes/ek693/Main/UnivEllCurve/univellcurvedatalmfdb/lmfdbdatafine.m";
curves:=make_data();

    exists(k){k:k in Keys(FAM)| FAM[k]`fine and assigned FAM[k]`H and not FAM[k]`genus eq 0};

        G:=FAM[k]`H;

        _,famfine,Gcong:=FamilyFinderFine(G,SL2Intersection(G),FAM);//THIS IS SO IMPORTANT! VERY IMPORTANT!First conjugate the fine group so it lies in our families

        H:=GL2IncludeNegativeOne(Gcong);
        M0:=CreateModularCurveRec(Gcong);//Modular curve of the fine group
        famkey,fam,H:=FamilyFinder(H,SL2Intersection(H),FAM);//Find the family of the coarse group
        

        model:=Curve(ProjectiveSpace(Rationals(),Rank(Parent(fam`M`psi[1]))-1),fam`M`psi);
        j_map:=fam`jmap
        

        f:=famfine`weight3form;
        FindUnivECModel(M0, model, j_map, f: verbose:=false)
       