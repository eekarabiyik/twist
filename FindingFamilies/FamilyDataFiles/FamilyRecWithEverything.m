AttachSpec("../../DrewMagma/magma.spec");
//This a record for the families we will use. I think most entries are clear.
FamilyRecFinal := recformat<
    calG_level, B_level, calG_index, B_index, genus, sl2level, level, k, prec, commutator_index :RngIntElt,                     
    calG_gens, B_gens, subgroupsofH :SeqEnum,   
    works: BoolElt,                                                              
    calG,B,H, commutator_sub, W :GrpMat,   
    onelementpossibly: BoolElt, 
    CPname: MonStgElt ,  
    M, AOfMF, quogroup, quomap, dataforquotient, conjugacyofB, transversals, nolift
    >;	 




//Creates a family once we already have calG and B.

function CreateFamilyRecFinal(calG, B ,Hc,W,CPname : compute_comm:=false, compute_calgmeetsl2:=false)   
 /*
    Input:
	    calG    : an agreeable subgroup
	    B       : an open subgroup of SL2(Zhat) such that [calG,calG] subseteq B subseteq SL2 meet calG
    Output:  
        A record of type "FamilyRec" with the following entries computed: 
            calG, B, calG_level, B_level, calG_gens, B_gens
            
 */

      F := rec<FamilyRecFinal | calG:= calG ,B:=B >;	 
    calG_level:=GL2Level(calG);
    B_level:=SL2Level(B);
    //calG_index:=Index(GL(2,Integers(calG_level)),ChangeRing(calG,Integers(calG_level)));
    //B_index:=Index(SL(2,Integers(B_level)),ChangeRing(B,Integers(B_level)));
    genus:=GL2Genus(B);


    calG_gens:=[Eltseq(g): g in Generators(calG)];
    B_gens:=[Eltseq(g): g in Generators(B)];
    F`W:=W;
    F`calG_level:=calG_level;
    F`B_level:=B_level;
    F`genus:=genus;
    F`calG_gens:=calG_gens;
    F`B_gens:=B_gens;
    F`AOfMF:=AssociativeArray();
    F`commutator_sub:=Hc;
    F`CPname:=CPname;

    return F;
end function;