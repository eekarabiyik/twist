
FamilyRec := recformat<
    calG_level, B_level, calG_index, B_index, genus, sl2level, level, k, prec, commutator_index :RngIntElt,                     
    calG_gens, B_gens, subgroupsofH :SeqEnum,   
    works: BoolElt,                                                              
    calG,B,H, commutator_sub :GrpMat,   
    onelementpossibly: BoolElt, 
    M              
    >;	 




//Creates a family once we already have calG and B.

function CreateFamilyRecSubgroup(calG, B  : compute_comm:=false, compute_calgmeetsl2:=false)   
 /*
    Input:
	    N       : a postitive integer
	    gens    : a set of generators for a subgroup G of GL(2,Z/NZ)
    Output:  
        A record of type "ModularCurveRec" with the following entries computed: 
            N, gens, G, H, genus, v2, v3, vinf, sl2level, level, index, degree,  cusps, widths, regular, is_entangled, trdet. 
            
    Note: when N=1 only some of these entries are computed; Magma does not like matrices with entries in Z/(1).

    When "use_minimal_level" is true, we replace N with the level of G
 */

    F := rec<FamilyRec | calG:= calG ,B:=B >;	 
    calG_level:=gl2Level(calG);
    B_level:=sl2Level(B);
    //calG_index:=Index(GL(2,Integers(calG_level)),ChangeRing(calG,Integers(calG_level)));
    //B_index:=Index(SL(2,Integers(B_level)),ChangeRing(B,Integers(B_level)));
    genus:=GL2Genus(B);

    if compute_comm eq true then
        comm_level,gens,i_comm:=FindCommutatorSubgroup(calG);
        commutator_sub:=sub<SL(2,Integers(comm_level))|gens>;
        F`commutator_sub:=commutator_sub;
    end if;


    calG_gens:=[Eltseq(g): g in Generators(calG)];
    B_gens:=[Eltseq(g): g in Generators(B)];

    F`calG_level:=calG_level;
    F`B_level:=B_level;
    //F`calG_index:=calG_index;
    //F`B_index:=B_index;
    F`genus:=genus;
    F`calG_gens:=calG_gens;
    F`B_gens:=B_gens;
    
          




    return F;
end function;