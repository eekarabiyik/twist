//Load  this to run the code on all curves in LMFDB
AttachSpec("../../DrewMagma/magma.spec");
load "main.m";
load "../Trial/lmfdbgenusupto6.m";
curves:=make_data();

//load "/homes/ek693/Main/FindingFamilies/TwistingCode/TwistingCode2.m";



for k in [15000..16000] do
        print(k);
        time0:=Realtime();
        G:=curves[k]`subgroup;
        if #BaseRing(G) eq Infinity() then continue; end if;
        if GL2Order(G) eq 1 then continue; end if;
        if assigned G`SL then delete G`SL; end if;
        
        T:=SL(2,Integers(#BaseRing(G))) meet G;
        T`SL:=true;
        psi,MAT,jmap:=FindModelNew(G,T: redcub:=true);
        print(psi);
        print(Realtime(time0));
end for;
//358 was problem fixed it