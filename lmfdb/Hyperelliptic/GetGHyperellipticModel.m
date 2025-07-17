//Assuming the output of FindModel
//Assume label is there
//Assume qgon2 is there.
if qgon2 eq true then   
    if psi eq [] then X:=Curve(ProjectiveSpace(Rationals(),1),[]); else
        X := Curve(Proj(Universe(psi)), psi); end if;
    isH, H,hmap := IsHyperelliptic(X);
    if isH then
        C:=H;
        LMFDBWriteHyperellipticModel(C, hmap, label);
    else
        "What do you mean it is not hyperelliptic?";
    end if;
else
    if not assigned prec then
        prec := 100;
    else
        prec := StringToInteger(prec);
    end if;
    if g lt 3 then
        label cat ":genus too small";
        //exit;
    end if;
    t0 := ReportStart(label, "conic double cover model");
    done:-=false;
    repeat
        try
            done:=true;
            C := HyperellipticModelFromGroup(Gcong,famG`CanModelForHyp,gonMAT : prec0:=prec);
        catch e 
            done:=false;
            prec:=prec+10;
        end try;
    until done;
    LMFDBWriteHyperellipticModel(DefiningEquations(C), [], label);
    //The above should give the hyperelliptic model
end if;

