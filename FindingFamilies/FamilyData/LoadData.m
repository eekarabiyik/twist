// Load data from saved files to a format used in calling FindModel.
// You specify a base folder, and optionally impose various constraints on the families that you want

intrinsic PortData(input, output) -> SeqEnum
{}
    maxlen := 0;
    bad := [];
    if input[#input] ne "/" then
        input *:= "/";
    end if;
    if output[#output] ne "/" then
        output *:= "/";
    end if;
    ok := System("mkdir " * output);
    if ok gt 0 then
        error "Output folder already exists";
    end if;
    genera := Split(Pipe("ls " * input, ""), "\n");
    for g in genera do
        assert g[1..5] eq "Genus" and StringToInteger(g[6..#g]) ge 0;
        System("mkdir " * output * g);
        indexes := Split(Pipe("ls " * input * g, ""), "\n");
        print g, #indexes;
        for i in [1..#indexes] do
            ind := indexes[i];
            assert ind[1..5] eq "Index" and ind[#ind-3..#ind] eq ".dat" and StringToInteger(ind[6..#ind-4]) gt 0;
            ind := ind[1..#ind-4];
            print "  ", ind;
            System("mkdir " * output * g * "/" * ind);
            I := Open(input * g * "/" * ind * ".dat", "r");
            FAM := [];
            repeat
                b, y := ReadObjectCheck(I);
                if b then
                    Append(~FAM, y);
                end if;
            until not b;
            delete I;
            // For now we don't mess with the record format
            A := AssociativeArray();
            for j in [1..#FAM] do
                y := FAM[j];
                if not assigned y`agreeable_label then
                    Append(~bad, <g, ind, j>);
                    continue;
                end if;
                if not IsDefined(A, y`agreeable_label) then
                    A[y`agreeable_label] := [];
                end if;
                Append(~(A[y`agreeable_label]), y);
            end for;
            for agreeable_label -> L in A do
                maxlen := Max(maxlen, #L);
                O := Open(output * g * "/" * ind * "/" * agreeable_label, "w");
                for y in L do
                    WriteObject(O, y);
                end for;
            end for;
        end for;
    end for;
    print "Maxlen", maxlen;
    return bad;
end intrinsic;

intrinsic LoadFamilies(base::MonStgElt : genus:="", index:="", label:="", agreeable_genus:="", agreeable_index:="", agreeable_label:="") -> SeqEnum
{Load family data from within the base folder with given invariants}
    if label ne "" then
        pieces := Split(label, "-");
        if #pieces ne 2 then
            error "Invalid format for label: must be agreeable_label-genus.index.tiebreaker";
        end if;
        if agreeable_label eq "" then
            agreeable_label := pieces[1];
        elif pieces[1] ne agreeable_label then
            error Sprintf("label (%o) must start with given agreeable label (%o)", label, agreeable_label);
        end if;
        pieces := Split(pieces[2], ".");
        if #pieces ne 3 then
            error "Invalid format for label: must be agreeable_label-genus.index.tiebreaker";
        end if;
        if genus cmpeq "" then
            genus := StringToInteger(pieces[1]);
        elif Sprint(genus) ne pieces[1] then
            error Sprintf("label (%o) incompatible with provided genus (%o)", label, genus);
        end if;
        if index cmpeq "" then
            index := StringToInteger(pieces[2]);
        elif Sprint(index) ne pieces[2] then
            error Sprintf("label (%o) incompatible with provided index (%o)", label, index);
        end if;
    end if;
    agreeable_genus := Sprint(agreeable_genus);
    agreeable_index := Sprint(agreeable_index);
    if agreeable_label ne "" then
        pieces := Split(agreeable_label, ".");
        if #pieces ne 5 then
            error "agreeable_label must be valid LMFDB coarse label for modular curve";
        end if;
        if agreeable_genus ne "" and agreeable_genus ne pieces[3] then
            error Sprintf("agreeable_label (%o) incompatible with provided agreeable_genus (%o)", agreeable_label, agreeable_genus);
        end if;
        if agreeable_index ne "" and agreeable_index ne pieces[2] then
            error Sprintf("agreeable_label (%o) incompatible with provided agreeable_index (%o)", agreeable_label, agreeable_index);
        end if;
    end if;
    if base[#base] ne "/" then // I guess we're not supporting Windows....
        base *:= "/";
    end if;
    genera := Split(Pipe("ls " * base, ""), "\n");
    if genus cmpne "" then
        // Size 0 or 1
        genera := [g : g in genera | g eq Sprintf("Genus%o", genus)];
    end if;
    FAM := [];
    for g in genera do
        path := base * g * "/";
        indexes := Split(Pipe("ls " * path, ""), "\n");
        if index cmpne "" then
            // Size 0 or 1
            indexes := [ind : ind in indexes | ind eq Sprintf("Index%o", index)];
        end if;
        for ind in indexes do
            path := base * g * "/" * ind * "/";
            agreeables := Split(Pipe("ls " * path, ""), "\n");
            if agreeable_label ne "" then
                // Size 0 or 1
                agreeables := [ag : ag in agreeables | ag eq agreeable_label];
            else
                if agreeable_genus ne "" then
                    agreeables := [ag : ag in agreeables | Split(ag, ".")[3] eq agreeable_genus];
                end if;
                if agreeable_index ne "" then
                    agreeables := [ag : ag in agreeables | Split(ag, ".")[2] eq agreeable_index];
                end if;
            end if;
            for ag in agreeables do
                path := base * g * "/" * ind * "/" * ag;
                I := Open(path, "r");
                repeat
                    b, y := ReadObjectCheck(I);
                    if b and (label eq "" or label eq y`family_label) then
                        Append(~FAM, y);
                    end if;
                until not b;
                delete I;
            end for;
        end for;
    end for;
    return FAM;
end intrinsic;

// This is the older version and is deprecated
intrinsic LoadFamilies(filenames::SeqEnum[MonStgElt]) -> SeqEnum
{Load family data from a sequence of files}
    FAM := [];
    for fname in filenames do
        I := Open(fname, "r");
        repeat
            b, y := ReadObjectCheck(I);
            if b then
                Append(~FAM, y);
            end if;
        until not b;
    end for;
    return FAM;
end intrinsic;
