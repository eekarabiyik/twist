// Load data from saved files to a format used in calling FindModelNew.

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
