//assuming the output of FindModel


j:=relmap;
fname := "jfacs/" * label;
if not rel then
    assert #j eq 2;
    facs, leading, nfacs, jdegs := getfac(j);
    Write(fname, Sprintf("1|%o|%o|%o|%o", facs, leading, nfacs, jdegs) : Overwrite);
    //facs, leading, nfacs, jdegs := getfac([j[1] - 1728*j[2], j[2]]);
    //Write(fname, Sprintf("3|%o|%o|%o|%o", facs, leading, nfacs, jdegs));
else
    // In this case we just want to factor out the leading coefficients, but getfac will do that
    facs, leading, nfacs, jdegs := getfac(j);
    Write(fname, Sprintf("0|%o|%o|%o|%o", facs, leading, nfacs, jdegs) : Overwrite);
end if;