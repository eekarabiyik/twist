//This is the input of the code, modular curve we are trying to compute a model of.
G:=sub<GL(2,Integers(14)|[[ 1, 0, 8, 13 ],[ 1, 11, 7, 10 ]])>;
//G is contained in G0. The family that contains G is of the form F(G0,G meet SL2)
G0:=sub<GL(2,Integers(14)|[[ 13, 0, 0, 13 ],[ 13, 0, 6, 1 ],[ 3, 10, 8, 13 ],[ 11, 8, 12, 5 ],[ 9, 4, 6, 13 ],[ 0, 1, 13, 13 ]])>;


//This is the representative in the Family F(G0,G meet SL2)
H:=sub<GL(2,Integers(56)|[[ 7, 16, 10, 23 ],[ 15, 0, 0, 15 ],[ 1, 42, 28, 43 ],[ 31, 20, 36, 39 ],[ 29, 0, 0, 29 ],[ 43, 14, 14, 15 ],[ 15, 42, 0, 1 ],[ 9, 0, 0, 9 ],[ 1, 14, 0, 1 ],[ 55, 0, 0, 55 ],[ 11, 22, 26, 47 ]])>;