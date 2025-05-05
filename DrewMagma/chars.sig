177,1
S,IsCyclic,"Returns true if (Z/NZ)* is cyclic, false otherwise",0,1,0,0,0,0,0,0,0,148,,36,-38,-38,-38,-38,-38
S,Parity,The value of the character on -1,0,1,0,0,0,0,0,0,0,547,,148,-38,-38,-38,-38,-38
S,IsReal,Whether the character takes only real values (trivial or quadratic) or not,0,1,0,0,0,0,0,0,0,547,,36,-38,-38,-38,-38,-38
S,Degree,The degree of the number field Q(chi),0,1,0,0,0,0,0,0,0,547,,148,-38,-38,-38,-38,-38
S,UnitGenerators,Lift to Z of standard generators for (Z/NZ)* where N is the modulus of chi,0,1,0,0,0,0,0,0,0,547,,82,-38,-38,-38,-38,-38
S,UnitGenerators,Lift to Z of standard generators for (Z/NZ)*,0,1,0,0,0,0,0,0,0,148,,82,-38,-38,-38,-38,-38
S,UnitGeneratorOrders,Lift of orders of standard generators for (Z/NZ)*,0,1,0,0,0,0,0,0,0,148,,82,-38,-38,-38,-38,-38
S,UnitGeneratorOrders,List of orders of standard generators for (Z/NZ)* where N is the modulus of chi,0,1,0,0,0,0,0,0,0,547,,82,-38,-38,-38,-38,-38
S,Factorization,Returns a list of Dirichlet characters of prime power modulus whose product is equal to chi (the empty list if chi has modulus 1),0,1,0,0,0,0,0,0,0,547,,168,-38,-38,-38,-38,-38
S,Product,Returns the product of the given list of Dirichlet characters (the trivial character for an empty list),0,1,0,0,0,0,0,0,0,168,,547,-38,-38,-38,-38,-38
S,IsMinimal,Returns true if the specified Dirichlet character is minimal in the sense of Booker-Lee-Strombergsson (Twist-minimal trace formulas and Selberg eignvalue conjedcture),0,1,0,0,0,0,0,0,0,547,,36,-38,-38,-38,-38,-38
S,IsMinimalSlow,Slow version of IsMinimal,0,1,0,0,0,0,0,0,0,547,,36,-38,-38,-38,-38,-38
S,UnitGeneratorsLogMap,Given a list of generators for (Z/NZ)* returns a function that maps integers coprime to N to a list of exponents writing the input as a power product over the given generators,1,1,1,82,0,148,2,0,0,0,0,0,0,0,82,,0,0,148,,41,-38,-38,-38,-38,-38
S,NumberOfCharacterOrbits,"The number of Galois orbits of Dirichlet characters of modulus N (of order <= OrderBound, if specified)",0,1,0,0,0,0,0,0,0,148,,148,-38,-38,-38,-38,-38
S,CharacterOrbitLabels,"List of labels of Galois orbits of Dirichlet characters of modulus N (of order <= OrderBound, if specified)",0,1,0,0,0,0,0,0,0,148,,82,-38,-38,-38,-38,-38
S,IsCharacterLabel,Determines if s is a valid conrey label q.n with n an integer in [1..q] coprime to q,0,1,0,0,0,0,0,0,0,298,,36,148,148,-38,-38,-38
S,IsConreyLabel,Determines if s is a valid conrey label q.n with n an integer in [1..q] coprime to q,0,1,0,0,0,0,0,0,0,298,,36,148,148,-38,-38,-38
S,IsCharacterOrbitLabel,Determines if s is a valid conrey label q.n with n an integer in [1..q] coprime to q,0,1,0,0,0,0,0,0,0,298,,36,148,148,-38,-38,-38
S,CharacterOrbitLabel,Label N.o of the character orbit of modulus N and orbit index o (converts o to base26 encoding),0,2,0,0,0,0,0,0,0,148,,0,0,148,,298,-38,-38,-38,-38,-38
S,CharacterOrbitLabel,Returns the character orbit label N.a for the specified Conrey character or character orbit,0,1,0,0,0,0,0,0,0,298,,298,-38,-38,-38,-38,-38
S,ConreyCharacterOrbitLabel,The label q.o of the Galois orbit of the specified Conrey character q.n,0,2,0,0,0,0,0,0,0,148,,0,0,148,,298,-38,-38,-38,-38,-38
S,ConreyCharacterOrbitLabel,The label q.o of the Galois orbit of the specified Conrey character q.n,0,1,0,0,0,0,0,0,0,298,,298,-38,-38,-38,-38,-38
S,CharacterOrbitIndex,Returns the character orbit index for the specified Conrey character or character orbit,0,1,0,0,0,0,0,0,0,298,,148,-38,-38,-38,-38,-38
S,SplitCharacterLabel,"Integers [q,n] for Conrey character label q.n",0,1,0,0,0,0,0,0,0,298,,82,-38,-38,-38,-38,-38
S,SplitCharacterOrbitLabel,Modulus N and orbit index o of character orbit label N.o (where o is base26 encoded),0,1,0,0,0,0,0,0,0,298,,82,-38,-38,-38,-38,-38
S,CompareCharacterOrbitLabels,"Compares character orbit labels (returns an integer less than, equal to, or greater than 0 indicating the result)",0,2,0,0,0,0,0,0,0,298,,0,0,298,,148,-38,-38,-38,-38,-38
S,CharacterOrbitOrder,The order of the characters in the nth orbit of modulus N,0,2,0,0,0,0,0,0,0,148,,0,0,148,,148,-38,-38,-38,-38,-38
S,CharacterOrbitOrder,The order of the characters in the specified character orbit,0,1,0,0,0,0,0,0,0,298,,148,-38,-38,-38,-38,-38
S,CharacterOrbitDegree,The order of the characters in the specified character orbit,0,1,0,0,0,0,0,0,0,298,,148,-38,-38,-38,-38,-38
S,NumberOfTrivialCharacterOrbits,The number of trivial Galois orbits of Dirichlet characters of modulus N (number of characters of degree 1),0,1,0,0,0,0,0,0,0,148,,148,-38,-38,-38,-38,-38
S,IsConjugate,Returns true if chi1 and chi2 are Galois conjugate Dirichlet characters,0,2,0,0,0,0,0,0,0,547,,0,0,547,,36,-38,-38,-38,-38,-38
S,CompareCharacters,Compare Dirichlet characters based on order and lexicographic ordering of traces,0,2,0,0,0,0,0,0,0,547,,0,0,547,,148,-38,-38,-38,-38,-38
S,CompareConreyCharacters,Compare two Conrey characters of modulus q based on order and lexicographic ordering of traces,0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,148,,148,-38,-38,-38,-38,-38
S,CompareConreyCharacters,Compare two Conrey characters of modulus q based on lex ordering of traces starting from amin (assumes characters have same order and agree on traces for a < amin),0,4,0,0,0,0,0,0,0,148,,0,0,148,,0,0,148,,0,0,148,,148,-38,-38,-38,-38,-38
S,CharacterOrbitReps,The list of Galois orbit representatives of the full Dirichlet group of modulus N with minimal codomains sorted by order and trace vectors. If the optional boolean argument RepTable is set then a table mapping Dirichlet characters to indexes in this list is returned as the second return value,0,1,0,0,0,0,0,0,0,148,,168,457,-38,-38,-38,-38
S,MinimalConreyConjugate,The minimal Conrey index among all conjugates of q.n,0,2,0,0,0,0,0,0,0,148,,0,0,148,,148,-38,-38,-38,-38,-38
S,MinimalConreyConjugate,The minimal Conrey index among all conjugates of q.n,0,1,0,0,0,0,0,0,0,298,,148,-38,-38,-38,-38,-38
S,MaximalConreyConjugate,The maximal Conrey index among all conjugates of q.n,0,2,0,0,0,0,0,0,0,148,,0,0,148,,148,-38,-38,-38,-38,-38
S,MaximalConreyConjugate,The maximal Conrey index among all conjugates of q.n,0,1,0,0,0,0,0,0,0,298,,148,-38,-38,-38,-38,-38
S,IsConreyConjugate,Whether the specified Conrey characters are conjugate or not,0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,148,,36,-38,-38,-38,-38,-38
S,IsConreyConjugate,Whether the specified Conrey characters are conjugate or not,0,2,0,0,0,0,0,0,0,298,,0,0,298,,36,-38,-38,-38,-38,-38
S,IsConjugate,Whether the specified Conrey characters are conjugate or not,0,2,0,0,0,0,0,0,0,298,,0,0,298,,36,-38,-38,-38,-38,-38
S,ConreyCharacterOrbitRepIndexes,The list of minimal index Conrey labels of Galois orbit representatives of the full Dirichlet group sorted by order and trace vectors,0,1,0,0,0,0,0,0,0,148,,82,-38,-38,-38,-38,-38
S,ConreyCharacterOrbitReps,The list of minimal index Conrey labels of Galois orbit representatives of the full Dirichlet group sorted by order and trace vectors,0,1,0,0,0,0,0,0,0,148,,82,-38,-38,-38,-38,-38
S,ConreyCharacterOrbitRep,The minimal index Conrey label that occurs in the specifed Galois orbit,0,1,0,0,0,0,0,0,0,298,,298,-38,-38,-38,-38,-38
S,ConreyCharacterOrbitRep,The minimal index Conrey label that occurs in the specifed Galois orbit,0,2,0,0,0,0,0,0,0,148,,0,0,148,,148,-38,-38,-38,-38,-38
S,ConreyCharacterOrbitIndex,The index of representative of the Galois orbit of the Conrey character q.n in the list returned by CharacterOrbitReps(q),0,2,0,0,0,0,0,0,0,148,,0,0,148,,148,-38,-38,-38,-38,-38
S,ConreyCharacterOrbitIndex,The index of representative of the Galois orbit of the Conrey character with label s in the list returned by CharacterOrbitReps(q),0,1,0,0,0,0,0,0,0,298,,148,-38,-38,-38,-38,-38
S,CharacterOrbitLabel,Label N.o of the orbit of the specified Dirichlet character,0,1,0,0,0,0,0,0,0,547,,148,-38,-38,-38,-38,-38
S,CharacterOrbitRep,Representative element for the Dirichlet character orbit indentified by the label,0,1,0,0,0,0,0,0,0,298,,547,-38,-38,-38,-38,-38
S,CharacterOrbitIndex,The index of the orbit of the specified Dirichlet character in the list of orbit representatives returned by CharacterOrbitReps (this can also be determined using the RepTable parameter),0,1,0,0,0,0,0,0,0,547,,148,-38,-38,-38,-38,-38
S,KroneckerDiscriminant,"Returns the discriminant of the Kronecker symbold corresponding to the specified character, or zero if none exists (1 for trivial character)",0,1,0,0,0,0,0,0,0,547,,148,-38,-38,-38,-38,-38
S,KroneckerCharacterOrbits,"A list of paris <D,i> where D is a fundamental discriminant dividing the modulus M and i is the orbit index of the corresponding Kronecker character",0,1,0,0,0,0,0,0,0,148,,148,-38,-38,-38,-38,-38
S,KroneckerCharacterOrbit,The index of the orbit of the Kronecker character for the fundamental discriminant D in modulus M,0,2,0,0,0,0,0,0,0,148,,0,0,148,,148,-38,-38,-38,-38,-38
S,ConreyGenerator,"For an odd prime p, the least positive integer a that generates (Z/p^eZ)^times for all e",0,1,0,0,0,0,0,0,0,148,,148,-38,-38,-38,-38,-38
S,ConreyLogModEvenPrimePower,"Given an exponent e > 2 and an odd integer n returns unique integers a,s such that n = s*5^a mod 2^e with s in [-1,1] and a in [0..e-1]",0,2,0,0,0,0,0,0,0,148,,0,0,148,,148,148,-38,-38,-38,-38
S,ConreyLogModOddPrimePower,"Given n coprime to the odd prime p returns the integer x in [0..phi(p^e)-1] for which n = r^x mod p^e, where r is the Conrey generator for p",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,148,,148,148,-38,-38,-38,-38
S,ConreyCharacterValue,"The value chi_q(n,m) of the Dirichlet character with Conrey label q.n at the integer m",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,148,,52,-38,-38,-38,-38,-38
S,ConreyCharacterValue,"The value chi_q(n,m) of the Dirichlet character with Conry label q.n at the integer m",0,2,0,0,0,0,0,0,0,148,,0,0,298,,52,-38,-38,-38,-38,-38
S,ConreyCharacterValues,The list of values of the Dirichlet character with Conrey label q.n on the integers in S,1,2,1,82,0,148,3,0,0,0,0,0,0,0,82,,0,0,148,,0,0,148,,82,-38,-38,-38,-38,-38
S,ConreyCharacterValues,The list of values of the Dirichlet character with Conrey label q.n on standard generators for (Z/qZ)* (as returned by UnitGenerators(q)),0,2,0,0,0,0,0,0,0,148,,0,0,148,,82,-38,-38,-38,-38,-38
S,CharacterValues,The list of values of the Dirichlet character with Conrey label q.n on standard generators for (Z/qZ)* (as returned by UnitGenerators(q)),0,2,0,0,0,0,0,0,0,148,,0,0,148,,82,-38,-38,-38,-38,-38
S,CharacterValues,The list of values of the specifed Dirichlet character of modulus N on standard generators for (Z/NZ)* (as returned by UnitGenerators(N)),0,1,0,0,0,0,0,0,0,547,,82,-38,-38,-38,-38,-38
S,ConreyCharacterTrace,"The trace of chi_q(n,m) as an element of the field of values of chi_q(n,.)",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,148,,148,-38,-38,-38,-38,-38
S,ConreyCharacterTrace,"The trace of chi_q(n,m) as an element of the field of values of chi_q(n,.)",0,2,0,0,0,0,0,0,0,148,,0,0,298,,148,-38,-38,-38,-38,-38
S,ConreyCharacterTraces,"The traces of chi_q(n,m) as elements of the field of values of chi_q(n,.) for m in S",1,2,1,82,0,148,3,0,0,0,0,0,0,0,82,,0,0,148,,0,0,148,,82,-38,-38,-38,-38,-38
S,ConreyCharacterTraces,"The traces of chi_q(n,m) as elements of the field of values of chi_q(n,.) for m in S",1,1,1,82,0,148,2,0,0,0,0,0,0,0,82,,0,0,298,,82,-38,-38,-38,-38,-38
S,NormalizedAngle,Given a rational number r return unique positive rational number s <= 1 such that r-s is an integer,0,1,0,0,0,0,0,0,0,267,,267,-38,-38,-38,-38,-38
S,ConjugateAngles,Given a list of angles v returns the (normalized) orbit of v under the action of (Z/phi(N)Z)* where N is the LCM of the denominators of v,1,0,1,82,0,267,1,0,0,0,0,0,0,0,82,,82,-38,-38,-38,-38,-38
S,CharacterAngles,The list of angles (r in Q corresponding to e(r) in C) of the specifed Dirichlet character of modulus N on standard generators for (Z/NZ)* (as returned by UnitGenerators(N)),1,1,1,82,0,148,2,0,0,0,0,0,0,0,82,,0,0,547,,82,-38,-38,-38,-38,-38
S,CharacterAngles,The list of angles (r in Q corresponding to e(r) in C) of the specifed Dirichlet character of modulus N on standard generators for (Z/NZ)* (as returned by UnitGenerators(N)),0,1,0,0,0,0,0,0,0,547,,82,-38,-38,-38,-38,-38
S,ConreyCharacterAngle,"The rational number r such that chi_q(n,m) = e(r) or 0 if m is not coprime to q",0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,148,,267,-38,-38,-38,-38,-38
S,ConreyCharacterComplexValue,"Value of chi_q(m,n) in specified complex field",0,4,0,0,0,0,0,0,0,173,,0,0,148,,0,0,148,,0,0,148,,172,-38,-38,-38,-38,-38
S,ConreyCharacterRealValue,"Real part of chi_q(m,n) in specified real field",0,4,0,0,0,0,0,0,0,403,,0,0,148,,0,0,148,,0,0,148,,402,-38,-38,-38,-38,-38
S,ConreyCharacterAngles,The list of angles (r in Q corresponding to e(r) in C) of the Dirichlet character with Conrey label q.n on the integers m in S (or 0 for m in S not coprime to Q),1,2,1,82,0,148,3,0,0,0,0,0,0,0,82,,0,0,148,,0,0,148,,82,-38,-38,-38,-38,-38
S,ConreyCharacterAngles,The list of angles (r in Q corresponding to e(r) in C) of the Dirichlet character with Conrey label q.n on standard generators for (Z/qZ)* (as returned by UnitGenerators(q)),0,2,0,0,0,0,0,0,0,148,,0,0,148,,82,-38,-38,-38,-38,-38
S,ConreyCharacterAngles,The list of angles (r in Q corresponding to e(r) in C) of the Dirichlet character with Conrey label q.n on standard generators for (Z/qZ)* (as returned by UnitGenerators(q)),0,1,0,0,0,0,0,0,0,-1,,82,-38,-38,-38,-38,-38
S,CharacterAngles,The list of angles (r in Q corresponding to e(r) in C) of the Dirichlet character with Conrey label q.n on standard generators for (Z/qZ)* (as returned by UnitGenerators(q)),0,2,0,0,0,0,0,0,0,148,,0,0,148,,82,-38,-38,-38,-38,-38
S,CharacterAngles,The list of angles (r in Q corresponding to e(r) in C) of the Dirichlet character with Conrey label q.n on standard generators for (Z/qZ)* (as returned by UnitGenerators(q)),0,1,0,0,0,0,0,0,0,-1,,82,-38,-38,-38,-38,-38
S,ConreyCharacterComplexValues,"List of values of chi_q(n,m) for m in S in specified complex field",1,2,1,82,0,148,4,0,0,0,0,0,0,0,173,,0,0,82,,0,0,148,,0,0,148,,82,-38,-38,-38,-38,-38
S,ComplexConreyCharacter,The Dirichlet character with Conrey label q.n with values in the specified complex field,0,3,0,0,0,0,0,0,0,173,,0,0,148,,0,0,148,,175,-38,-38,-38,-38,-38
S,ComplexConreyCharacter,The Dirichlet character with Conrey label q.n. with values in the specific complex field,0,2,0,0,0,0,0,0,0,173,,0,0,298,,175,-38,-38,-38,-38,-38
S,ConreyIndex,The integer n such that q.n is the Conrey label of the specified Dirichlet character of modulus q,0,1,0,0,0,0,0,0,0,547,,148,-38,-38,-38,-38,-38
S,ConreyLabel,Conrey label q.n of the specified Dirichlet character (as a string),0,1,0,0,0,0,0,0,0,547,,298,-38,-38,-38,-38,-38
S,ConreyCharacterFromLabel,"The coprime integers n <= q corresponding to the Conrey label q.n, or the minimal representative of the character orbit with label q.a",0,1,0,0,0,0,0,0,0,298,,148,148,-38,-38,-38,-38
S,CharacterOrder,The order of the Conrey character q.n,0,2,0,0,0,0,0,0,0,148,,0,0,148,,148,-38,-38,-38,-38,-38
S,CharacterOrder,The order of the Conrey character q.n or character orbit q.a,0,1,0,0,0,0,0,0,0,298,,148,-38,-38,-38,-38,-38
S,Degree,The degree of the number field generated by the values of the specified Conrey character,0,2,0,0,0,0,0,0,0,148,,0,0,148,,148,-38,-38,-38,-38,-38
S,Degree,The degree of the number field generated by the values of the specified Conrey character,0,1,0,0,0,0,0,0,0,298,,148,-38,-38,-38,-38,-38
S,IsReal,Whether the specifed Conrey character takes only real values (trivial or quadratic) or not,0,2,0,0,0,0,0,0,0,148,,0,0,148,,36,-38,-38,-38,-38,-38
S,IsReal,Whether the specifed Conrey character takes only real values (trivial or quadratic) or not,0,1,0,0,0,0,0,0,0,298,,36,-38,-38,-38,-38,-38
S,IsMinimal,Returns true if the specified Conrey character q.n is minimal in the sense of Booker-Lee-Strombergsson (Twist-minimal trace formulas and Selberg eignvalue conjedcture),0,2,0,0,0,0,0,0,0,148,,0,0,148,,36,-38,-38,-38,-38,-38
S,IsMinimal,Returns true if the specified Conrey character q.n is minimal in the sense of Booker-Lee-Strombergsson (Twist-minimal trace formulas and Selberg eignvalue conjedcture),0,1,0,0,0,0,0,0,0,298,,36,-38,-38,-38,-38,-38
S,Factorization,"Returns the factorization of the Conrey character q.n into Conrey characters q_i.n_i of prime power moduli q_i as a list of pairs of integers [q_i,n_i]",0,2,0,0,0,0,0,0,0,148,,0,0,148,,82,-38,-38,-38,-38,-38
S,Factorization,Returns the factorization of the Conrey character q.n into Conrey characters q_i.n_i of prime power moduli q_i as a list of Conrey labels q_i.n_i,0,1,0,0,0,0,0,0,0,298,,82,-38,-38,-38,-38,-38
S,Parity,"The parity of the Conrey character q.n, given by its value +/-1 on -1",0,2,0,0,0,0,0,0,0,148,,0,0,148,,148,-38,-38,-38,-38,-38
S,IsEven,True if the Conrey character q.n has even parity (takes value 1 on -1),0,2,0,0,0,0,0,0,0,148,,0,0,148,,148,-38,-38,-38,-38,-38
S,IsOdd,True if the Conrey character q.n has odd parity (takes value -1 on -1),0,2,0,0,0,0,0,0,0,148,,0,0,148,,148,-38,-38,-38,-38,-38
S,Parity,"The parity of the Conrey character q.n, given by its value +/-1 on -1",0,1,0,0,0,0,0,0,0,298,,148,-38,-38,-38,-38,-38
S,Conductor,The conductor of the Conrey character q.n,0,2,0,0,0,0,0,0,0,148,,0,0,148,,148,-38,-38,-38,-38,-38
S,Conductor,The conductor of the Conrey character q.n,0,1,0,0,0,0,0,0,0,298,,148,-38,-38,-38,-38,-38
S,Modulus,The modulus q of the Conrey character q.n,0,1,0,0,0,0,0,0,0,298,,148,-38,-38,-38,-38,-38
S,IsPrimitiveCharacter,Whether the specifed Conrey character q.n is primitive (conductor = modulus = q) or not,0,2,0,0,0,0,0,0,0,148,,0,0,148,,36,-38,-38,-38,-38,-38
S,IsPrimitiveCharacter,Whether the specifed Conrey character q.n is primitive (conductor = modulus = q) or not,0,1,0,0,0,0,0,0,0,298,,36,-38,-38,-38,-38,-38
S,CharacterOrder,"Given a map xi:ZZ -> K that is a Dirichlet character of modulus N, returns its order (results are undefined if xi is not of modulus N)",0,2,0,0,0,0,0,0,0,148,,0,0,175,,148,-38,-38,-38,-38,-38
S,Conductor,"Given a map ZZ -> K that is a Dirichlet character of modulus N, returns its conductor (results are undefined if xi is not of modulus N)",0,2,0,0,0,0,0,0,0,148,,0,0,175,,148,-38,-38,-38,-38,-38
S,Degree,"Given a map ZZ -> K that is a Dirichlet character of modulus N, returns the degree of the (cyclotomic) subfield of K generated by its image",0,2,0,0,0,0,0,0,0,148,,0,0,175,,148,-38,-38,-38,-38,-38
S,Parity,"Given a map ZZ -> K that is a Dirichlet character, returns its parity xi(-1)",0,1,0,0,0,0,0,0,0,175,,148,-38,-38,-38,-38,-38
S,IsReal,"Given a map ZZ -> K that is a Dirichlet character, returns a boolean indicating whether the character takes only real values (trivial or quadratic) or not",0,2,0,0,0,0,0,0,0,148,,0,0,175,,37,-38,-38,-38,-38,-38
S,AssociatedCharacter,The Dirichlet character of modulus m induced by the primitive character inducing chi (whose conductor must divide m),0,2,0,0,0,0,0,0,0,547,,0,0,148,,547,-38,-38,-38,-38,-38
S,AssociatedCharacter,The Conrey index nn of the Conrey character qq.nn of modulus qq induced by the primitive character inducing the Conrey character q.n,0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,148,,148,-38,-38,-38,-38,-38
S,AssociatedCharacter,Conrey character qq.nn of modulus qq induced by the primitive character inducing the Conrey character q.n,0,2,0,0,0,0,0,0,0,298,,0,0,148,,298,-38,-38,-38,-38,-38
S,AssociatedPrimitiveCharacter,The primitive Conrey character qq.nn inducing the Conrey character q.n (returns qq and nn),0,2,0,0,0,0,0,0,0,148,,0,0,148,,148,148,-38,-38,-38,-38
S,AssociatedPrimitiveCharacter,Conrey character qq.nn of modulus qq induced by the primitive character inducing the Conrey character q.n,0,1,0,0,0,0,0,0,0,298,,298,-38,-38,-38,-38,-38
S,ConreyCharacterProduct,"Computes the product q.n of the Conrey characters q1.n1 and q2.n2, returning q=LCM(q1,q2) and n",0,4,0,0,0,0,0,0,0,148,,0,0,148,,0,0,148,,0,0,148,,148,148,-38,-38,-38,-38
S,ConreyCharacterProduct,"Computes the product q.n of the Conrey characters q1.n1 and q2.n2, returning the Conrey label q.n",0,2,0,0,0,0,0,0,0,298,,0,0,298,,298,-38,-38,-38,-38,-38
S,ConreyInverse,The Conrey index of the inverse of the Conrey character q.n,0,2,0,0,0,0,0,0,0,148,,0,0,148,,148,-38,-38,-38,-38,-38
S,ConreyInverse,The Conrey index of the inverse of the Conrey character q.n,0,1,0,0,0,0,0,0,0,298,,298,-38,-38,-38,-38,-38
S,ConductorProductBound,Quickly computes an integer guaranteed to divide the conductor of any product of Dirichlet characters of conductors M and N,0,2,0,0,0,0,0,0,0,148,,0,0,148,,148,-38,-38,-38,-38,-38
S,ConductorProduct,The conductor of the product of the Conrey characters q1.n1 and q2.n2,0,4,0,0,0,0,0,0,0,148,,0,0,148,,0,0,148,,0,0,148,,148,-38,-38,-38,-38,-38
S,ConductorProduct,The conductor of the product of the Conrey characters q1.n1 and q2.n2,0,2,0,0,0,0,0,0,0,298,,0,0,298,,148,-38,-38,-38,-38,-38
S,PrimitiveConductorProduct,The conductor of the product of the primitive Conrey characters q1.n1 and q2.n2 (primitivity is not verified),0,4,0,0,0,0,0,0,0,148,,0,0,148,,0,0,148,,0,0,148,,148,-38,-38,-38,-38,-38
S,PrimitiveConductorProduct,The conductor of the product of the primitive Conrey characters q1.n1 and q2.n2 (primitivity not verified),0,2,0,0,0,0,0,0,0,298,,0,0,298,,148,-38,-38,-38,-38,-38
S,Twist,"Given Conrey characters chi:=q1.n1 and psi:=q2.n2 returns the character tchi:=q.n of modulus q:=LCM(Mudulus(chi),Conductor(psi)*Conductor(chi*psi)) associated to chi*psi^2; if chi is minimal the twist of a twist-minimal newform f of character chi by psi will lie in S_k(q,tchi)^new",0,4,0,0,0,0,0,0,0,148,,0,0,148,,0,0,148,,0,0,148,,148,148,-38,-38,-38,-38
S,Twist,"Given Conrey characters chi:=q1.n1 and psi:=q2.n2 returns the character tchi:=q.n of modulus q:=LCM(Mudulus(chi),Conductor(psi)*Conductor(chi*psi)) associated to chi*psi^2; if chi is minimal the twist of a twist-minimal newform f of character chi by psi will lie in S_k(q,tchi)^new",0,2,0,0,0,0,0,0,0,298,,0,0,298,,298,-38,-38,-38,-38,-38
S,Twist,"Given Dirichlet characters chi and psi returns the character tchi of modulus N:=LCM(Mudulus(chi),Conductor(psi)*Conductor(chi*psi)) associated to chi*psi^2; if chi is minimal the twist of a twist-minimal newform f of character chi by psi will lie in S_k(N,tchi)^new",0,2,0,0,0,0,0,0,0,547,,0,0,547,,547,-38,-38,-38,-38,-38
S,ConreyConjugates,"Given a Dirichlet character chi embedded as xi with values in a number field K, returns a list of the Conrey labels corresponding to the embeddings of K in C, as ordered by Conjugates",0,2,0,0,0,0,0,0,0,175,,0,0,547,,82,-38,-38,-38,-38,-38
S,TranslatedCharacterAngles,"Given arbitrary generators u for (Z/NZ)* and a corresponding list of angles v defining a character of modulus N, compute a list of angles giving values of character on the integers in S. Does not verify the validity of v!",2,1,1,82,0,148,3,1,82,0,148,4,0,0,0,0,0,0,0,82,,0,0,82,,0,0,82,,0,0,148,,82,-38,-38,-38,-38,-38
S,DirichletCharacterFromAngles,"Given a modulus N, a list of generators for (Z/NZ)*, and a list of angles v returns the Dirichlet character with values in Q(zeta_n) mapping u[i] to zeta_n^(n*v[i]), where n is the LCM of the denominators in v",2,1,1,82,0,148,2,1,82,0,267,3,0,0,0,0,0,0,0,82,,0,0,82,,0,0,148,,547,-38,-38,-38,-38,-38
S,DirichletCharacterFromAngles,"Given a modulus N, a positive integer n, a list of integers u giving standard generates for (Z/NZ)*, and a suitable list of integers v, returns the Dirichlet character with values in Q(zeta_n) mapping u[i] to zeta_n^v[i]",0,2,0,0,0,0,0,0,0,82,,0,0,148,,547,-38,-38,-38,-38,-38
S,SquareRoots,A list of the Dirichlet characters psi in the ambient group of chi for which psi^2 = chi (note that only psi in the ambient group of chi will be returned),0,1,0,0,0,0,0,0,0,547,,82,-38,-38,-38,-38,-38
S,CyclotomicConreyCharacter,The Dirichlet character with Conrey label q.n,0,2,0,0,0,0,0,0,0,148,,0,0,148,,547,-38,-38,-38,-38,-38
S,CyclotomicConreyCharacter,The Dirichlet character with the specified Conrey label or character orbit label,0,1,0,0,0,0,0,0,0,298,,547,-38,-38,-38,-38,-38
S,DirichletCharacter,The Dirichlet character,0,1,0,0,0,0,0,0,0,-1,,547,-38,-38,-38,-38,-38
S,DirichletCharacter,"The Dirichlet character with Conrey label q.n, equivalent to CyclotomicConreyCharacter(q,n)",0,2,0,0,0,0,0,0,0,148,,0,0,148,,547,-38,-38,-38,-38,-38
S,DirichletCharacter,Returns the Dirichlet character with the specified Conrey label or character orbit label,0,1,0,0,0,0,0,0,0,298,,547,-38,-38,-38,-38,-38
S,Conjugates,List of Galois conjugates of chi,0,1,0,0,0,0,0,0,0,547,,82,-38,-38,-38,-38,-38
S,ConreyConjugates,Sorted list of Conrey indexes m of all Conrey characters q.m conjugate to q.n,0,2,0,0,0,0,0,0,0,148,,0,0,148,,82,-38,-38,-38,-38,-38
S,ConreyConjugates,Returns a sorted list of labels of all Conrey characters q.m conjugate to specified Conrey character or in specified character orbit,0,1,0,0,0,0,0,0,0,298,,82,-38,-38,-38,-38,-38
S,ConreyIndexes,Sorted list of Conrey indexes of the Galois conjugates of the specified Dirichlet charatacter,0,1,0,0,0,0,0,0,0,547,,82,-38,-38,-38,-38,-38
S,ConreyIndexes,Sorted list of integers n giving the Conrey labels q.n of the conjugates in the specifeid Galois orbit of modulus N,0,1,0,0,0,0,0,0,0,298,,82,-38,-38,-38,-38,-38
S,ConreyLabels,Sorted list of Conrey indexes of the Galois conjugates of the specified Dirichlet charatacter,0,1,0,0,0,0,0,0,0,547,,82,-38,-38,-38,-38,-38
S,ConreyLabels,Returns a sorted list of labels of all Conrey characters q.m conjugate to specified Conrey character or in specified character orbit,0,1,0,0,0,0,0,0,0,298,,82,-38,-38,-38,-38,-38
S,ConreyOrbitTable,"Given the name of input file containing records N:o:L:... where L is a list of Conrey indexes n of Conrey characters N.n with orbit index o, creates table T[N][n] := o",0,2,0,0,0,0,0,0,0,148,,0,0,298,,82,-38,-38,-38,-38,-38
S,ConreyOrbitLabelTable,"Given the name of input file containing records N:o:L:... where L is a list of Conrey indexes n of Conrey characters N.n with orbit index o, creates table T[N][n] := N.a where N.a is the lable of the character orbit of modulus N and index o",0,2,0,0,0,0,0,0,0,148,,0,0,298,,82,-38,-38,-38,-38,-38
S,CharacterFromValues,"Given a modulus N, a list of generators of (Z/NZ)*, and a corresponding list of roots of unity in a number/cyclotomic field K, returns a map ZZ -> K for the Dirichlet character",1,1,1,82,0,148,3,0,0,0,0,0,0,0,82,,0,0,82,,0,0,148,,175,-38,-38,-38,-38,-38
S,NewModularSymbols,Returns newspace of modular symbols of weight k for the Dirichlet character chi with sign -1,0,2,0,0,0,0,0,0,0,148,,0,0,298,,548,-38,-38,-38,-38,-38
S,NewModularSymbols,Returns newspace of modular symbols of weight k for the newspace with label s,0,1,0,0,0,0,0,0,0,298,,548,-38,-38,-38,-38,-38
