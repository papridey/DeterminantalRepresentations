newPackage("DeterminantalRepresentations",
	AuxiliaryFiles => false,
	Version => "0.0.1",
	Date => "December 5, 2018",
	Authors => {
		{Name => "Justin Chen",
		Email => "jchen646@gatech.edu"},
		{Name => "Papri Dey",
		Email => "papri_dey@brown.edu"}
	},
	Headline => "a package for computing determinantal representations",
	HomePage => "https://github.com/jchen419/DeterminantalRepresentations-M2",
	PackageImports => {"NumericalAlgebraicGeometry"},
	PackageExports => {"NumericalAlgebraicGeometry"},
	DebuggingMode => true
)
export {
    "quadraticDetRep",
    "makeOrthogonalMatrix",
    "generalizedMixedDiscriminant",
    "roundMatrix"
}


quadraticDetRep = method()
quadraticDetRep RingElement := List => f -> (
    R := ring f;
    n := #gens R;
    b := sub(last coefficients(f, Monomials => gens R), RR);
    A := sub(matrix table(n, n, (i,j) -> if i == j then (last coefficients(f, Monomials => {R_i^2}))_(0,0) else (1/2)*(last coefficients(f, Monomials => {R_i*R_j}))_(0,0)), RR);
    Q := (1/4)*b*transpose(b) - A;
    E := eigenvectors(Q, Hermitian => true);
    E = (E#0/clean_1e-10, E#1);
    if not all(E#0, e -> e >= 0) then return false;
    if rank(Q) > 3 then return false;
    posEvalues := positions(E#0, e -> e > 0);
    posEvectors := apply(posEvalues, i -> (E#0#i,matrix E#1_i));
    r := (1/2)*b + sqrt(posEvectors#0#0)*posEvectors#0#1;
    s := (1/2)*b - sqrt(posEvectors#0#0)*posEvectors#0#1;
    t := sqrt(posEvectors#1#0)*posEvectors#1#1;
    u := if #posEvalues == 3 then sqrt(posEvectors#2#0)*posEvectors#2#1 else 0*b;
    apply(n, i -> matrix{{r_(i,0),t_(i,0) - ii*u_(i,0)},{t_(i,0)+ii*u_(i,0),s_(i,0)}})
)

makeOrthogonalMatrix = method()
makeOrthogonalMatrix (ZZ, RingElement) := Matrix => (n, f) -> (
    R := ring f;
    R1 := (coefficientRing R)[R_0];
    R2 := (coefficientRing R)[R_1];
    f1 := sub(sub(f, R_1 => 0), R1);
    f2 := sub(sub(f, R_0 => 0), R2);
    r1 := roots(f1);
    r2 := roots(f2);
    D1 := reverse sort(apply(r1,r -> -1/r) | toList(3-#r1:0));
    D2 := reverse sort(apply(r2,r -> -1/r) | toList(3-#r2:0));
    d := #D1;
    if not all(D1 | D2, r -> clean((10.0)^(-n), imaginaryPart r) == 0) then (
	print("Not a real zero polynomial - no determinantal representation of size " | d);
	return;
    );
    (D1, D2) = (D1/realPart, D2/realPart);
    C1 := last coefficients(f, Monomials => apply(d, i -> R_{1,i}));
    G1 := sub(matrix table(d,d,(i,j) -> sum apply(subsets(toList(0..<d)-set{j},i), s -> product(D2_s))), RR);
    diag1 := solve(G1, sub(C1,RR));
    if not isMajorized((10.0)^(-n), D1,flatten entries diag1) then (
	print(toString(D1) | " is not majorized by " | toString(diag1));
	return;
    );
    C2 := last coefficients(f, Monomials => apply(d, i -> R_{i,1}));
    G2 := sub(matrix table(d,d,(i,j) -> sum apply(subsets(toList(0..<d)-set{j},i), s -> product(D1_s))), RR);
    diag2 := solve(G2,sub(C2,RR));
    if not isMajorized((10.0)^(-n), D2,flatten entries diag2) then (
	print(toString(D2) | " is not majorized by " | toString(diag2));
	return;
    );
    D1 = transpose matrix{D1};
    D2 = transpose matrix{D2};
    y := symbol y;
    T := RR[y_0..y_(d^2-1)];
    A := genericMatrix(T,d,d);
    L := minors(1, (transpose A)*D1-diag1)+minors(1, A*D2-diag2);
    allOnes := transpose matrix{apply(d, i -> 1_T)};
    rowsum := minors(1, A*allOnes - allOnes);
    colsum := minors(1, (transpose A)*allOnes - allOnes);
    J := minors(1, A*transpose A - id_(T^d)) + sub(L + rowsum + colsum, apply(gens T, v -> v => v^2));
    print "Computing orthogonal matrices numerically ...";
    elapsedTime N := numericalIrreducibleDecomposition(J, Software => BERTINI);
    rawPts := apply(N#0, W -> matrix pack(d,W#Points#0#Coordinates));
    select(rawPts/clean_((10.0)^(-n)), M -> unique(flatten entries M/imaginaryPart) == {0_RR})
)
makeOrthogonalMatrix RingElement := Matrix => f -> makeOrthogonalMatrix(5, f)


-- Helper functions for makeOrthogonalMatrix

makeUvector = method()
makeUvector (List, ZZ) := List => (D, k) -> (
    Nk := subsets(#D,k);
    transpose matrix{apply(Nk, s -> product(s, i -> D_i))}
)

makeUComp = method()
makeUComp (List, ZZ, ZZ) := List => (D, k, k') -> (
    Nk := subsets(#D, k);
    Nk1 := subsets(#D, k');
    transpose matrix{apply(Nk1, s -> sum flatten((select(Nk, t -> #((set t)*(set s)) == 0))/(S -> product(D_S))))}
)

isMajorized = method()
isMajorized (RR, List, List) := Boolean => (eps, v, w) -> (
    (v,w) = (v,w)/rsort;
    if not clean(eps, sum v - sum w) == 0 then return false;
    all(#v, k -> clean(eps, sum(v_{0..k}) - sum(w_{0..k})) >= 0)
)


makeOrthostochasticMatrix = method()
makeOrthostochasticMatrix RingElement := Matrix => f -> (
    R := ring f;
    R1 := (coefficientRing R)[R_0];
    R2 := (coefficientRing R)[R_1];
    f1 := sub(sub(f, R_1 => 0), R1);
    f2 := sub(sub(f, R_0 => 0), R2);
    r1 := roots(f1);
    r2 := roots(f2);
    D1 := reverse sort(apply(r1,r -> -1/r) | toList(3-#r1:0));
    D2 := reverse sort(apply(r2,r -> -1/r) | toList(3-#r2:0));
    d := #D1;
    if not all(D1 | D2, r -> clean((10.0)^(-n), imaginaryPart r) == 0) then (
	print("Not a real zero polynomial - no determinantal representation of size " | d);
	return;
    );
    (D1, D2) = (D1/realPart, D2/realPart);
    C1 := last coefficients(f, Monomials => apply(d, i -> R_{1,i}));
    G1 := sub(matrix table(d,d,(i,j) -> sum apply(subsets(toList(0..<d)-set{j},i), s -> product(D2_s))), RR);
    diag1 := solve(G1, sub(C1,RR));
    if not isMajorized((10.0)^(-n), D1,flatten entries diag1) then (
	print(toString(D1) | " is not majorized by " | toString(diag1));
	return;
    );
    C2 := last coefficients(f, Monomials => apply(d, i -> R_{i,1}));
    G2 := sub(matrix table(d,d,(i,j) -> sum apply(subsets(toList(0..<d)-set{j},i), s -> product(D1_s))), RR);
    diag2 := solve(G2,sub(C2,RR));
    if not isMajorized((10.0)^(-n), D2,flatten entries diag2) then (
	print(toString(D2) | " is not majorized by " | toString(diag2));
	return;
    );
    D1 = transpose matrix{D1};
    D2 = transpose matrix{D2};
     
    R:=RR[q11,q12,q21,q22];
    q11=(diag2_(0,0)-D2_(2,0)-q12*(D2_(1,0)-D2_(2,0)))/(D2_(0,0)-D2_(2,0))
    q21=(-(D1_(0,0)-D1_(2,0))*(diag2_(0,0)-D2_(2,0)-q12*(D2_(1,0)-D2_(2,0)))+(D2_(0,0)-D2_(2,0))*(diag1_(0,0)-D1_(1,0)))/((D1_(1,0)-D1_(2,0))*(D2_(0,0)-D2_(2,0)))
    q22=(diag1_(0,0)-D1_(2,0)-q12*(D1_(0,0)-D1_(2,0)))/(D1_(1,0)-D2_(2,0))
    
    
    
    
    y := symbol y;
    T := RR[y_0..y_(d^2-1)];
    A := genericMatrix(T,d,d);
    L := minors(1, (transpose A)*D1-diag1)+minors(1, A*D2-diag2);
    allOnes := transpose matrix{apply(d, i -> 1_T)};
    rowsum := minors(1, A*allOnes - allOnes);
    colsum := minors(1, (transpose A)*allOnes - allOnes);
    
)



--Compute Generalized Mixed discriminant of matrices

generalizedMixedDiscriminant = method()
generalizedMixedDiscriminant List := RingElement => L -> (
    T := tally L;
    m := #keys T;
    k := #L;
    n := numcols L#0;
    Sk := subsets(n,k);
    Skv := unique permutations flatten apply(m, i -> toList((T#((keys T)#i)):i));
    sum flatten table(Sk, Skv, (alpha, sigma) -> det matrix table(k, k, (i,j) -> ((keys T)#(sigma#i))_(alpha#i,alpha#j)))
)

-- Helper functions for rounding

round (ZZ,CC) := (n,x) -> round(n, realPart x) + ii*round(n,imaginaryPart x)

round (ZZ,ZZ) := (n,x) -> x

roundMatrix = method() -- only accepts real matrices
roundMatrix (ZZ, Matrix) := Matrix => (n, A) -> matrix table(numrows A, numcols A, (i,j) -> (round(n,0.0+A_(i,j)))^QQ)

liftRealMatrix = method()
liftRealMatrix Matrix := Matrix => A -> (
    matrix table(numrows A, numcols A, (i,j) -> realPart A_(i,j))
)

beginDocumentation()

doc ///
    Key
        DeterminantalRepresentations
    Headline
    	computing definite determinantal representations of polynomials
    Description
    	Text
	    The goal of this package is to compute definite determinantal representations of bivariate polynomials.
///


-- Documentation --
-- <<docTemplate

-----------------------------

-- TESTS

TEST /// -- Quadratic determinantal representation tests
R = RR[x1,x2,x3]
f = 1 - 8*x1*x2 - 4*x1*x3 - 100*x2^2 - 12*x2*x3 - x3^2 - 5*x1^2
matrixCoeffs = apply(quadraticDetRep f, A -> sub(liftRealMatrix A, R))
assert(clean(1e-10, f - det(id_(R^2) + sum apply(#gens R, i -> matrixCoeffs#i*R_i))))
///

TEST /// -- Generalized mixed discriminant tests
n = 4
R = QQ[a_(1,1)..a_(n,n),b_(1,1)..b_(n,n)][x_1,x_2]
A = sub(transpose genericMatrix(coefficientRing R,n,n), R)
B = sub(transpose genericMatrix(coefficientRing R,b_(1,1),n,n), R)
P = det(id_(R^n) + x_1*A + x_2*B);
assert((last coefficients(P, Monomials => {x_1*x_2}))_(0,0) == generalizedMixedDiscriminant({A,B}))
assert((last coefficients(P, Monomials => {x_1^3*x_2}))_(0,0) == generalizedMixedDiscriminant({A,A,A,B}))
///

TEST ///
n = 3
R = QQ[a_(1,1)..a_(n,n),b_(1,1)..b_(n,n),c_(1,1)..c_(n,n)][x_1,x_2,x_n]
A = sub(transpose genericMatrix(coefficientRing R,n,n), R)
B = sub(transpose genericMatrix(coefficientRing R,b_(1,1),n,n), R)
C = sub(transpose genericMatrix(coefficientRing R,c_(1,1),n,n), R)
P = det(id_(R^n) + x_1*A + x_2*B + x_3*C);
assert((last coefficients(P, Monomials => {x_1^3*x_2^2*x_3}))_(0,0) == generalizedMixedDiscriminant({A,A,A,B,B,C}))
///


end--
restart
loadPackage("DeterminantalRepresentations", Reload => true)
uninstallPackage "DeterminantalRepresentations"
installPackage "DeterminantalRepresentations"
installPackage("DeterminantalRepresentations", RemakeAllDocumentation => true)
viewHelp "DeterminantalRepresentations"
check "DeterminantalRepresentations"


-- Examples of quadric

C = matrix{{1_RR,0,0,0},{0,-1,0,0},{0,0,-1,0},{0,0,0,-1}}
b=matrix{{2_RR},{0},{0},{0}} 
C = matrix{{-5_RR,-4,-2},{-4,-100,-6},{-2,-6,-1}}
b=matrix{{0_RR},{0},{0}}


--Cubic bivariate 
 
M = roundMatrix(5, matrix{{diag2_(0,0),diag2_(1,0),diag2_(2,0),0,0,0,0,0,0},{0,0,0,diag2_(0,0),diag2_(1,0),diag2_(2,0),0,0,0},{diag1_(0,0),0,0,diag1_(1,0),0,0,diag1_(2,0),0,0},{0,diag1_(0,0),0,0,diag1_(1,0),0,0,diag1_(2,0),0},{1,1,1,0,0,0,0,0,0},{0,0,0,1,1,1,0,0,0},{0,0,0,0,0,0,1,1,1},{1,0,0,1,0,0,1,0,0},{0,1,0,0,1,0,0,1,0}})
s = roundMatrix(5, matrix{{D2#0},{D2#1},{D1#0},{D1#1},{1},{1},{1},{1},{1}})

m=solve(M,s)
v=gens ker M
T=QQ[t]
q11 = m_(0,0)+t*v_(0,0)
q12 = m_(1,0)+t*v_(1,0)
q21 = m_(3,0)+t*v_(3,0)
q22 = m_(4,0)+t*v_(4,0)
C = (1_T-q11-q12-q21-q22+q11*q22+q12*q21)^2 - 4*q11*q12*q21*q22
roots C

--Examples of Cubic

R=QQ[x1,x2]
f=6*x1^3+36*x1^2*x2+11*x1^2+66*x1*x2^2+42*x1*x2+6*x1+36*x2^3+36*x2^2+11*x2+1
matrixList = makeOrthogonalMatrix f
G = toList((set{1,-1}) ^** 3) /deepSplice/toList/diagonalMatrix
Q1 = matrixList#0
removeOneOrbit = select(matrixList, A -> not any(G, g -> clean(1e-10, A - g*Q1) == 0));

S = CC[gens R]
D1=matrix{{3,0,0},{0,2,0},{0,0,1_S}}
D2=matrix{{6,0,0},{0,3,0},{0,0,2_S}}
Q = sub(Q1, S)
clean(1e-10, sub(f, S) - det(id_(S^3) + S_0*D1 + S_1*(transpose Q)*D2*Q)) == 0

-- Random cubic
A1 = random(R^3,R^3)
A2 = random(R^3,R^3)
(A1,A2) = (A1 + transpose A1, A2 + transpose A2)
f = det(id_(R^3) + R_0*A1 + R_1*A2)


-- Quartic examples
R = QQ[x1,x2]
f=(1/2)*(x1^4+x2^4-3*x1^2-3*x2^2+x1^2*x2^2)+1
matrixList = makeOrthogonalMatrix f

f=24*x1^4+(49680/289)*x1^3*x2+50*x1^3+(123518/289)*x1^2*x2^2+(72507/289)*x1^2*x2+35*x1^2+(124740/289)*x1*x2^3+(112402/289)*x1*x2^2+(32022/289)*x1*x2+10*x1+144*x2^4+180*x2^3+80*x2^2+15*x2+1

-- Random quartic
A1 = random(R^4,R^4)
A2 = random(R^4,R^4)
(A1,A2) = (A1 + transpose A1, A2 + transpose A2)
f = det(id_(R^4) + R_0*A1 + R_1*A2)

-- Permutation test
L = {1,1,2,2,2,3,3}
unique permutations L
--7!//(2!*3!*2!)

-- makeOrthogonalMatrix test

U = QQ[a_(1,1)..a_(3,3)]
L = ideal(a_(1,1)-(5-2*a_(1,2))/8, a_(1,3) - (3-6*a_(1,2))/8, a_(2,1) - (1+2*a_(1,2))/4, a_(2,2) - (1-2*a_(1,2)), a_(2,3) - (6*a_(1,2)-1)/4, a_(3,1) - (1-2*a_(1,2))/8, a_(3,3) - (7-6*a_(1,2))/8, a_(3,2) - a_(1,2))
I = sub(L, apply(gens U, v -> v => v^2))
A = genericMatrix(U,3,3)
O = minors(1, A*transpose A - id_(U^3))
J = I + O
time PD = primaryDecomposition J
#PD
PD/radical