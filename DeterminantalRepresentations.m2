newPackage("DeterminantalRepresentations",
	AuxiliaryFiles => false,
	Version => "0.0.3",
	Date => "January 19, 2019",
	Authors => {
		{Name => "Justin Chen",
		Email => "jchen646@gatech.edu"},
		{Name => "Papri Dey",
		Email => "papri_dey@brown.edu"}
	},
	Headline => "a package for computing determinantal representations",
	HomePage => "https://github.com/papridey/DeterminantalRepresentations",
	PackageExports => {"NumericalAlgebraicGeometry"},
	DebuggingMode => true,
        Reload => true
)
export {
    "quadraticDetRep",
    "cubicBivariateOrthostochastic",
    "bivariateOrthogonal",
    "bivariateSystem",
    "generalizedMixedDiscriminant",
    "orthogonalFromOrthostochastic",
    "bivariateDiagEntries",
    "roundMatrix",
    "hadamard"
}

-- Quadratic case

quadraticDetRep = method(Options => {Tolerance => 1e-6})
quadraticDetRep RingElement := List => opts -> f -> ( -- returns a list of matrices over original ring R
    R := ring f;
    n := #gens R;
    b := sub(last coefficients(f, Monomials => gens R), RR);
    A := sub(matrix table(n, n, (i,j) -> if i == j then (last coefficients(f, Monomials => {R_i^2}))_(0,0) else (1/2)*(last coefficients(f, Monomials => {R_i*R_j}))_(0,0)), RR);
    Q := (1/4)*b*transpose(b) - A;
    E := eigenvectors(Q, Hermitian => true);
    E = (E#0/clean_(opts.Tolerance), E#1);
    if not all(E#0, e -> e >= 0) then ( print "Not all eigenvalues nonnegative!"; return false; );
    if #select(E#0, e -> not(e == 0)) > 3 then ( print("Rank of matrix Q is " | rank(Q) | " (too large)!"); return false; );
    posEvalues := positions(E#0, e -> e > 0);
    posEvectors := apply(posEvalues, i -> (E#0#i,matrix E#1_i));
    r := (1/2)*b + sqrt(posEvectors#0#0)*posEvectors#0#1;
    s := (1/2)*b - sqrt(posEvectors#0#0)*posEvectors#0#1;
    t := if #posEvalues >= 2 then sqrt(posEvectors#1#0)*posEvectors#1#1 else 0*b;
    u := if #posEvalues == 3 then sqrt(posEvectors#2#0)*posEvectors#2#1 else 0*b;
    L := apply(n, i -> matrix{{r_(i,0),t_(i,0) - ii*u_(i,0)},{t_(i,0)+ii*u_(i,0),s_(i,0)}});
    if not class ultimate (coefficientRing, R) === ComplexField then L = L/liftRealMatrix/clean_(opts.Tolerance);
    if ultimate (coefficientRing, R) === QQ then L = L/roundMatrix_(ceiling(log_10(1/opts.Tolerance)));
    apply(L, M -> sub(M, R))
)

-- Cubic bivariate case

cubicBivariateOrthostochastic = method(Options => options quadraticDetRep)
cubicBivariateOrthostochastic RingElement := List => opts -> f -> ( -- returns a list of orthostochastic matrices
    (D1, D2, diag1, diag2) := bivariateDiagEntries(f, opts);
    S := RR(monoid[getSymbol "q12"]);
    q11 := (diag2_(0,0)-D2_(2,0)-S_0*(D2_(1,0)-D2_(2,0)))/(D2_(0,0)-D2_(2,0));
    q21 := (-(D1_(0,0)-D1_(2,0))*(diag2_(0,0)-D2_(2,0)-S_0*(D2_(1,0)-D2_(2,0)))+(D2_(0,0)-D2_(2,0))*(diag1_(0,0)-D1_(2,0)))/((D1_(1,0)-D1_(2,0))*(D2_(0,0)-D2_(2,0)));
    q22 := (diag1_(1,0)-D1_(2,0)-S_0*(D1_(0,0)-D1_(2,0)))/(D1_(1,0)-D1_(2,0));
    Q := matrix{{q11, S_0, 1 - S_0 - q11}, {q21, q22, 1 - q21 - q22}, {1 - q11 - q21, 1 - S_0 - q22, 1 - (1 - S_0 - q11) - (1 - q21 - q22)}};
    apply(roots((1 - q11 - q22 - S_0 - q21 + q11*q22 + S_0*q21)^2 - 4*q11*q22*S_0*q21), r -> sub(Q, S_0 => r))
)

orthogonalFromOrthostochastic = method(Options => options quadraticDetRep)
orthogonalFromOrthostochastic Matrix := List => opts -> M -> (
    if min(flatten entries M) < 0 then return {};
    N := matrix apply(entries M, r -> r/sqrt);
    d := numrows M;
    sgn := toList((set{1,-1}) ^** (d-1))/deepSplice/toList;
    row1 := transpose N^{0};
    validRows := {{N^{0}}};
    for i from 1 to numrows N-1 do (
        for S in sgn do (
            candidate := hadamard(matrix{{1} | S}, N^{i});
            if clean(opts.Tolerance, candidate*row1) == 0 then (
                validRows = append(validRows, {candidate});
                break;
            );
        );
    );
    matrix validRows
)

-- General bivariate case 
-- via orthogonal matrices

bivariateOrthogonal = method(Options => {Tolerance => 1e-6, Software => M2engine})
bivariateOrthogonal RingElement := List => opts -> f -> ( -- returns a list of orthogonal matrices
    (D1, D2, diag1, diag2) := bivariateDiagEntries(f, Tolerance => opts.Tolerance);
    d := first degree f;
    y := getSymbol "y";
    T := RR(monoid[y_0..y_(d^2-1)]);
    A := genericMatrix(T,d,d);
    L := minors(1, (transpose A)*D1-diag1)+minors(1, A*D2-diag2);
    allOnes := transpose matrix{apply(d, i -> 1_T)};
    rowsum := minors(1, A*allOnes - allOnes);
    colsum := minors(1, (transpose A)*allOnes - allOnes);
    J := minors(1, A*transpose A - id_(T^d)) + sub(L + rowsum + colsum, apply(gens T, v -> v => v^2));
    print "Computing orthogonal matrices numerically ...";
    elapsedTime N := numericalIrreducibleDecomposition(J, Software => opts.Software);
    rawPts := apply(N#0, W -> matrix pack(d,W#Points#0#Coordinates));
    select(rawPts/clean_(opts.Tolerance), M -> unique(flatten entries M/imaginaryPart) == {0_RR})
)

-- via solving polynomial system numerically

bivariateSystem = method(Options => options bivariateOrthogonal)
bivariateSystem RingElement := List => opts -> F -> (
    (D1, D2, diag1, diag2) := bivariateDiagEntries(F, Tolerance => opts.Tolerance);
    D := flatten entries D1;
    R := ring F;
    d := first degree F;
    S := R/(ideal gens R)^(d+1);
    mons := lift(super basis(ideal(S_1^2)), R);
    C := last coefficients(F, Monomials => mons);
    e := getSymbol "e";
    T := RR(monoid[e_1..e_(binomial(d,2))]);
    S = T[gens R];
    A := genericSkewMatrix(T, d);
    B := matrix table(d, d, (i,j) -> if i == j then diag2_(i,0) else A_(min(i,j),max(i,j)));
    G := det(id_(S^d) + S_0*sub(diagonalMatrix D, S) + S_1*sub(B, S));
    C1 := last coefficients(G, Monomials => sub(mons, S)) - sub(C, S);
    P := polySystem sub(clean(opts.Tolerance, C1), T);
    print ("Solving " | binomial(d,2) | " x " | binomial(d,2) | " polynomial system...");
    time sols := select(solveSystem(P, Software => opts.Software), p -> not status p === RefinementFailure);
    realPoints apply(sols, p -> point{p#Coordinates/clean_(opts.Tolerance)})
)

-- Helper functions for bivariate case

makeUvector = method()
makeUvector (List, ZZ) := List => (D, k) -> (
    Nk := subsets(#D,k);
    transpose matrix{apply(Nk, s -> product(s, i -> D_i))}
)

makeUComp = method()
makeUComp (List, ZZ, ZZ) := List => (D, k, l) -> (
    Nk := subsets(#D, k);
    Nl := subsets(#D, l);
    transpose matrix{apply(Nl, s -> sum flatten((select(Nk, t -> #((set t)*(set s)) == 0))/(S -> product(D_S))))}
)

isMajorized = method(Options => options quadraticDetRep)
isMajorized (List, List) := Boolean => opts -> (v, w) -> (
    (v,w) = (v,w)/rsort;
    if not clean(opts.Tolerance, sum v - sum w) == 0 then return false;
    all(#v, k -> clean(opts.Tolerance, sum(v_{0..k}) - sum(w_{0..k})) >= 0)
)

bivariateDiagEntries = method(Options => options quadraticDetRep)
bivariateDiagEntries RingElement := Sequence => opts -> f -> ( -- returns diagonal entries and eigenvalues of coefficient matrices
    R := ring f;
    (R1, R2) := ((coefficientRing R)(monoid[R_0]), (coefficientRing R)(monoid[R_1]));
    (f1, f2) := (sub(sub(f, R_1 => 0), R1), sub(sub(f, R_0 => 0), R2));
    (r1, r2) := (f1, f2)/roots;
    D1 := reverse sort(apply(r1,r -> -1/r) | toList(3-#r1:0));
    D2 := reverse sort(apply(r2,r -> -1/r) | toList(3-#r2:0));
    d := #D1;
    if not all(D1 | D2, r -> clean(opts.Tolerance, imaginaryPart r) == 0) then (
	error("Not a real zero polynomial - no determinantal representation of size " | d);
    );
    (D1, D2) = (D1/realPart, D2/realPart);
    C1 := last coefficients(f, Monomials => apply(d, i -> R_{1,i}));
    G1 := sub(matrix table(d,d,(i,j) -> sum apply(subsets(toList(0..<d)-set{j},i), s -> product(D2_s))), RR);
    diag1 := solve(G1, sub(C1,RR));
    if not isMajorized(D1, flatten entries diag1, opts) then (
	error(toString(D1) | " is not majorized by " | toString(diag1));
    );
    C2 := last coefficients(f, Monomials => apply(d, i -> R_{i,1}));
    G2 := sub(matrix table(d,d,(i,j) -> sum apply(subsets(toList(0..<d)-set{j},i), s -> product(D1_s))), RR);
    diag2 := solve(G2,sub(C2,RR));
    if not isMajorized(D2, flatten entries diag2, opts) then (
	error(toString(D2) | " is not majorized by " | toString(diag2));
    );
    (transpose matrix{D1}, transpose matrix{D2}, diag1, diag2)
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

-- Helper functions

round (ZZ,CC) := (n,x) -> round(n, realPart x) + ii*round(n,imaginaryPart x)
round (ZZ,ZZ) := (n,x) -> x

roundMatrix = method() -- only accepts real matrices
roundMatrix (ZZ, Matrix) := Matrix => (n, A) -> matrix apply(entries A, r -> r/(e -> (round(n,0.0+e))^QQ))

liftRealMatrix = method()
liftRealMatrix Matrix := Matrix => A -> matrix apply(entries A, r -> r/realPart)

hadamard = method()
hadamard (Matrix, Matrix) := Matrix => (A, B) -> (
    if not(numcols A == numcols B and numrows A == numrows B) then error "Expected same size matrices";
    matrix table(numrows A, numcols A, (i,j) -> A_(i,j)*B_(i,j))
)

randomIntegerSymmetric := (d, R) -> ( A := random(ZZ^d,ZZ^d); sub(A + transpose A, R) )

-- Documentation --
-- <<docTemplate

beginDocumentation()

doc ///
    Key
        DeterminantalRepresentations
    Headline
    	computing determinantal representations of polynomials
    Description
    	Text
	    The goal of this package is to compute determinantal representations of polynomials. To be precise, a polynomial $f$ in $\mathbb{R}[x_1, \ldots, x_n]$ of total degree $d$ (not necessarily homogeneous) is called determinantal if $f$ is the determinant of a matrix of linear forms - in other words, there exist matrices $A_0, \ldots, A_n \in \mathbb{R}^{d\times d}$ such that $f(x_1, \ldots, x_n) = det(A_0 + x_1A_1 + \ldots + x_nA_n)$. We say that the matrices $A_0, \ldots, A_n$ give a determinantal representation of $f$ of size $d$. If the matrices $A_i$ can be chosen to be all symmetric (respectively, Hermitian), then the determinantal representation is called symmetric (resp. Hermitian). The determinantal representation is called definite if $A_0$ is positive definite, and monic if $A_0 = I_d$ is the identity matrix. 
            
            Even detecting whether or not a degree $d$ polynomial has a determinantal representation of size $d$ is difficult, and computing such a representation even more so. Computing (monic) symmetric determinantal representations of bivariate polynomials is already of interest, owing to a connection with real-zero and hyperbolic polynomials, due to a celebrated theorem of Helton-Vinnikov. In general, determinantal polynomials also have connections to convex algebraic geometry and semidefinite programming.
            
            Currently, the functions in this package are geared towards computing monic symmetric determinantal representations of quadrics, as well as bivariate cubics and quartics. The algorithms in this package can be found in [Dey1], [Dey2].
///

doc ///
    Key
        quadraticDetRep
        (quadraticDetRep, RingElement)
        [quadraticDetRep, Tolerance]
    Headline
        computes determinantal representation of a quadric
    Usage
        quadraticDetRep f
        quadraticDetRep(f, Tolerance => 1e-6)
    Inputs
        f:RingElement
            a quadric with real coefficients
    Outputs
        :List
            of matrices, giving a determinantal representation of f
    Description
        Text
            This method computes a monic symmetric determinantal representation of a real quadric $f$, or returns false if no such representation exists.
            
            As this algorithm performs computations with floating point numbers, one can use the optional input {\tt Tolerance} to specify the internal threshold for checking equality.
        
        Example
            -- R = RR[x1, x2]
            -- f = 15*x1^2 + 20*x1*x2 - 36*x2^2 + 20*x1 + 16*x2 + 1
            -- A = quadraticDetRep f
            -- clean(1e-10, f - det(id_(R^2) + x1*A#0 + x2*A#1))
            R = RR[x1, x2, x3, x4]
            f = 260*x1^2+180*x1*x2-25*x2^2-140*x1*x3-170*x2*x3-121*x3^2+248*x1*x4+94*x2*x4-142*x3*x4+35*x4^2+36*x1+18*x2+2*x3+20*x4+1
            time A = quadraticDetRep f
            clean(1e-10, f - det(id_(R^2) + sum(#gens R, i -> R_i*A#i)))
    SeeAlso
        DeterminantalRepresentations
///

doc ///
    Key
        bivariateDiagEntries
        (bivariateDiagEntries, RingElement)
        [bivariateDiagEntries, Tolerance]
    Headline
        computes diagonal entries and eigenvalues for a determinantal representation of a bivariate polynomial
    Usage
        bivariateDiagEntries f
        bivariateDiagEntries(f, Tolerance => 1e-6)
    Inputs
        f:RingElement
            a bivariate polynomial with real coefficients
    Outputs
        :Sequence
            consisting of eigenvalues and diagonal entries of a potential determinantal representation of f
    Description
        Text
            This method computes the eigenvalues and diagonal entries of a (potential) monic symmetric determinantal representation of a real bivariate polynomial $f$, or returns false certain necessary conditions for existence of such a representation are not met.
            
            As this algorithm performs computations with floating point numbers, one can use the optional input {\tt Tolerance} to specify the internal threshold for checking equality.
        
        Example
            R = RR[x1, x2]
            f = 15*x1^2 + 20*x1*x2 - 36*x2^2 + 20*x1 + 16*x2 + 1
            bivariateDiagEntries f
    SeeAlso
        DeterminantalRepresentations
///

doc ///
    Key
        generalizedMixedDiscriminant
        (generalizedMixedDiscriminant, List)
    Headline
        computes generalized mixed discriminant of a list of matrices
    Usage
        generalizedMixedDiscriminant L
    Inputs
        L:List
            an $n$-tuple of $n\times n$ matrices
    Outputs
        :RingElement
            the generalized mixed discriminant of L
    Description
        Text
            This method computes the generalized mixed discriminant of $n$-tuple of $n\times n$ matrices.
                 
        Example
            n = 3
            R = QQ[a_(1,1)..a_(n,n),b_(1,1)..b_(n,n),c_(1,1)..c_(n,n)][x_1..x_n]
            A = sub(transpose genericMatrix(coefficientRing R,n,n), R)
            B = sub(transpose genericMatrix(coefficientRing R,b_(1,1),n,n), R)
            C = sub(transpose genericMatrix(coefficientRing R,c_(1,1),n,n), R)
            P = det(id_(R^n) + x_1*A + x_2*B + x_3*C);
	    gmd = generalizedMixedDiscriminant({A,B,C})
	    coeff = (last coefficients(P, Monomials => {x_1*x_2*x_3}))_(0,0)
            gmd == coeff
    SeeAlso
        DeterminantalRepresentations
///


-----------------------------

-- TESTS

TEST /// -- Quadratic determinantal representation tests
R = RR[x1,x2,x3]
f = 1 - 8*x1*x2 - 4*x1*x3 - 100*x2^2 - 12*x2*x3 - x3^2 - 5*x1^2
coeffMatrices = quadraticDetRep f
assert(0 == clean(1e-10, f - det(id_(R^2) + sum apply(#gens R, i -> coeffMatrices#i*R_i))))
///

TEST /// -- cubic case tests
R=QQ[x1,x2]
f=6*x1^3+36*x1^2*x2+11*x1^2+66*x1*x2^2+42*x1*x2+6*x1+36*x2^3+36*x2^2+11*x2+1
orthostochasticMatrices = cubicBivariateOrthostochastic f
L1 = orthogonalFromOrthostochastic last orthostochasticMatrices
M = matrix{{0.5322,0.3711,0.0967},{0.4356,0.2578,0.3066},{0.0322,0.3711,0.5967}}
L2 = orthogonalFromOrthostochastic M
assert(all(L2, M -> any(L1, N -> 0 == clean(1e-4, N - M))))
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
R = QQ[a_(1,1)..a_(n,n),b_(1,1)..b_(n,n),c_(1,1)..c_(n,n)][x_1..x_n]
A = sub(transpose genericMatrix(coefficientRing R,n,n), R)
B = sub(transpose genericMatrix(coefficientRing R,b_(1,1),n,n), R)
C = sub(transpose genericMatrix(coefficientRing R,c_(1,1),n,n), R)
P = det(id_(R^n) + x_1*A + x_2*B + x_3*C);
assert((last coefficients(P, Monomials => {x_1*x_2*x_3}))_(0,0) == generalizedMixedDiscriminant({A,B,C}))
-- assert((last coefficients(P, Monomials => {x_1^3*x_2^2*x_3}))_(0,0) == generalizedMixedDiscriminant({A,A,A,B,B,C})) -- these coefficients are 0
///

end--
restart
loadPackage("DeterminantalRepresentations", Reload => true)
uninstallPackage "DeterminantalRepresentations"
installPackage "DeterminantalRepresentations"
installPackage("DeterminantalRepresentations", RemakeAllDocumentation => true)
viewHelp "DeterminantalRepresentations"
check "DeterminantalRepresentations"

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
matrixList = bivariateOrthogonal f
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


-- Degenerate cubic
R = QQ[x1,x2]
f = 162*x1^3 - 23*x1^2*x2 + 99*x1^2 - 8*x1*x2^2 - 10*x1*x2 + 18*x1 + x2^3 - x2^2 - x2 + 1
cubicBivariateOrthostochastic f


-- Quartic examples
R = QQ[x1,x2]
f=(1/2)*(x1^4+x2^4-3*x1^2-3*x2^2+x1^2*x2^2)+1
matrixList = bivariateOrthogonal f

f=24*x1^4+(49680/289)*x1^3*x2+50*x1^3+(123518/289)*x1^2*x2^2+(72507/289)*x1^2*x2+35*x1^2+(124740/289)*x1*x2^3+(112402/289)*x1*x2^2+(32022/289)*x1*x2+10*x1+144*x2^4+180*x2^3+80*x2^2+15*x2+1

-- Random quartic
A1 = random(R^4,R^4)
A2 = random(R^4,R^4)
(A1,A2) = (A1 + transpose A1, A2 + transpose A2)
f = det(id_(R^4) + R_0*A1 + R_1*A2)


clearAll
R = RR[x,y];A = sub(diagonalMatrix{5,6,7,8},R);f = det(id_(R^4) + x*sub(diagonalMatrix {1,2,3,4},R) + y*A);

R = RR[x,y]
A = sub(diagonalMatrix{5,6,7,8},R)
f = det(id_(R^4) + x*sub(diagonalMatrix {1,2,3,4},R) + y*A)
bivariateSystem f -- diagonal case
A = sub(random(ZZ^4,ZZ^4), R)
f = det(id_(R^4) + x*sub(diagonalMatrix {1,2,3,4},R) + y*(A + transpose A))
f = det(id_(R^4) + x*sub(diagonalMatrix {4,3,2,1},R) + y*(A + transpose A))
bivariateSystem f


-- Quintic

mons := matrix{{R_1^2, R_0*R_1^2, R_0^2*R_1^2, R_1^3, R_0*R_1^3, R_1^4, R_0^3*R_1^2, R_0^2*R_1^3, R_0*R_1^4, R_1^5}};
S = R/(ideal gens R)^6
sort flatten entries lift(super basis(ideal(S_1^2)), R)

R = RR[x,y]
A = sub(random(ZZ^5,ZZ^5),R)
f = det(id_(R^5) + x*sub(diagonalMatrix {1,2,3,4,5},R) + y*(A + transpose A))

-- bivariateOrthogonal test

U = QQ[a_(1,1)..a_(3,3)]
L = ideal(a_(1,1)-(5-2*a_(1,2))/8, a_(1,3) - (3-6*a_(1,2))/8, a_(2,1) - (1+2*a_(1,2))/4, a_(2,2) - (1-2*a_(1,2)), a_(2,3) - (6*a_(1,2)-1)/4, a_(3,1) - (1-2*a_(1,2))/8, a_(3,3) - (7-6*a_(1,2))/8, a_(3,2) - a_(1,2))
I = sub(L, apply(gens U, v -> v => v^2))
A = genericMatrix(U,3,3)
O = minors(1, A*transpose A - id_(U^3))
J = I + O
time PD = primaryDecomposition J
#PD
PD/radical