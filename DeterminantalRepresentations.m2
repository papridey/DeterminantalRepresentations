newPackage("DeterminantalRepresentations",
	AuxiliaryFiles => false,
	Version => "0.0.4",
	Date => "February 8, 2019",
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
    "liftRealMatrix",
    "hadamard",
    "isOrthogonal",
    "isDoublystochastic",
    "randomIntegerSymmetric",
    "randomOrthostochastic"
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
    select(apply(roots((1 - q11 - q22 - S_0 - q21 + q11*q22 + S_0*q21)^2 - 4*q11*q22*S_0*q21), r -> liftRealMatrix sub(Q, S_0 => r)), isDoublystochastic)
)

orthogonalFromOrthostochastic = method(Options => options quadraticDetRep)
orthogonalFromOrthostochastic Matrix := List => opts -> M -> (
    if min(flatten entries M) < 0 then return {};
    N := matrix apply(entries M, r -> r/sqrt);
    d := numrows M;
    sgn := drop(sort toList((set{1,-1}) ^** (d-1))/deepSplice/toList, -1);
    validRows := {{{N^{0}}}};
    for i from 1 to numrows N-1 do (
        validRows = flatten apply(validRows, rowset -> apply(select(sgn/(S -> hadamard(matrix{{1} | S}, N^{i})), candidate -> clean(opts.Tolerance, matrix rowset * transpose candidate) == 0), r -> append(rowset, {r})));
    );
    unique validRows/matrix
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

-- General helper functions

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

-- Tests for matrix classes

isOrthogonal = method(Options => options quadraticDetRep)
isOrthogonal Matrix := Boolean => opts -> A -> (
    if not numcols A == numrows A then (
        if debugLevel > 0 then print "Not a square matrix";
        return false;
    );
    delta := A*transpose A - id_((ring A)^(numcols A));
    if instance(class 1_(ultimate(coefficientRing, ring A)), InexactFieldFamily) then delta = clean(opts.Tolerance, delta);
    delta == 0
)

isDoublystochastic = method(Options => options quadraticDetRep)
isDoublystochastic Matrix := Boolean => opts -> A -> (
    n := numcols A;
    if not numrows A == n then ( if debugLevel > 0 then print "Not a square matrix"; return false; );
    if not class(ultimate(coefficientRing, ring A)) === RealField then ( if debugLevel > 0 then print "Not a real matrix"; return false; );
    if not min flatten entries A >= 0 then ( if debugLevel > 0 then print "Not all entries are nonnegative"; return false; );
    v := matrix{toList(n:1_RR)};
    if not clean(opts.Tolerance, v*A - v) == 0 and clean(opts.Tolerance, A*transpose v - transpose v) == 0 then ( if debugLevel > 0 then print "Not doubly stochastic"; return false; );
    true
)

-- Construct various types of matrices

randomIntegerSymmetric = method()
randomIntegerSymmetric (ZZ, Ring) := Matrix => (d, R) -> ( 
    A := random(ZZ^d,ZZ^d); 
    sub(A + transpose A, R)
)
randomIntegerSymmetric ZZ := Matrix => d -> randomIntegerSymmetric(d, ZZ)

randomOrthostochastic = method(Options => options quadraticDetRep)
randomOrthostochastic ZZ := Matrix => opts -> n -> (
    o := symbol o;
    R := RR[o_(1,1)..o_(n,n)];
    A := genericMatrix(R, n, n);
    I := ideal apply(subsets(n, 2) /toSequence | apply(n, i -> 2:i), s -> (A*transpose A - id_(R^n))_s);
    p0 := point id_(RR^n);
    p := (track(I_* | flatten entries((vars R - matrix p0)*random(RR^(n^2), RR^(n^2 - #I_*))), I_* | flatten entries(vars R*random(RR^(n^2), RR^(n^2 - #I_*))), {p0}))#0#Coordinates;
    clean(opts.Tolerance, liftRealMatrix matrix pack(n, apply(p, c -> c^2)))
)

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
	    The goal of this package is to compute determinantal representations of polynomials. To be precise, a polynomial $f$ in $\mathbb{R}[x_1, \ldots, x_n]$ of total degree $d$ (not necessarily homogeneous) is called determinantal if $f$ is the determinant of a matrix of linear forms - in other words, there exist matrices $A_0, \ldots, A_n \in \mathbb{R}^{d\times d}$ such that $f(x_1, \ldots, x_n) = det(A_0 + x_1A_1 + \ldots + x_nA_n)$. The matrices $A_0, \ldots, A_n$ are said to give a determinantal representation of $f$ of size $d$. If the matrices $A_i$ can be chosen to be all symmetric (respectively, Hermitian), then the determinantal representation is called symmetric (resp. Hermitian). The determinantal representation is called definite if $A_0$ is positive definite, and monic if $A_0 = I_d$ is the identity matrix. 
            
            Detecting whether or not a degree $d$ polynomial has a determinantal representation of size $d$ is already difficult, and computing such a representation even more so. Computing (monic) symmetric determinantal representations of bivariate polynomials is of interest owing to a connection with real-zero and hyperbolic polynomials, due to a celebrated theorem of Helton-Vinnikov. In general, determinantal polynomials also have connections to convex algebraic geometry and semidefinite programming.
            
            Currently, the functions in this package are geared towards computing monic symmetric determinantal representations of quadrics, as well as bivariate cubics and quartics. The algorithms implemented in this package can be found in [Dey1], [Dey2].
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
            of matrices, giving a determinantal representation of $f$
    Description
        Text
            This method computes a monic symmetric determinantal representation of a real quadric $f$, or returns false if no such representation exists.
            
            The option {\tt Tolerance} can be used to specify the internal threshold for checking equality (any floating point number below the tolerance is treated as numerically zero).
        
        Example
            R = RR[x1, x2, x3, x4]
            f = 260*x1^2+180*x1*x2-25*x2^2-140*x1*x3-170*x2*x3-121*x3^2+248*x1*x4+94*x2*x4-142*x3*x4+35*x4^2+36*x1+18*x2+2*x3+20*x4+1
            time A = quadraticDetRep f
            clean(1e-10, f - det(id_(R^2) + sum(#gens R, i -> R_i*A#i)))
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
            of eigenvalues and diagonal entries of a determinantal representation of $f$
    Description
        Text
            This method computes the eigenvalues and diagonal entries of a monic symmetric determinantal representation of a real bivariate polynomial $f$, or returns false if certain necessary conditions for existence of such a representation are not met. For a symmetric determinantal representation $f = det(I + x_1A_1 + x_2A_2)$, this method computes diagonal entries and eigenvalues of $A_1$ and $A_2$. The output is a 4-tuple of column vectors: (eigenvalues of A_1, eigenvalues of $A_2$, diagonal entries of $A_1$, diagonal entries of $A_2$).
            
            The option {\tt Tolerance} can be used to specify the internal threshold for checking equality (any floating point number below the tolerance is treated as numerically zero).
        
        Example
            R = RR[x1, x2]
            f = 15*x1^2 + 20*x1*x2 - 36*x2^2 + 20*x1 + 16*x2 + 1
            bivariateDiagEntries f
///

doc ///
    Key
        cubicBivariateOrthostochastic
        (cubicBivariateOrthostochastic, RingElement)
        [cubicBivariateOrthostochastic, Tolerance]
    Headline
        computes orthostochastic matrices for a determinantal representation of a cubic bivariate polynomial
    Usage
        cubicBivariateOrthostochastic f
        cubicBivariateOrthostochastic(f, Tolerance => 1e-6)
    Inputs
        f:RingElement
            a cubic bivariate polynomial with real coefficients
    Outputs
        :List
            of orthostochastic matrices corresponding to determinantal representations of $f$
    Description
        Text
            This method computes @TO2{randomOrthostochastic, "orthostochastic"}@ matrices used in finding a monic symmetric determinantal representation of a real cubic bivariate polynomial $f$, or returns false if certain necessary conditions for existence of such a representation are not met. For a symmetric determinantal representation $f = det(I + x_1A_1 + x_2A_2)$, by suitable conjugation one may assume $A_1 = D_1$ is a diagonal matrix. Since $A_2$ is symmetric, by the spectral theorem there exist an orthogonal change-of-basis matrix $V$ such that $VA_2V^T = D_2$ is diagonal. Since $D_1, D_2$ can be found using the method @TO bivariateDiagEntries@, to find a symmetric determinantal representation of $f$ it suffices to compute the orthogonal matrix $V$. This method computes the orthostochastic matrix which is the Hadamard square of $V$, via the algorithm in [Dey1].
            
            The option {\tt Tolerance} can be used to specify the internal threshold for checking equality (any floating point number below the tolerance is treated as numerically zero).
        
        Example
            R = RR[x1, x2]
            f=6*x1^3+36*x1^2*x2+11*x1^2+66*x1*x2^2+42*x1*x2+6*x1+36*x2^3+36*x2^2+11*x2+1
            cubicBivariateOrthostochastic f
    SeeAlso
        bivariateDiagEntries
        orthogonalFromOrthostochastic
///

doc ///
    Key
        orthogonalFromOrthostochastic
        (orthogonalFromOrthostochastic, Matrix)
        [orthogonalFromOrthostochastic, Tolerance]
    Headline
        computes orthogonal matrices for a given orthostochastic matrix
    Usage
        orthogonalFromOrthostochastic A
        cubicBivariateOrthostochastic(A, Tolerance => 1e-6)
    Inputs
        A:Matrix
            an orthostochastic matrix
    Outputs
        :List
            of orthogonal matrices whose Hadamard square is $A$
    Description
        Text
            This method computes orthogonal matrices whose Hadamard square is a given @TO2{randomOrthostochastic, "orthostochastic"}@ matrix. Combined with the method @TO cubicBivariateOrthostochastic@, this allows one to compute symmetric determinantal representations of real cubic bivariate polynomials. 
            
            Given a $n\times n$ orthostochastic matrix $A$, there are $2^{n^2}$ possible matrices whose Hadamard square is $A$ (not all of which will be orthogonal in general though). Let $G\cong (\ZZ/2\ZZ)^n$ be the group of diagonal matrices with diagonal entries equal to &plusmn;1. One can act (on the left and right) by $G\times G$ on the set of orthogonal matrices whose Hadamard square is $A$. This method computes all such orthogonal matrices, modulo the action of $G\times G$. The representative for each orbit is chosen so that the first row and column will have nonnegative entries.
            
            The option {\tt Tolerance} can be used to specify the internal threshold for checking equality (any floating point number below the tolerance is treated as numerically zero).
        
        Example
            R = RR[x1, x2]
            f=6*x1^3+36*x1^2*x2+11*x1^2+66*x1*x2^2+42*x1*x2+6*x1+36*x2^3+36*x2^2+11*x2+1
            L = cubicBivariateOrthostochastic f
            apply(L, orthogonalFromOrthostochastic)
            A = randomOrthostochastic 4
            orthogonalFromOrthostochastic A
    SeeAlso
        cubicBivariateOrthostochastic
///

doc ///
    Key
        bivariateOrthogonal
        (bivariateOrthogonal, RingElement)
        [bivariateOrthogonal, Tolerance]
        [bivariateOrthogonal, Software]
    Headline
        computes orthogonal matrices for a determinantal representation of a bivariate polynomial
    Usage
        bivariateOrthogonal f
        bivariateOrthogonal(f, Tolerance => 1e-6)
    Inputs
        f:RingElement
            a bivariate polynomial with real coefficients
    Outputs
        :List
            of orthogonal matrices corresponding to determinantal representations of $f$
    Description
        Text
            This method computes orthogonal matrices used in finding a monic symmetric determinantal representation of a real bivariate polynomial $f$. For a symmetric determinantal representation $f = det(I + x_1A_1 + x_2A_2)$, by suitable conjugation one may assume $A_1 = D_1$ is a diagonal matrix. Since $A_2$ is symmetric, by the spectral theorem there exist an orthogonal change-of-basis matrix $V$ such that $VA_2V^T = D_2$ is diagonal. Since $D_1, D_2$ can be found using the method @TO bivariateDiagEntries@, to find a symmetric determinantal representation of $f$ it suffices to compute the orthogonal matrix $V$. This method computes the orthogonal matrix $V$ via numerical algebraic geometry.
            
            The option {\tt Tolerance} can be used to specify the internal threshold for checking equality (any floating point number below the tolerance is treated as numerically zero). The option @TO Software@ specifies the numerical algebraic geometry software used to perform a numerical irreducible decomposition: by default, the native M2engine is used, although other valid options include BERTINI and PHCPACK (if the user has these installed on their system).
        
        Example
            R = RR[x1, x2]
            f=6*x1^3+36*x1^2*x2+11*x1^2+66*x1*x2^2+42*x1*x2+6*x1+36*x2^3+36*x2^2+11*x2+1
            bivariateOrthogonal f
    Caveat
        Due to the time-consuming process of computing a numerical irreducible decomposition, this algorithm may not terminate for a polynomial of large degree (e.g. degree >= 5).
    SeeAlso
        bivariateDiagEntries
///

doc ///
    Key
        bivariateSystem
        (bivariateSystem, RingElement)
        [bivariateSystem, Tolerance]
        [bivariateSystem, Software]
    Headline
        computes a determinantal representation of a bivariate polynomial numerically
    Usage
        bivariateSystem f
        bivariateSystem(f, Tolerance => 1e-6)
    Inputs
        f:RingElement
            a bivariate polynomial with real coefficients
    Outputs
        :List
            of orthogonal matrices corresponding to determinantal representations of $f$
    Description
        Text
            This method implements a brute-force algorithm to find a monic symmetric determinantal representation of a real cubic bivariate polynomial $f$. For a symmetric determinantal representation $f = det(I + x_1A_1 + x_2A_2)$, by suitable conjugation one may assume $A_1 = D_1$ is a diagonal matrix. Since $D_1$ and the diagonal entries of $A_2$ can be found using the method @TO bivariateDiagEntries@, to find a symmetric determinantal representation of $f$ it suffices to compute the off-diagonal entries of $A_2$. These off-diagonal entries of $A_2$ are solutions to a $(d choose 2)\times (d choose 2)$ polynomial system, for a determinantal representation of size $d$. This method computes solutions to this system via numerical algebraic geometry.
            
            The option {\tt Tolerance} can be used to specify the internal threshold for checking equality (any floating point number below the tolerance is treated as numerically zero). The option @TO Software@ specifies the numerical algebraic geometry software used to perform a numerical irreducible decomposition: by default, the native M2engine is used, although other valid options include BERTINI and PHCPACK (if the user has these installed on their system).
        
        Example
            R = RR[x1, x2]
            f=6*x1^3+36*x1^2*x2+11*x1^2+66*x1*x2^2+42*x1*x2+6*x1+36*x2^3+36*x2^2+11*x2+1
            bivariateSystem f
    Caveat
        As this algorithm implements a relatively naive algorithm, it may not terminate for a polynomial of large degree (e.g. degree >= 5).
    SeeAlso
        bivariateDiagEntries
        bivariateOrthogonal
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
            This method computes the generalized mixed discriminant of an $n$-tuple of $n\times n$ matrices.
                 
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
///

doc ///
    Key
        isDoublystochastic
        (isDoublystochastic, Matrix)
        [isDoublystochastic, Tolerance]
    Headline
        whether a matrix is doubly stochastic
    Usage
        isDoublystochastic A
    Inputs
        A:Matrix
    Outputs
        :Boolean
            whether $A$ is a doubly stochastic matrix
    Description
        Text
            This method determines whether a given matrix is doubly stochastic, i.e. is a real square matrix with all entries nonnegative and all row and column sums equal to $1$. 
            
            The option {\tt Tolerance} can be used to specify the internal threshold for checking equality (any floating point number below the tolerance is treated as numerically zero).
                 
        Example
            R = RR[x1, x2]
            f=6*x1^3+36*x1^2*x2+11*x1^2+66*x1*x2^2+42*x1*x2+6*x1+36*x2^3+36*x2^2+11*x2+1
            L = cubicBivariateOrthostochastic f
            isDoublystochastic L#0
            A = randomOrthostochastic 3
            isDoublystochastic A
///

doc ///
    Key
        isOrthogonal
        (isOrthogonal, Matrix)
        [isOrthogonal, Tolerance]
    Headline
        whether a matrix is orthogonal
    Usage
        isOrthogonal A
    Inputs
        A:Matrix
    Outputs
        :Boolean
            whether $A$ is orthogonal
    Description
        Text
            This method determines whether a given matrix is orthogonal, i.e. has inverse equal to its transpose. 
            
            The option {\tt Tolerance} can be used to specify the internal threshold for checking equality (any floating point number below the tolerance is treated as numerically zero). If the given matrix does not have floating point entries, then this option is not used.
                 
        Example
            R = RR[x1, x2]
            f=6*x1^3+36*x1^2*x2+11*x1^2+66*x1*x2^2+42*x1*x2+6*x1+36*x2^3+36*x2^2+11*x2+1
            O = first orthogonalFromOrthostochastic first cubicBivariateOrthostochastic f
            isOrthogonal O
///

doc ///
    Key
        randomOrthostochastic
        (randomOrthostochastic, ZZ)
        [randomOrthostochastic, Tolerance]
    Headline
        constructs a random orthostochastic matrix
    Usage
        randomOrthostochastic n
        randomOrthostochastic(n, Tolerance => 1e-6)
    Inputs
        n:ZZ
    Outputs
        :Matrix
            a random $n\times n$ orthostochastic matrix
    Description
        Text
            This method returns a random orthostochastic matrix of a given size $n$. A real square matrix $A$ is said to be orthostochastic if there is an orthogonal matrix $V$ whose Hadamard square is $A$. Note that an orthostochastic matrix is necessarily @TO2{isDoublystochastic, "doubly stochastic"}@.
            
            The option {\tt Tolerance} can be used to specify the internal threshold for checking equality (any floating point number below the tolerance is treated as numerically zero).
            
        Example
            A3 = randomOrthostochastic 3
            isDoublystochastic A3
            time A10 = randomOrthostochastic(10, Tolerance => 1e-8)
            isDoublystochastic A10
///

doc ///
    Key
        randomIntegerSymmetric
        (randomIntegerSymmetric, ZZ)
        (randomIntegerSymmetric, ZZ, Ring)
    Headline
        constructs a random integer symmetric matrix
    Usage
        randomIntegerSymmetric n
        randomIntegerSymmetric(n, R)
    Inputs
        n:ZZ
        R:Ring
    Outputs
        :Matrix
            a random $n\times n$ symmetric matrix with integer entries
    Description
        Text
            This method returns a random symmetric matrix of a given size $n$ with integer entries. This can in turn be specialized to any ring, which may be provided as an argument. 
                 
        Example
            randomIntegerSymmetric 5
            randomIntegerSymmetric 20
            R = RR[x,y]
            randomIntegerSymmetric(3, R)
    Caveat
        The entries of the constructed matrix will be integers between 0 and 18, inclusive.
///

doc ///
    Key
        hadamard
        (hadamard, Matrix, Matrix)
    Headline
        computes the Hadamard product of two matrices
    Usage
        hadamard(A, B)
    Inputs
        A:
            an $m\times n$ matrix
        B:
            an $m\times n$ matrix
    Outputs
        :Matrix
            the Hadamard product of $A$ and $B$
    Description
        Text
            This method computes the Hadamard product of two matrices $A, B$ of the same size. The Hadamard product is defined as the componentwise product, i.e. if $A, B$ are $m\times n$ matrices, then the Hadamard product is the $m\times n$ matrix with $(i,j)$ entry equal to $A_{i,j}*B_{i,j}$.
                 
        Example
            A = randomOrthostochastic 3
            O = first orthogonalFromOrthostochastic A
            clean(1e-10, hadamard(O, O) - A)
///

doc ///
    Key
        liftRealMatrix
        (liftRealMatrix, Matrix)
    Headline
        lifts matrix over CC to matrix over RR
    Usage
        liftRealMatrix A
    Inputs
        A:Matrix
            with complex entries
    Outputs
        :Matrix
            the real matrix whose entries are real parts of entries of A
    Description
        Text
            This method converts a complex matrix a real matrix, by taking the real part of each entry. 
                 
        Example
            A = random(RR^3,RR^5)
            B = sub(A, CC)
            C = liftRealMatrix B
            clean(1e-10, A - C) == 0
///

doc ///
    Key
        roundMatrix
        (roundMatrix, ZZ, Matrix)
    Headline
        lifts matrix over RR to matrix over QQ
    Usage
        roundMatrix(n, A)
    Inputs
        A:Matrix
            with real entries
        n:ZZ
            a threshold for rounding digits
    Outputs
        :Matrix
            a matrix over QQ, obtained by rounding entries of A
    Description
        Text
            This method converts a real matrix to a rational matrix, by rounding each entry. The input $n$ specifies the number of (decimal) digits used for rounding.
                 
        Example
            A = matrix{{1, 2.5, -13/17}, {1*pi, 4.7, sqrt(2)}}
            roundMatrix(5, A)
///


-----------------------------

-- TESTS

TEST /// -- Quadratic case tests
R = RR[x1,x2,x3]
f = 1 - 8*x1*x2 - 4*x1*x3 - 100*x2^2 - 12*x2*x3 - x3^2 - 5*x1^2
coeffMatrices = quadraticDetRep f
assert(0 == clean(1e-10, f - det(id_(R^2) + sum apply(#gens R, i -> coeffMatrices#i*R_i))))
///

TEST /// -- cubic case tests
R=QQ[x1,x2]
f=6*x1^3+36*x1^2*x2+11*x1^2+66*x1*x2^2+42*x1*x2+6*x1+36*x2^3+36*x2^2+11*x2+1
orthostochasticMatrices = cubicBivariateOrthostochastic f
O1 = orthogonalFromOrthostochastic last orthostochasticMatrices
M = matrix{{0.5322,0.3711,0.0967},{0.4356,0.2578,0.3066},{0.0322,0.3711,0.5967}}
assert(orthogonalFromOrthostochastic M === {})
assert(clean(1e-4, first(O1 - orthogonalFromOrthostochastic(M, Tolerance => 1e-4))) == 0)
///

TEST /// -- Generalized mixed discriminant - bivariate case
n = 4
R = QQ[a_(1,1)..a_(n,n),b_(1,1)..b_(n,n)][x_1,x_2]
A = sub(transpose genericMatrix(coefficientRing R,n,n), R)
B = sub(transpose genericMatrix(coefficientRing R,b_(1,1),n,n), R)
P = det(id_(R^n) + x_1*A + x_2*B);
assert((last coefficients(P, Monomials => {x_1*x_2}))_(0,0) == generalizedMixedDiscriminant({A,B}))
assert((last coefficients(P, Monomials => {x_1^3*x_2}))_(0,0) == generalizedMixedDiscriminant({A,A,A,B}))
///

TEST /// -- Generalized mixed discriminant - trivariate case
n = 3
R = QQ[a_(1,1)..a_(n,n),b_(1,1)..b_(n,n),c_(1,1)..c_(n,n)][x_1..x_n]
A = sub(transpose genericMatrix(coefficientRing R,n,n), R)
B = sub(transpose genericMatrix(coefficientRing R,b_(1,1),n,n), R)
C = sub(transpose genericMatrix(coefficientRing R,c_(1,1),n,n), R)
P = det(id_(R^n) + x_1*A + x_2*B + x_3*C);
assert((last coefficients(P, Monomials => {x_1*x_2*x_3}))_(0,0) == generalizedMixedDiscriminant({A,B,C}))
///

end--
restart
loadPackage("DeterminantalRepresentations", Reload => true)
uninstallPackage "DeterminantalRepresentations"
installPackage "DeterminantalRepresentations"
installPackage("DeterminantalRepresentations", RemakeAllDocumentation => true)
viewHelp "DeterminantalRepresentations"
check "DeterminantalRepresentations"


-- Degenerate cubic (fix!)
R = QQ[x1,x2]
f = 162*x1^3 - 23*x1^2*x2 + 99*x1^2 - 8*x1*x2^2 - 10*x1*x2 + 18*x1 + x2^3 - x2^2 - x2 + 1
cubicBivariateOrthostochastic f

-- Quartic examples
R = QQ[x1,x2]
f=(1/2)*(x1^4+x2^4-3*x1^2-3*x2^2+x1^2*x2^2)+1
time matrixList = bivariateOrthogonal(f, Software => BERTINI) -- SLOW!

f = 24*x1^4+(49680/289)*x1^3*x2+50*x1^3+(123518/289)*x1^2*x2^2+(72507/289)*x1^2*x2+35*x1^2+(124740/289)*x1*x2^3+(112402/289)*x1*x2^2+(32022/289)*x1*x2+10*x1+144*x2^4+180*x2^3+80*x2^2+15*x2+1
bivariateSystem f

-- Higher degree bivariate
n = 5
R = RR[x,y]
f = det(id_(R^n) + x*sub(diagonalMatrix toList(1..n),R) + y*randomIntegerSymmetric(n, R))
