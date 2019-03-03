newPackage("DeterminantalRepresentations",
	AuxiliaryFiles => false,
	Version => "0.0.5",
	Date => "March 3, 2019",
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
    "cubicBivariateDetRep",
    "bivariateDetRep",
    "bivariateDiagEntries",
    "orthogonalFromOrthostochastic",
    "generalizedMixedDiscriminant",
    "roundMatrix",
    "liftRealMatrix",
    "hadamard",
    "isOrthogonal",
    "isDoublystochastic",
    "randomIntegerSymmetric",
    "randomOrthogonal"
}

-- Quadratic case

quadraticDetRep = method(Options => {Tolerance => 1e-6})
quadraticDetRep RingElement := List => opts -> f -> ( -- returns a list of matrices over original ring R
    R := ring f;
    n := #gens R;
    k := ultimate(coefficientRing, R);
    b := sub(last coefficients(f, Monomials => gens R), k);
    A := sub(matrix table(n, n, (i,j) -> if i == j then (last coefficients(f, Monomials => {R_i^2}))_(0,0) else (1/2)*(last coefficients(f, Monomials => {R_i*R_j}))_(0,0)), k);
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
    if not class k === ComplexField then L = L/liftRealMatrix/clean_(opts.Tolerance);
    if k === QQ then L = L/roundMatrix_(ceiling(log_10(1/opts.Tolerance)));
    apply(L, M -> sub(M, R))
)

-- Cubic bivariate case

cubicBivariateDetRep = method(Options => options quadraticDetRep)
cubicBivariateDetRep RingElement := List => opts -> f -> (
    (D1, D2, diag1, diag2) := bivariateDiagEntries(f, opts)/entries/flatten;
    S := RR(monoid[getSymbol "q12"]);
    q11 := (diag2#0-D2#2-S_0*(D2#1-D2#2))/(D2#0-D2#2);
    q21 := (-(D1#0-D1#2)*(diag2#0-D2#2-S_0*(D2#1-D2#2))+(D2#0-D2#2)*(diag1#0-D1#2))/((D1#1-D1#2)*(D2#0-D2#2));
    q22 := (diag1#1-D1#2-S_0*(D1#0-D1#2))/(D1#1-D1#2);
    Q := matrix{{q11,S_0,1-S_0-q11},{q21,q22,1-q21-q22},{1-q11-q21,1-S_0-q22,1-(1-S_0-q11)-(1-q21-q22)}};
    L0 := apply(roots((1-q11-q22-S_0-q21+q11*q22+S_0*q21)^2-4*q11*q22*S_0*q21), r -> liftRealMatrix sub(Q,S_0=>r));
    L := flatten apply(select(L0, isDoublystochastic), M -> orthogonalFromOrthostochastic(M, opts));
    if ultimate(coefficientRing, ring f) === QQ then (
        numDigits := ceiling(-log_10(opts.Tolerance));
        (D1, D2) = (D1/round_numDigits, D2/round_numDigits);
        L = L/roundMatrix_numDigits;
    );
    (D1, D2) = (D1, D2)/diagonalMatrix/(A -> sub(A, ring f));
    L = L/(A -> sub(A, ring f));
    apply(L, M -> {D1, M*D2*transpose M})
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

bivariateDetRep = method(Options => {Tolerance => 1e-6, Software => M2engine, Strategy => "DirectSystem"})
bivariateDetRep RingElement := List => opts -> f -> (
    (D1, D2, diag1, diag2) := bivariateDiagEntries(f, Tolerance => opts.Tolerance);
    R := ring f;
    d := first degree f;
    y := getSymbol "y";
    if opts.Strategy == "DirectSystem" then ( -- via solving polynomial system numerically
        D := flatten entries D1;
        S := R/(ideal gens R)^(d+1);
        mons := lift(super basis(ideal(S_1^2)), R);
        C := last coefficients(f, Monomials => mons);
        T := RR(monoid[y_1..y_(binomial(d,2))]);
        S = T(monoid[gens R]);
        A := genericSkewMatrix(T, d);
        B := matrix table(d, d, (i,j) -> if i == j then diag2_(i,0) else A_(min(i,j),max(i,j)));
        G := det(id_(S^d) + S_0*sub(diagonalMatrix D, S) + S_1*sub(B, S));
        C1 := last coefficients(G, Monomials => sub(mons, S)) - sub(C, S);
        P := polySystem sub(clean(opts.Tolerance, C1), T);
        print ("Solving " | binomial(d,2) | " x " | binomial(d,2) | " polynomial system...");
        elapsedTime sols := select(solveSystem(P, Software => opts.Software), p -> not status p === RefinementFailure);
        realPoints apply(sols, p -> point{p#Coordinates/clean_(opts.Tolerance)})
    ) else if opts.Strategy == "Orthogonal" then ( -- via orthogonal matrices
        T = RR(monoid[y_0..y_(d^2-1)]);
        A = genericMatrix(T,d,d);
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
)

-- Helper functions for bivariate case

bivariateDiagEntries = method(Options => options quadraticDetRep)
bivariateDiagEntries RingElement := Sequence => opts -> f -> ( -- returns diagonal entries and eigenvalues of coefficient matrices
    R := ring f;
    d := first degree f;
    (R1, R2) := ((coefficientRing R)(monoid[R_0]), (coefficientRing R)(monoid[R_1]));
    (f1, f2) := (sub(sub(f, R_1 => 0), R1), sub(sub(f, R_0 => 0), R2));
    (r1, r2) := (f1, f2)/roots;
    D1 := reverse sort(apply(r1,r -> -1/r) | toList(d-#r1:0));
    D2 := reverse sort(apply(r2,r -> -1/r) | toList(d-#r2:0));
    if not all(D1 | D2, r -> clean(opts.Tolerance, imaginaryPart r) == 0) then error("Not a real zero polynomial - no determinantal representation of size " | d);
    (D1, D2) = (D1/realPart, D2/realPart);
    C1 := last coefficients(f, Monomials => apply(d, i -> R_{1,i}));
    G1 := sub(matrix table(d,d,(i,j) -> sum apply(subsets(toList(0..<d)-set{j},i), s -> product(D2_s))), RR);
    diag1 := addScaleToMajorize(flatten entries solve(G1, sub(C1,RR)), D1, gens ker G1, opts);
    C2 := last coefficients(f, Monomials => apply(d, i -> R_{i,1}));
    G2 := sub(matrix table(d,d,(i,j) -> sum apply(subsets(toList(0..<d)-set{j},i), s -> product(D1_s))), RR);
    diag2 := addScaleToMajorize(flatten entries solve(G2, sub(C2,RR)), D2, gens ker G2, opts);
    (D1, D2, diag1, diag2)/(L -> transpose matrix{L})
)

addScaleToMajorize = method(Options => options quadraticDetRep)
addScaleToMajorize (List, List, Matrix) := List => opts -> (v, w, K) -> (
    if isMajorized(v, w, opts) then return v;
    if clean(opts.Tolerance, K) == 0 then error (toString(w) | " cannot be majorized by " | toString(v));
    (w, K) = (rsort w, flatten entries K);
    ineqs := apply(select(subsets(#K), s -> clean(opts.Tolerance, sum K_s) != 0), s -> (K_s, w_(toList(0..<#s)) - v_s)/sum);
    tmax := min apply(select(ineqs, p -> p#0 > 0), p -> p#1/p#0);
    tmin := max apply(select(ineqs, p -> p#0 < 0), p -> p#1/p#0);
    if tmin > tmax then error (toString(w) | " cannot be majorized by " | toString(v));
    t1 := 0.5*(tmax + tmin);
    t0 := if tmax - tmin >= 1 then ( if floor t1 >= tmin then floor t1 else ceiling t1 ) else t1;
    v + t0*K
)

isMajorized = method(Options => options quadraticDetRep)
isMajorized (List, List) := Boolean => opts -> (v, w) -> (
    (v,w) = (v,w)/rsort;
    if not clean(opts.Tolerance, sum v - sum w) == 0 then return false;
    all(#v, k -> clean(opts.Tolerance, sum(w_{0..k}) - sum(v_{0..k})) >= 0)
)

getDescendingSort = method()
getDescendingSort List := List => L -> (
    H := hashTable (identity, apply(#L, i -> L#i => i)); 
    splice apply(rsort keys H, k -> H#k)
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

randomOrthogonal = method()
randomOrthogonal (ZZ, Thing) := Matrix => (n, R) -> (
    k := if instance(R, InexactFieldFamily) then R else ultimate(coefficientRing, R);
    A := random(k^n, k^n);
    S := A - transpose A;
    sub((-1)*inverse(S - id_(k^n))*(S + id_(k^n)), R)
)
randomOrthogonal ZZ := Matrix => n -> randomOrthogonal(n, RR)

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
	    The goal of this package is to compute determinantal representations of
            polynomials. To be precise, a polynomial $f$ in $\mathbb{R}[x_1, \ldots, x_n]$ 
            of total degree $d$ (not necessarily homogeneous) is called determinantal if $f$
            is the determinant of a matrix of linear forms - in other words, there exist
            matrices $A_0, \ldots, A_n \in \mathbb{R}^{d\times d}$ such that 
            $f(x_1, \ldots, x_n) = det(A_0 + x_1A_1 + \ldots + x_nA_n)$. The matrices 
            $A_0, \ldots, A_n$ are said to give a determinantal representation of $f$ of size
            $d$. If the matrices $A_i$ can be chosen to be all symmetric, then the
            determinantal representation is called symmetric. The determinantal
            representation is called definite if $A_0$ is positive definite, and monic if 
            $A_0 = I_d$ is the identity matrix. 
            
            Detecting whether or not a degree $d$ polynomial has a determinantal
            representation of size $d$ is difficult, and computing such a representation 
            even more so. Computing (monic) symmetric determinantal representations 
            of bivariate polynomials is of interest owing to a connection with real-zero and
            hyperbolic polynomials, due to a celebrated theorem of Helton-Vinnikov. In
            general, determinantal polynomials also have connections to convex algebraic
            geometry and semidefinite programming.
            
            Currently, the functions in this package are geared towards computing monic
            symmetric determinantal representations of quadrics, as well as bivariate cubics
            and quartics. The algorithms implemented in this package can be found in 
            [Dey1], [Dey2].
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
            This method computes a monic symmetric determinantal representation of a 
            real quadric $f$, or returns false if no such representation exists.
            
            The option {\tt Tolerance} can be used to specify the internal threshold for
            checking equality (any floating point number below the tolerance is treated as
            numerically zero).
        
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
            This method computes the eigenvalues and diagonal entries of a monic
            symmetric determinantal representation of a real bivariate polynomial $f$, or
            returns false if certain necessary conditions for existence of such a 
            representation are not met. For a symmetric determinantal representation 
            $f = det(I + x_1A_1 + x_2A_2)$, this method computes diagonal entries and
            eigenvalues of $A_1$ and $A_2$. The output is a 4-tuple of column vectors: 
            (eigenvalues of A_1, eigenvalues of $A_2$, diagonal entries of $A_1$,
            diagonal entries of $A_2$).
            
            The option {\tt Tolerance} can be used to specify the internal threshold for
            checking equality (any floating point number below the tolerance is treated as
            numerically zero).
        
        Example
            R = RR[x1, x2]
            f = 15*x1^2 + 20*x1*x2 - 36*x2^2 + 20*x1 + 16*x2 + 1
            bivariateDiagEntries f
    SeeAlso
        bivariateDetRep
        cubicBivariateDetRep
///

doc ///
    Key
        bivariateDetRep
        (bivariateDetRep, RingElement)
        [bivariateDetRep, Tolerance]
        [bivariateDetRep, Software]
        [bivariateDetRep, Strategy]
    Headline
        computes determinantal representations of a bivariate polynomial numerically
    Usage
        bivariateDetRep f
        bivariateDetRep(f, Tolerance => 1e-6)
        bivariateDetRep(f, Strategy => "DirectSystem")
    Inputs
        f:RingElement
            a bivariate polynomial with real coefficients
    Outputs
        :List
            of lists of matrices, each giving a determinantal representation of $f$
    Description
        Text
            This method implements two strategies to compute a determinantal 
            representation of a bivariate polynomial numerically. For a
            symmetric determinantal representation $f = det(I + x_1A_1 + x_2A_2)$, by
            suitable conjugation one may assume $A_1 = D_1$ is a diagonal matrix. We
            also have that $D_1$ and the diagonal entries of $A_2$ can be found using 
            the method @TO bivariateDiagEntries@.
            
            The first (and default) strategy is "DirectSystem", which computes the 
            off-diagonal entries of $A_2$ directly as solutions to a 
            $(d choose 2)\times (d choose 2)$ polynomial system.
            
            The second strategy is "Orthogonal", which computes the orthogonal 
            change-of-basis matrices $V$ such that $VA_2V^T = D_2$ is diagonal. 
            Since $D_2$ can be found using @TO bivariateDiagEntries@, $A_2$ can 
            be recovered from $V$.
            
            Both strategies use numerical algebraic geometry, specifically a 
            @TO numericalIrreducibleDecomposition@.
            
            The option {\tt Tolerance} can be used to specify the internal threshold for
            checking equality (any floating point number below the tolerance is treated as
            numerically zero). The option @TO Software@ specifies the numerical algebraic
            geometry software used to perform a numerical irreducible decomposition: by
            default, the native M2engine is used, although other valid options include
            BERTINI and PHCPACK (if the user has these installed on their system).
        
        Example
            R = RR[x1, x2]
            f=(1/2)*(x1^4+x2^4-3*x1^2-3*x2^2+x1^2*x2^2)+1
            bivariateDetRep f
    Caveat
        As this algorithm implements relatively brute-force algorithms, it may not 
        terminate for polynomials of large degree (e.g. degree >= 5).
    SeeAlso
        bivariateDiagEntries
///

doc ///
    Key
        cubicBivariateDetRep
        (cubicBivariateDetRep, RingElement)
        [cubicBivariateDetRep, Tolerance]
    Headline
        computes determinantal representations of a bivariate cubic
    Usage
        cubicBivariateDetRep f
        cubicBivariateDetRep(f, Tolerance => 1e-6)
    Inputs
        f:RingElement
            a cubic bivariate polynomial with real coefficients
    Outputs
        :List
            of lists of matrices, each giving a determinantal representation of $f$
    Description
        Text
            This method computes monic symmetric determinantal representations of a 
            real bivariate cubic $f$, or returns false if certain necessary conditions for
            existence of such a representation are not met. For a symmetric
            determinantal representation $f = det(I + x_1A_1 + x_2A_2)$, by suitable
            conjugation one may assume $A_1 = D_1$ is a diagonal matrix. Since $A_2$ is
            symmetric, by the spectral theorem there exist an orthogonal change-of-basis
            matrix $V$ such that $VA_2V^T = D_2$ is diagonal. Since $D_1, D_2$ can be
            found using the method @TO bivariateDiagEntries@, to find a symmetric
            determinantal representation of $f$ it suffices to compute the possible 
            orthogonal matrices $V$. This method computes the orthostochastic matrices 
            which are the Hadamard squares of $V$, via the algorithm in [Dey1], and 
            returns the associated determinantal representation (using the method 
            @TO orthogonalFromOrthostochastic@ - see that method for more on the
            possible orthogonal matrices returned).
            
            The option {\tt Tolerance} can be used to specify the internal threshold for
            checking equality (any floating point number below the tolerance is treated as
            numerically zero).
        
        Example
            R = RR[x1, x2]
            f=6*x1^3+36*x1^2*x2+11*x1^2+66*x1*x2^2+42*x1*x2+6*x1+36*x2^3+36*x2^2+11*x2+1
            repList = cubicBivariateDetRep f
            all(repList, A -> clean(1e-10, f - det(id_(R^3) + sum(#gens R, i -> R_i*A#i))) == 0)
    SeeAlso
        bivariateDiagEntries
        orthogonalFromOrthostochastic
        bivariateDetRep
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
        orthogonalFromOrthostochastic(A, Tolerance => 1e-6)
    Inputs
        A:Matrix
            an orthostochastic matrix
    Outputs
        :List
            of orthogonal matrices whose Hadamard square is $A$
    Description
        Text
            This method computes orthogonal matrices whose Hadamard square is a 
            given orthostochastic matrix. This is a helper function to 
            @TO cubicBivariateDetRep@, which computes symmetric
            determinantal representations of real cubic bivariate polynomials. 
            
            Given a $n\times n$ orthostochastic matrix $A$, there are $2^{n^2}$ possible
            matrices whose Hadamard square is $A$ (not all of which will be orthogonal in
            general though). Let $G\cong (\ZZ/2\ZZ)^n$ be the group of diagonal matrices 
            with diagonal entries equal to &plusmn;1. One can act (on the left and right) by 
            $G\times G$ on the set of orthogonal matrices whose Hadamard square is $A$.
            This method computes all such orthogonal matrices, modulo the action of 
            $G\times G$. The representative for each orbit is chosen so that the first row 
            and column will have nonnegative entries. Note that for generic choices of the
            orthostochastic matrix $A$, there will be exactly one $G\times G$-orbit of 
            orthogonal matrices with Hadamard square equal to $A$.
            
            The option {\tt Tolerance} can be used to specify the internal threshold for
            checking equality (any floating point number below the tolerance is treated as
            numerically zero).
        
        Example
            O = randomOrthogonal 4
            A = hadamard(O, O)
            orthogonalFromOrthostochastic A
    SeeAlso
        cubicBivariateDetRep
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
            This method computes the generalized mixed discriminant of an $n$-tuple 
            of $n\times n$ matrices.
                 
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
            This method determines whether a given matrix is doubly stochastic, i.e. is 
            a real square matrix with all entries nonnegative and all row and column sums
            equal to $1$. 
            
            The option {\tt Tolerance} can be used to specify the internal threshold for
            checking equality (any floating point number below the tolerance is treated as
            numerically zero).
                 
        Example
            O = randomOrthogonal 3
            A = hadamard(O, O)
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
            This method determines whether a given matrix is orthogonal, i.e. has 
            inverse equal to its transpose. 
            
            The option {\tt Tolerance} can be used to specify the internal threshold for
            checking equality (any floating point number below the tolerance is treated as
            numerically zero). If the given matrix does not have floating point entries, then
            this option is not used.
                 
        Example
            O1 = randomOrthogonal 5
            isOrthogonal O1
            O2 = randomOrthogonal(5, QQ)
            isOrthogonal O2
    SeeAlso
        randomOrthogonal
///

doc ///
    Key
        randomOrthogonal
        (randomOrthogonal, ZZ)
        (randomOrthogonal, ZZ, Thing)
    Headline
        constructs a random special orthogonal matrix
    Usage
        randomOrthogonal n
        randomOrthogonal(n, R)
    Inputs
        n:ZZ
        R:
            a @TO Ring@, or @TO RR@ or @TO CC@ (of type @TO InexactFieldFamily@)
    Outputs
        :Matrix
            a random $n\times n$ special orthogonal matrix, over the ring $R$
    Description
        Text
            This method returns a random orthogonal matrix of a given size $n$.
            The orthogonal matrix is constructed via Cayley's correspondence,
            which gives a bijection between skew-symmetric matrices, and 
            orthogonal matrices $O$ which do not have $1$ as an eigenvalue
            (i.e. $O - I$ is invertible). Up to changing signs of rows, any orthogonal 
            matrix can be obtained this way: if $G\cong (\ZZ/2\ZZ)^n$ 
            is the group of diagonal matrices with diagonal entries equal to 
            &plusmn;1, acting on $n\times n$ matrices by left multiplication, then 
            (as one may check) every $G$-orbit contains a matrix 
            that does not have $1$ as an eigenvalue (if the characteristic is not 2).
            
            Note that the matrices which feature in the Cayley correspondence have
            determinant $(-1)^n$, so this method scales by $-1$ to return a special
            orthogonal matrix. Thus the matrices returned by this method do not have 
            $-1$ as an eigenvalue.
            
            By default a matrix over @TO RR@ is returned. This method also accepts
            a ring as an (optional) argument, in which case a special orthogonal matrix
            over the ring is returned, with entries in the 
            @TO2{coefficientRing, "base field"}@.
            
        Example
            O1 = randomOrthogonal 5
            isOrthogonal O1
            eigenvalues O1
            det O1
            R = QQ[x,y]
            O2 = randomOrthogonal(5, R)
            isOrthogonal O2
            det(O2), det(O2+id_(R^5))
    SeeAlso
        isOrthogonal
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
            a random $n\times n$ symmetric matrix with integer entries, over the ring $R$
    Description
        Text
            This method returns a random symmetric matrix of a given size $n$ with 
            integer entries. This can in turn be specialized to any ring, which may be
            provided as an argument. 
                 
        Example
            randomIntegerSymmetric 5
            randomIntegerSymmetric 20
            R = RR[x,y]
            randomIntegerSymmetric(3, R)
    Caveat
        The entries of the constructed matrix will be integers between 0 and 18, inclusive.
    SeeAlso
        genericSymmetricMatrix
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
            This method computes the Hadamard product of two matrices $A, B$ of the
            same size. The Hadamard product is defined as the componentwise product, 
            i.e. if $A, B$ are $m\times n$ matrices, then the Hadamard product is the 
            $m\times n$ matrix with $(i,j)$ entry equal to $A_{i,j}*B_{i,j}$.
                 
        Example
            (A1, A2) = (random(ZZ^2, ZZ^3), random(ZZ^2, ZZ^3))
            hadamard(A1, A2)
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
            This method converts a complex matrix to a real matrix, by taking the real 
            part of each entry. 
                 
        Example
            A = random(RR^3,RR^5)
            B = sub(A, CC)
            C = liftRealMatrix B
            clean(1e-10, A - C) == 0
    SeeAlso
        roundMatrix
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
            This method converts a real matrix to a rational matrix, by rounding each 
            entry. The input $n$ specifies the number of (decimal) digits used for rounding.
                 
        Example
            A = matrix{{1, 2.5, -13/17}, {1*pi, 4.7, sqrt(2)}}
            roundMatrix(5, A)
    SeeAlso
        liftRealMatrix
///


-----------------------------

-- TESTS

TEST /// -- Quadratic case tests
S = QQ[x1,x2,x3]
f = 1 - 8*x1*x2 - 4*x1*x3 - 100*x2^2 - 12*x2*x3 - x3^2 - 5*x1^2
coeffMatrices = quadraticDetRep(f, Tolerance => 1e-10)
assert(0 == clean(1e-9, sub(f - det(id_(S^2) + sum apply(#gens S, i -> coeffMatrices#i*S_i)), RR(monoid[gens S]))))
SRR = RR[x1,x2,x3]
fRR = sub(f, SRR)
coeffMatrices = quadraticDetRep fRR
assert(0 == clean(1e-10, fRR - det(id_(SRR^2) + sum apply(#gens SRR, i -> coeffMatrices#i*SRR_i))))
SCC = CC[x1,x2,x3]
fCC = sub(f, SCC)
coeffMatrices = quadraticDetRep fCC
assert(0 == clean(1e-10, fCC - det(id_(SCC^2) + sum apply(#gens SCC, i -> coeffMatrices#i*SCC_i))))
///

TEST /// -- cubic case tests
S=QQ[x1,x2]
f=6*x1^3+36*x1^2*x2+11*x1^2+66*x1*x2^2+42*x1*x2+6*x1+36*x2^3+36*x2^2+11*x2+1
detrep = cubicBivariateDetRep(f, Tolerance => 1e-12)
assert(all(detrep, L -> clean(1e-10, sub(f - det(id_(S^3) + S_0*L#0 + S_1*L#1), RR(monoid[gens S]))) == 0))
SRR=RR[x1,x2]
fRR=sub(f, SRR)
detrep = cubicBivariateDetRep fRR
assert(all(detrep, L -> clean(1e-10, fRR - det(id_(SRR^3) + SRR_0*L#0 + SRR_1*L#1)) == 0))
orthostochasticMatrices = cubicBivariateOrthostochastic f
O1 = orthogonalFromOrthostochastic last orthostochasticMatrices
M = matrix{{0.5322,0.3711,0.0967},{0.4356,0.2578,0.3066},{0.0322,0.3711,0.5967}}
assert(orthogonalFromOrthostochastic M === {})
assert(clean(1e-4, first(O1 - orthogonalFromOrthostochastic(M, Tolerance => 1e-4))) == 0)
///

TEST /// -- Quartic case tests
R=QQ[x1,x2]
eps = 1e-10
n = 4
A = randomIntegerSymmetric(n, R)
f = det(id_(R^n) + R_0*diagonalMatrix {4,3,2,1_R} + R_1*A)
(D1, D2, diag1, diag2) = bivariateDiagEntries f
sols = apply(bivariateSystem f, p -> p#Coordinates/realPart)
integerSols = select(sols, p -> all(p, c -> clean(eps, c - round(6, c)) ==  0))
sol1 = first select(integerSols, p -> all(n-1, i -> p#i >= 0)) /round_6
upperIndices = select((0,0)..(n-1,n-1), s -> s#0 < s#1);
H = hashTable apply(#sol1, i -> upperIndices#i => sol1#i);
B = roundMatrix(6, matrix table(n, n, (i,j) -> if i == j then diag2_(i,0) else H#(min(i,j), max(i,j))))
assert(A - B == 0) -- note: assert(A == B) fails!
assert(f == det(id_(R^n) + R_0*sub(roundMatrix(6, diagonalMatrix D1), R) + R_1*sub(B, R)))
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

TEST /// -- isOrthogonal, isDoublystochastic tests
assert(isOrthogonal id_(ZZ^5))
assert(isOrthogonal id_(QQ^5))
assert(isOrthogonal id_((CC[x,y])^5))
R = RR[x,y]
I = id_(R^5)
assert(isOrthogonal I and isDoublystochastic I)
assert(clean(1e-10, hadamard(I, I) - I) == 0)
O1 = randomOrthogonal 5
A = hadamard(O1, O1)
O = first orthogonalFromOrthostochastic A
assert(isOrthogonal O and isDoublystochastic A and clean(1e-10, hadamard(O, O) - A) == 0)
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

----------------------------------------------------
-- Old code

doc ///
    Key
        randomOrthostochastic
        (randomOrthostochastic, ZZ)
        (randomOrthostochastic, ZZ, Thing)
    Headline
        constructs a random orthostochastic matrix
    Usage
        randomOrthostochastic n
        randomOrthostochastic(n, R)
    Inputs
        n:ZZ
        R:
            a @TO Ring@, or @TO RR@ or @TO CC@ (of type @TO InexactFieldFamily@)
    Outputs
        :Matrix
            a random $n\times n$ orthostochastic matrix, over the ring $R$
    Description
        Text
            This method returns a random orthostochastic matrix of a given size $n$. 
            A real square matrix $A$ is said to be orthostochastic if there is an orthogonal
            matrix $V$ whose Hadamard square is $A$. Note that an orthostochastic matrix
            is necessarily @TO2{isDoublystochastic, "doubly stochastic"}@. This method 
            is a combination of the methods @TO randomOrthogonal@ and 
            @TO hadamard@.
            
            By default a matrix over @TO RR@ is returned. This method also accepts
            a ring as an (optional) argument, in which case an orthostochastic  matrix
            over the ring is returned, with entries in the 
            @TO2{coefficientRing, "base field"}@.
            
        Example
            A3 = randomOrthostochastic 3
            isDoublystochastic A3
            time A10 = randomOrthostochastic 10
            isDoublystochastic(A10, Tolerance => 1e-8)
    SeeAlso
        randomOrthogonal
        hadamard
///

----------------------------------------------------

clearAll

tOperator = method()
tOperator (RingElement, RingElement) := RingElement => (f, l) -> (
    R := ring f;
    f+(1-last gens coefficientRing R)*l*diff(R_0,f)
)

(n,d) = (2,3)
e = max(d,n)
k = CC
C = k[a_0..a_(binomial(n+d,d)-1),s]
R = C[t,x_1..x_n]
f = (basis(d,R)*matrix pack(1, drop(gens C, -1)))_(0,0)

g = sub(f, apply(drop(gens R, 1), v -> v => v*last gens C))
F = g
for i to e-1 do F = tOperator(F, (basis(1,R,Variables=>drop(gens R,1))*random(k^n,k^1))_(0,0))
system = sub(last coefficients(F, Monomials => basis(first degree f,R)), C)

S = k[gens C | {t}]
H = flatten entries sub(system, S)
sols = bertiniUserHomotopy(t,{s=>t},H,{point{toList(#gens S-2:0)}})

f = det(R_0*id_(R^d) + R_1*diagonalMatrix {1_R,2,3} + R_2*diagonalMatrix {4_R,5,6})
p = point sub(last coefficients f, CC)
sols = bertiniUserHomotopy(t,{s=>t},H-p#Coordinates,{p})

needsPackage "Bertini"
R = CC[x,a,t]
H = { (x^2-1)*a^3 + (x^2-2)*(1-a)^2}
sol1 = point {{1}}
sol2 = point {{ -1}}
S1= { sol1, sol2  }
S0 = bertiniUserHomotopy (t,{a=>t}, H, S1)
