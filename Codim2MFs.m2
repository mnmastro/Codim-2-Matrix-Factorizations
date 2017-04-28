needsPackage "CompleteIntersectionResolutions"

-- Note: BRanks spits out the ranks of the B modules as {{B01, B11}, {B02, B12}}.

rhoMaps = method()

rhoMaps List := mf -> (
    h2 := (hMaps mf)#1;
    r := BRanks mf;
    {submatrix(h2, apply(r#0#1, i -> i), apply(r#0#0, i -> i)), 
	submatrix(h2, apply(r#0#1, i -> i), apply(r#1#0, i -> r#0#0 + i))}
    )

thetaMaps = method()

thetaMaps List := mf -> (
    h2 := (hMaps mf)#1;
    r := BRanks mf;
    {submatrix(h2, apply(r#1#1, i -> r#0#1 + i), apply(r#0#0, i -> i)), 
	submatrix(h2, apply(r#1#1, i -> r#0#1 + i), apply(r#1#0, i -> r#0#0 + i))}
    )    

epsilonMaps = method()

epsilonMaps List := mf -> (
    d := mf#0;
    h := hMaps mf;
    b1 := (bMaps mf)#0;
    f1 := (b1*h#0)_0_0;
    eps := d*h#1;
    B := source eps;
    eps = (eps - (eps)_0_0*id_B)//f1;
    r := BRanks mf;
    {submatrix(eps, apply(r#1#0, i -> r#0#0 + i), apply(r#0#0, i -> i)), 
	submatrix(eps, apply(r#1#0, i -> r#0#0 + i), apply(r#1#0, i -> r#0#0 + i))}
    )

omegaMaps = method()

omegaMaps List := mf -> (
    d := mf#0;
    h := hMaps mf;
    b1 := (bMaps mf)#0;
    f1 := (b1*h#0)_0_0;
    f2 := (d*h#1)_0_0;
    omega := h#1*d;
    B := source omega;
    omega = (omega - f2*id_B)//f1;
    r := BRanks mf;
    {submatrix(omega, apply(r#1#1, i -> r#0#1 + i), apply(r#0#1, i -> i)), 
	submatrix(omega, apply(r#1#1, i -> r#0#1 + i), apply(r#1#1, i -> r#0#1 + i))}
    )

sigmaMaps = method()

sigmaMaps List := mf -> (
    Q := ring(mf#0);
    d := mf#0;
    h := hMaps mf;
    b1 := (bMaps mf)#0;
    f := matrix {{(b1*h#0)_0_0, (d*h#1)_0_0}};
    L := (makeFiniteResolutionCodim2(mf, f))#"resolution";
    r := BRanks mf;
    sigma10 := {(h#0|map(Q^(r#0#1),Q^(r#1#0),0))||map(Q^(r#1#1),L#0,0)||
	(map(Q^(r#1#0),Q^(r#0#0),0)|id_(Q^(r#1#0))), 
	map(Q^(r#1#1),Q^(r#0#1),0)|(-id_(Q^(r#1#1)))|map(Q^(r#1#1),Q^(r#1#0),0)};
    sigma10 = map(L[1], L, i -> sigma10#i);    
    eps := epsilonMaps mf;
    eps = eps#0|eps#1;
    omega := omegaMaps mf;
    omega = omega#0|omega#1;
    theta2 := (thetaMaps mf)#1;
    sigma01 := {h#1||(-eps), omega|theta2};
    sigma01 = map(L[1], L, i -> sigma01#i);
    {sigma10, sigma01}
    )

-- WARNING: As of March 2017, makeFiniteResolution and makeFiniteResolutionCodim2 do not
-- yield the same resoltuion of a codimension 2 MF module.  The former appears to incorrectly
-- negate the bottom rightmost blocks of each differential.

-- To make the above work with makeFiniteResolution instead, one would have to make the
-- following changes to sigmaMaps:

-- 1. Negate the identity map in the bottom corner of the first part of sigma10.
-- 2. Negate theta2 instead of eps
  


-- Given a codimension two matrix factorization of f1, f2 over a ring Q, constructs 
-- the corresponding graded matrix factorization of W = f1*T_1 + f2*T_2 over Q[T_1,T_2].

toGradedMF = method()

toGradedMF List := mf -> (
    Q := ring(mf#0);
    T := local T;
    S := Q[T_1,T_2];
    d := mf#0;
    h := hMaps mf;
    b1 := (bMaps mf)#0;
    f := matrix {{(b1*h#0)_0_0, (d*h#1)_0_0}};
    L := (makeFiniteResolutionCodim2(mf, f))#"resolution";
    sigma := sigmaMaps mf;
    e0 := (sub(L.dd_2,S))|(T_1*sub(sigma#0_0,S)+T_2*sub(sigma#1_0,S));
    e1 := (T_1*sub(sigma#0_1,S) + T_2*sub(sigma#1_1,S))||sub(L.dd_1,S);
    {e0,e1}
    )


/// TEST

Q = QQ[x,y,z];
f = matrix{{x*z,y^2}};
R = Q/ideal(f);
M = highSyzygy coker matrix {{x,y}}
mf = matrixFactorization(f, M, Check => true)
L = (makeFiniteResolutionCodim2(mf, f))#"resolution"; L.dd
eps = epsilonMaps mf
omega = omegaMaps mf
sigma = sigmaMaps mf
dL = map(L[-1],L, i -> L.dd_i);


-- Asserts that sigma is a system of higher homotopies.

assert(dL[1]*(sigma#0) + (sigma#0)[-1]*dL == f_0_0*id_L)
assert(dL[1]*(sigma#1) + (sigma#1)[-1]*dL == f_1_0*id_L)

E = toGradedMF mf
S = ring E#0;
W = (f*(transpose vars S))_0_0;

-- Asserts that E is a graded matrix factorization of W.

assert(E#0*E#1 == W*id_(source E#1))
assert(E#1*E#0 == W*id_(source E#0))


///


