///////////////////////////////////////////////////////////////////////////
//  lib.m
//
//  Stable core for extremal rational elliptic surfaces:
//    - Picard lattice / intersection form
//    - affine E8 lifting machinery
//    - computation of (-2)-curves
//    - Riemann--Roch polytope and (-1)-curves
//    - A8, index 3: the two extension classes
//
//  Conventions:
//    Pic(X) = Z^10 with basis (H,E1,...,E9)
//    K_X    = -3H + E1 + ... + E9
//    intersection form = diag(1,-1,...,-1)
//
//  Magma-user-file conventions:
//    - no intrinsic
//    - no require
//    - no reassignment of variables used in `for ... in ... do`
///////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////
//  0. SMALL HELPERS
///////////////////////////////////////////////////////////////////////////

SequenceGCDRES := function(v)
    local g, i;
    if #v eq 0 then
        return 0;
    end if;

    g := 0;
    for i in [1..#v] do
        g := Gcd(g, Integers()!v[i]);
    end for;

    if g lt 0 then
        g := -g;
    end if;

    return g;
end function;

ZeroOfParentRES := function(a)
    local G;
    G := Parent(a);
    return G!0;
end function;

///////////////////////////////////////////////////////////////////////////
//  1. BASIC LATTICE OBJECTS
///////////////////////////////////////////////////////////////////////////

PicardLatticeRES := function()
    return ToricLattice(10);
end function;

CanonicalClassRES := function(Pic)
    if Dimension(Pic) ne 10 then
        error "The Picard lattice must have rank 10.";
    end if;
    return Pic!([-3] cat [1 : i in [1..9]]);
end function;

IntersectionMatrixRES := function()
    return DiagonalMatrix(Integers(), [1] cat [-1 : i in [1..9]]);
end function;

IntersectionRES := function(A, B)
    local a, b;
    a := Eltseq(A);
    b := Eltseq(B);

    if not (#a eq 10 and #b eq 10) then
        error "The arguments must lie in the rank-10 Picard lattice.";
    end if;

    return a[1]*b[1] - &+[a[i]*b[i] : i in [2..10]];
end function;

SelfIntersectionRES := function(A)
    return IntersectionRES(A, A);
end function;

IsOrthogonalToCanonicalRES := function(A)
    local Pic, K;
    Pic := Parent(A);
    K := CanonicalClassRES(Pic);
    return IntersectionRES(A, K) eq 0;
end function;

IsMinusTwoClassRES := function(A)
    return SelfIntersectionRES(A) eq -2 and IsOrthogonalToCanonicalRES(A);
end function;

IsMinusOneCandidateRES := function(A)
    local Pic, K;
    Pic := Parent(A);
    K := CanonicalClassRES(Pic);
    return SelfIntersectionRES(A) eq -1 and IntersectionRES(A, K) eq -1;
end function;

PrimitiveRepresentativeRES := function(A)
    local Pic, v, g;
    Pic := Parent(A);
    v := Eltseq(A);
    g := SequenceGCDRES(v);

    if g eq 0 then
        return A;
    end if;

    return Pic![v[i] div g : i in [1..#v]];
end function;

SameRayRES := function(A, B)
    local a, b;
    a := Eltseq(PrimitiveRepresentativeRES(A));
    b := Eltseq(PrimitiveRepresentativeRES(B));
    return a eq b or a eq [-u : u in b];
end function;

///////////////////////////////////////////////////////////////////////////
//  2. LIFTING UTILITIES
///////////////////////////////////////////////////////////////////////////

KernelGeneratorIfCyclicRES := function(phi)
    local K, G;
    K := Kernel(phi);
    G := Domain(phi);

    if Ngens(K) gt 1 then
        error "The kernel is not cyclic; this routine applies only in the cyclic case.";
    end if;

    if #K eq 1 then
        return G!0;
    end if;

    return K.1;
end function;

HasPreimageRES := function(phi, a)
    local x, G;
    G := Domain(phi);

    try
        x := a @@ phi;
        return true, x;
    catch err
        return false, G!0;
    end try;
end function;

RequirePreimageRES := function(phi, a)
    local ok, x;
    ok, x := HasPreimageRES(phi, a);
    if not ok then
        error "The requested element does not lie in the image of the homomorphism.";
    end if;
    return x;
end function;

StandardDifferenceMapRES := function(Z8)
    local Z9;

    if Dimension(Z8) ne 8 then
        error "The codomain must have rank 8.";
    end if;

    Z9 := RSpace(BaseRing(Z8), 9);

    return hom< Z9 -> Z8 |
        [ Z8.i : i in [1..8] ] cat [ Z8![-2,-4,-6,-3,-5,-4,-3,-2] ]
    >;
end function;

LiftHomomorphismRES := function(phiGA, f)
    local G, Z8, phi, Z9, kerGen, imagesZ9, i, ai, gi, coeffs, ninth,
          liftZ9;

    G := Domain(phiGA);
    Z8 := Domain(f);

    if Dimension(Z8) ne 8 then
        error "The map f must have domain of rank 8.";
    end if;

    phi := StandardDifferenceMapRES(Z8);
    Z9 := Domain(phi);

    kerGen := KernelGeneratorIfCyclicRES(phiGA);

    imagesZ9 := [];
    for i in [1..8] do
        ai := f(phi(Z9.i));
        gi := RequirePreimageRES(phiGA, ai);
        Append(~imagesZ9, gi);
    end for;

    coeffs := [-2,-4,-6,-3,-5,-4,-3,-2];
    ninth := -kerGen + &+[ coeffs[i] * imagesZ9[i] : i in [1..8] ];
    Append(~imagesZ9, ninth);

    // Generic map: free Z-module -> finite abelian group.
    liftZ9 := map< Z9 -> G | x :-> &+[
        (Integers()!Eltseq(x)[i]) * imagesZ9[i] : i in [1..9]
    ] >;

    return liftZ9, kerGen, imagesZ9;
end function;

///////////////////////////////////////////////////////////////////////////
//  3. WEYL / E8 AFFINE BASIS
///////////////////////////////////////////////////////////////////////////

StandardWeylGeneratorsRES := function()
    local gens, cremona;

    gens := [PermutationMatrix(Integers(), Sym(10)!(i, i+1)) : i in [2..8]];

    cremona := DiagonalJoin(
        Matrix(Integers(), [[2,-1,-1,-1],
                            [1, 0,-1,-1],
                            [1,-1, 0,-1],
                            [1,-1,-1, 0]]),
        IdentityMatrix(Integers(), 6)
    );

    Append(~gens, cremona);
    return gens;
end function;

StandardWeylGroupRES := function()
    return MatrixGroup<10, Integers() | StandardWeylGeneratorsRES()>;
end function;

AffineE8BasisChangeMatrixRES := function()
    local Z10, H, E, lis, M;

    Z10 := RSpace(Integers(), 10);
    H := Z10.1;
    E := [Z10.i : i in [2..10]];

    // New basis:
    //   [E1, alpha1, alpha2, alpha3, alpha4, alpha5, alpha6, alpha7, alpha8, alpha0]
    // with
    //   alpha1 = E1-E2, ..., alpha3 = E3-E4,
    //   alpha4 = H-E1-E2-E3,
    //   alpha5 = E4-E5, ..., alpha8 = E7-E8,
    //   alpha0 = E8-E9.
    lis := [E[i] - E[i+1] : i in [1..3]]
           cat [H - &+E[1..3]]
           cat [E[i] - E[i+1] : i in [4..8]];

    M := Matrix(Integers(), [Eltseq(E[1])] cat [Eltseq(v) : v in lis]);
    return M;
end function;

BuildPicardFiniteMapFromAffineLiftRES := function(imagesZ9, Gmid)
    local Pic, M, N, newImgs, baseImgs, i, j, coeff, img, row, phi;

    if #imagesZ9 ne 9 then
        error "imagesZ9 must contain 9 elements.";
    end if;

    Pic := PicardLatticeRES();
    M := AffineE8BasisChangeMatrixRES();
    N := ChangeRing(M, Rationals())^(-1);

    // The first new-basis vector E1 is sent to 0 in the finite group.
    newImgs := [Gmid!0] cat imagesZ9;

    baseImgs := [];
    for i in [1..10] do
        row := [];
        for j in [1..10] do
            coeff := N[i,j];
            if Denominator(coeff) ne 1 then
                error "Non-integral coefficient in the affine-to-Picard change of basis.";
            end if;
            Append(~row, Integers()!coeff);
        end for;

        img := Gmid!0;
        for j in [1..10] do
            img := img + row[j] * newImgs[j];
        end for;
        Append(~baseImgs, img);
    end for;

    phi := map< Pic -> Gmid | x :-> &+[
        (Integers()!Eltseq(x)[i]) * baseImgs[i] : i in [1..10]
    ] >;

    return phi, baseImgs;
end function;

///////////////////////////////////////////////////////////////////////////
//  4. (-2)-CURVES
///////////////////////////////////////////////////////////////////////////

FindCompRES := function(f)
    local Pic, K, G, H, zeroG, invs, d, m, W, v, orb, S;
    local ww, uu, cc, cur, lifts, rlist, r, C, q, rem, dmin, Q, Sd, Qseq, M;

    Pic := Domain(f);
    K := CanonicalClassRES(Pic);
    G := Parent(f(K));
    H := sub<G | f(K)>;
    zeroG := G!0;

    invs := [a : a in AbelianInvariants(G) | a ne 0];
    if #invs eq 0 then
        d := 1;
    else
        d := Lcm(invs);
    end if;

    m := Min([n : n in [1..d] | n*f(K) eq zeroG]);

    W := StandardWeylGroupRES();
    v := Vector([0,1,-1,0,0,0,0,0,0,0]);
    orb := v^W;

    S := [];
    for ww in orb do
        uu := Pic!Eltseq(ww);
        if f(uu) in H then
            Append(~S, uu);
        end if;
    end for;

    cc := [Pic.i - Pic.j : i, j in [2..10] | i lt j];
    cur := {C0 : C0 in cc | f(C0) eq zeroG};

    if #cur ne 0 then
        cur := {Pic!Eltseq(R) : R in Rays(Cone([Eltseq(C0) : C0 in cur]))};
    end if;

    lifts := cur;
    for uu in S do
        rlist := [n : n in [0..m-1] | f(uu + n*K) eq zeroG];
        if #rlist eq 0 then
            error "Internal error: no shift along K kills the class.";
        end if;

        r := rlist[1];
        C := uu + r*K;
        q, rem := Quotrem(Eltseq(C)[1], 3*m);
        C := C + q*m*K;

        if Eltseq(C)[1] eq 0 and C notin cur then
            C := C - m*K;
        end if;

        Include(~lifts, C);
    end for;

    if #lifts eq 0 then
        return {}, ZeroMatrix(Integers(), 0, 0);
    end if;

    dmin := Min([Eltseq(E0)[1] : E0 in lifts]);
    if dmin eq 0 then
        Q := cur;
    else
        Q := {E0 : E0 in lifts | Eltseq(E0)[1] eq dmin};
    end if;

    lifts := lifts diff {E0 : E0 in lifts | Eltseq(E0)[1] eq 0};

    while lifts ne {} do
        d := Minimum({Eltseq(E0)[1] : E0 in lifts});
        Sd := {C0 : C0 in lifts | Eltseq(C0)[1] eq d};
        Q := Q join {C0 : C0 in Sd | Minimum([IntersectionRES(C0, R0) : R0 in Q]) ge 0};
        lifts := lifts diff Sd;
    end while;

    Qseq := Setseq(Q);
    if #Qseq eq 0 then
        M := ZeroMatrix(Integers(), 0, 0);
    else
        M := Matrix(#Qseq, #Qseq, [IntersectionRES(Qseq[i], Qseq[j]) :
                                   i, j in [1..#Qseq]]);
    end if;

    return Q, M;
end function;


///////////////////////////////////////////////////////////////////////////
//  5A. FINITE LATTICE SEARCH FOR (-1)-CURVES
///////////////////////////////////////////////////////////////////////////

forward IntegerVectorsSumSquaresRES;

IntSqrtRES := function(N)
    local r;
    if N lt 0 then
        error "IntSqrtRES expects a non-negative integer.";
    end if;

    r := 0;
    while (r+1)^2 le N do
        r := r + 1;
    end while;

    return r;
end function;

CeilDivRES := function(a, b)
    local q, r;
    if b le 0 then
        error "CeilDivRES expects a positive denominator.";
    end if;

    q, r := Quotrem(a, b);
    if r eq 0 then
        return q;
    else
        return q + 1;
    end if;
end function;

IntegerVectorsSumSquaresRES := function(n, S, Q)
    local B, out, x, tail, T, R, lower;

    if n eq 0 then
        if S eq 0 and Q eq 0 then
            return [ [] ];
        else
            return [];
        end if;
    end if;

    if Q lt 0 then
        return [];
    end if;

    if n eq 1 then
        if S^2 eq Q then
            return [ [S] ];
        else
            return [];
        end if;
    end if;

    // Cauchy lower bound for remaining coordinates.
    if S^2 gt n*Q then
        return [];
    end if;

    B := IntSqrtRES(Q);
    out := [];

    for x in [-B..B] do
        T := S - x;
        R := Q - x^2;

        if R ge 0 then
            // Necessary condition: T^2 <= (n-1) R.
            if T^2 le (n-1)*R then
                for tail in IntegerVectorsSumSquaresRES(n-1, T, R) do
                    Append(~out, [x] cat tail);
                end for;
            end if;
        end if;
    end for;

    return out;
end function;

FindSectionsBoundedRES := function(cur, maxd)
    local Pic, K, roots, curve, d, S, Q, vecs, v, D, ok, C0;

    Pic := PicardLatticeRES();
    K := CanonicalClassRES(Pic);
    roots := [Pic!Eltseq(C0) : C0 in cur];

    curve := [];

    for d in [0..maxd] do
        // Conditions D.K = -1 and D^2 = -1 for D=(d;m1,...,m9):
        //   sum m_i = 1 - 3d,
        //   sum m_i^2 = d^2 + 1.
        S := 1 - 3*d;
        Q := d^2 + 1;

        vecs := IntegerVectorsSumSquaresRES(9, S, Q);

        for v in vecs do
            D := Pic!([d] cat v);

            ok := true;
            for C0 in roots do
                if IntersectionRES(D, C0) lt 0 then
                    ok := false;
                    break;
                end if;
            end for;

            if ok then
                Append(~curve, D);
            end if;
        end for;
    end for;

    return curve;
end function;

///////////////////////////////////////////////////////////////////////////
//  5. RIEMANN--ROCH POLYTOPE AND (-1)-CURVES
///////////////////////////////////////////////////////////////////////////

FindPolRES := function(cur)
    local Pic, PicD, D, K, P, Q, qmap;

    Pic := PicardLatticeRES();
    PicD := Dual(Pic);
    cur := [Pic!Eltseq(C0) : C0 in cur];
    D := IntersectionMatrixRES();
    K := CanonicalClassRES(Pic);

    // This is the original working construction:
    // P lives in the ambient polyhedral lattice attached to Pic,
    // and Quotient(K) removes the canonical direction.
    P := &meet[HalfspaceToPolyhedron(PicD!Eltseq(C0) * D, 0) : C0 in cur]
         meet HyperplaneToPolyhedron(-PicD!Eltseq(K) * D, 1);

    Q, qmap := Quotient(K);
    return Image(qmap, P);
end function;

FindSectionsRES := function(cur)
    local Pic, PicD, D, K, P, Q, qmap, pts, curve, qpt, pt, s, n;

    Pic := PicardLatticeRES();
    PicD := Dual(Pic);
    cur := [Pic!Eltseq(C0) : C0 in cur];
    D := IntersectionMatrixRES();
    K := CanonicalClassRES(Pic);

    // Riemann--Roch polyhedron:
    //   psi(-K)=1, psi(C)>=0 for all (-2)-curves C.
    P := &meet[HalfspaceToPolyhedron(PicD!Eltseq(C0) * D, 0) : C0 in cur]
         meet HyperplaneToPolyhedron(-PicD!Eltseq(K) * D, 1);

    // Quotient by the K-direction. This is the robust method from the older
    // library: enumerate points after passing to Pic/<K>.
    Q, qmap := Quotient(K);
    pts := [Preimage(qmap, qpt) : qpt in Points(Image(qmap, P))];

    curve := [];
    for pt in pts do
        s := SelfIntersectionRES(pt) + 1;
        if (s mod 2) ne 0 then
            error "Unexpected parity obstruction when lifting a point of the Riemann--Roch polytope.";
        end if;
        n := s div 2;
        Append(~curve, pt + n*K);
    end for;

    return curve;
end function;

FindSectionsHRES := function(cur, H0)
    local Pic, PicD, D, K, Hd, Kd, P, HH;

    Pic := PicardLatticeRES();
    PicD := Dual(Pic);
    D := IntersectionMatrixRES();
    K := CanonicalClassRES(Pic);

    HH := Pic!Eltseq(H0);
    Hd := PicD!Eltseq(HH);
    Kd := PicD!Eltseq(K);
    cur := [Pic!Eltseq(C0) : C0 in cur];

    if #cur eq 0 then
        P := HyperplaneToPolyhedron(-Kd * D, 1)
             meet HyperplaneToPolyhedron(Hd * D, 0);
    else
        P := &meet[HalfspaceToPolyhedron((PicD!Eltseq(C0)) * D, 0) : C0 in cur]
             meet HyperplaneToPolyhedron(-Kd * D, 1)
             meet HyperplaneToPolyhedron(Hd * D, 0);
    end if;

    return P;
end function;

///////////////////////////////////////////////////////////////////////////
//  6. AUXILIARY LATTICE UTILITIES
///////////////////////////////////////////////////////////////////////////

quaLRES := function(A, B, M, lis)
    local Kfield, n, N, sol, E, A1, B1;

    Kfield := Rationals();
    M := Matrix(Kfield, M);
    n := Nrows(M);

    if #lis eq 0 then
        return (Matrix(Kfield,1,n,Eltseq(A)) * M * Matrix(Kfield,n,1,Eltseq(B)))[1,1];
    end if;

    E := ToricLattice(n);
    N := Matrix(Kfield, lis) * M * Transpose(Matrix(Kfield, lis));

    sol := Solution(N, Matrix(Kfield,1,n,Eltseq(A)) * M * Transpose(Matrix(Kfield, lis)));
    A1 := E!Eltseq(A) - &+[E!lis[i] * Eltseq(sol)[i] : i in [1..#lis]];

    sol := Solution(N, Matrix(Kfield,1,n,Eltseq(B)) * M * Transpose(Matrix(Kfield, lis)));
    B1 := E!Eltseq(B) - &+[E!lis[i] * Eltseq(sol)[i] : i in [1..#lis]];

    return (Matrix(Kfield,1,n,Eltseq(A1)) * M * Matrix(Kfield,n,1,Eltseq(B1)))[1,1];
end function;

StdFormRES := function(H0)
    local Pic, v, mults, d, i, j, k, q, sm;

    Pic := Parent(H0);
    v := Eltseq(H0);
    d := v[1];
    mults := v[2..10];

    repeat
        sm := Sort(mults);
        i := Index(mults, sm[1]);
        j := [n : n in [1..9] | n ne i and mults[n] eq sm[2]][1];
        k := [n : n in [1..9] | n notin [i,j] and mults[n] eq sm[3]][1];
        q := d + mults[i] + mults[j] + mults[k];

        if q lt 0 then
            d := d + q;
            mults[i] := mults[i] - q;
            mults[j] := mults[j] - q;
            mults[k] := mults[k] - q;
        end if;
    until q ge 0 or d le 0;

    return Pic!([d] cat mults);
end function;

///////////////////////////////////////////////////////////////////////////
//  7. SMOKE TEST
///////////////////////////////////////////////////////////////////////////

procedure SmokeTestRES()
    local Pic, K, a, b;

    Pic := PicardLatticeRES();
    K := CanonicalClassRES(Pic);

    a := Pic![0,1,-1,0,0,0,0,0,0,0];
    b := Pic![1,1,0,0,0,0,0,0,0,0];

    print "Picard lattice rank:", Dimension(Pic);
    print "Canonical class:", K;
    print "a^2 =", SelfIntersectionRES(a);
    print "a.K =", IntersectionRES(a, K);
    print "b^2 =", SelfIntersectionRES(b);
    print "b.K =", IntersectionRES(b, K);
end procedure;

///////////////////////////////////////////////////////////////////////////
//  8. BACKWARDS-COMPATIBLE ALIASES
///////////////////////////////////////////////////////////////////////////

qua := function(a, b)
    return IntersectionRES(a, b);
end function;

LiftHomomorphism := function(phiGA, f)
    return LiftHomomorphismRES(phiGA, f);
end function;

FindComp := function(f)
    return FindCompRES(f);
end function;

FindSections := function(cur)
    return FindSectionsRES(cur);
end function;

FindPol := function(cur)
    return FindPolRES(cur);
end function;

quaL := function(A, B, M, lis)
    return quaLRES(A, B, M, lis);
end function;

FindSectionsH := function(cur, H0)
    return FindSectionsHRES(cur, H0);
end function;

StdForm := function(H0)
    return StdFormRES(H0);
end function;
