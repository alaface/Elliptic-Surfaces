// Function to lift a homomorphism f: Z^8 -> A to a homomorphism Z^10 -> G + Z
// Input:
//   - GA_Homomorphism: A homomorphism from G to A
//   - f: A homomorphism from Z^8 to A
// Output:
//   - LiftedHom: A homomorphism from Z^10 to G + Z
//   - Subgroup: A subgroup of the codomain of LiftedHom
function LiftHomomorphism(GA_Homomorphism, f)
    G := Domain(GA_Homomorphism);
    A := Codomain(GA_Homomorphism);
    
    Z8 := Domain(f);
    Z9 := RSpace(BaseRing(Z8), 9);

    phi := hom<Z9->Z8 | [Z8.i : i in [1..8]] cat [Z8![-2,-4,-6,-3,-5,-4,-3,-2]]>;
    f_phi := func<x | f(phi(x))>;
    
    ker := Kernel(GA_Homomorphism);
    if #ker eq 1 then KernelGen := Zero(ker); else KernelGen := ker.1; end if;

    images := [];
    for i in [1..8] do
        elem := f_phi(Z9.i);
        preimage := IsCoercible(G, elem @@ GA_Homomorphism) select elem @@ GA_Homomorphism else G!0;
        Append(~images, preimage);
    end for;
    
    coeffs := [-2,-4,-6,-3,-5,-4,-3,-2];
    images := images cat [-KernelGen + &+[coeffs[i] * images[i] : i in [1..#coeffs]]];
    
    LiftedHom := hom<Z9 -> G | images>;

    Z10 := RSpace(Integers(), 10);
    H := Z10.1;
    E := [Z10.i : i in [2..10]];
    GG := DirectSum(G, RSpace(Integers(), 1));
    n := #Generators(GG);
    gg := hom<Z10 -> GG | [GG.n] cat [GG!(Eltseq(LiftedHom(b)) cat [0]) : b in Basis(Z9)]>;
    lis := [E[i] - E[i+1] : i in [1..3]] cat [H - &+E[1..3]] cat [E[i] - E[i+1] : i in [4..8]];
    M := Matrix([E[1]] cat lis);
    h := hom<Z10 -> Z10 | M^(-1)>;
    LiftedHom := hom<Z10 -> GG | [(h * gg)(b) : b in Basis(Z10)]>;

    K := Z10![-3, 1, 1, 1, 1, 1, 1, 1, 1, 1];
    
    return LiftedHom, sub<GG | LiftedHom(K)>;
end function;

// Function to compute a quadratic form value
// Input:
//   - a, b: Elements of a lattice represented as vectors
// Output:
//   - The value of the quadratic form qua(a, b)
qua := function(a, b)
    a := Eltseq(a);
    b := Eltseq(b);
    return a[1] * b[1] - &+[a[i] * b[i] : i in [2..#a]];
end function;

// Function to find all the (-2)-curves of the surface
// Input:
//   - f: A homomorphism from a Picard lattice to a group
// Output:
//   - Q: all the (-2)-curves of the surface
//   - CartanName: The Cartan type of the lattice
FindComp := function(f)
    Pic := Domain(f);
    K := Pic![-3, 1, 1, 1, 1, 1, 1, 1, 1, 1];
    G := Parent(f(K));
    H := sub<G|f(K)>;
    d := Lcm([u : u in Moduli(G) | u ne 0]);
    m := Min([n : n in [1..d] | n * f(K) eq Zero(G)]);

    S10 := Sym(10);
    gens := [PermutationMatrix(Integers(), S10!(i, i+1)) : i in [2..8]] 
             cat [DiagonalJoin(Matrix([[2, -1, -1, -1], 
                                       [1,  0, -1, -1], 
                                       [1, -1,  0, -1], 
                                       [1, -1, -1,  0]]),
                 IdentityMatrix(Integers(), 6))];
    W := MatrixGroup<10, Integers() | gens>;

    v := Vector([0, 1, -1, 0, 0, 0, 0, 0, 0, 0]);
    S := [C : C in v^W | f(C) in H];
    cur := {};
    for u in S do
        r := [n : n in [0..m] | f(u + n*K) eq Zero(H)][1];
        C := u + r*K;
        q := Quotrem(C[1], 3 * m);
        Include(~cur, C + q * m * K);
    end for;

    cc := [Pic.i - Pic.(i+1) : i in [2..9]];
    Q := {E : E in cur | E[1] eq 0 and E in cc};
    cur := cur diff {E : E in cur | E[1] eq 0};
    while cur ne {} do
        d := Minimum({E[1] : E in cur});
        C := Random([E : E in cur | E[1] eq d]);
        if Minimum([qua(C, E) : E in Q]) ge 0 then Q := Q join {C}; end if;
        cur := cur diff {C};
    end while;
    M := Matrix(#Q, #Q, [qua(a, b) : a, b in Q]);
    return Q, CartanName(-M);
end function;

// Function to find all the (-1)-curves of the surface
// Input:
//   - cur: A set of roots
//   - m: A scalar value
// Output:
//   - curve: all the (-1)-curves of the surface
FindSections := function(cur)
    Pic := ToricLattice(10);
    cur := [Pic!Eltseq(C) : C in cur];
    D := DiagonalMatrix([1] cat [-1 : i in [2..10]]);
    K := Pic!([-3] cat [1 : i in [2..10]]);
    P := &meet[HalfspaceToPolyhedron(C * D, 0) : C in cur] meet HyperplaneToPolyhedron(-K * D, 1);
    P := CompactPart(P);
    P := Polytope([Pic!Eltseq(p) : p in Vertices(P)]);
    Q,f := Quotient(K);
    pts := [Preimage(f,p) : p in Points(Image(f,P))];
    curve := [];
    for p in pts do
        Append(~curve, p + Quotrem(qua(p, p) + 1, 2) * K);
    end for;
    return curve;
end function;
