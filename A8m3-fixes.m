///////////////////////////////////////////////////////////////////////////
//  A8m3-fixes.m
//
//  Temporary fixes for A8m3.txt. Load after A8m3.txt:
//      load "lib.m";
//      load "A8m3.txt";
//      load "A8m3-fixes.m";
///////////////////////////////////////////////////////////////////////////

A8AsPicSeqRES := function(Q)
    local Pic, C0;

    Pic := PicardLatticeRES();

    if Type(Q) eq SetEnum then
        return [Pic!Eltseq(C0) : C0 in Setseq(Q)];
    end if;

    return [Pic!Eltseq(C0) : C0 in Q];
end function;

A8OrthogonalNegativeCurvesRES := function(H, CurMinus2, CurMinus1)
    local Pic, roots, secs, roots0, secs0, all0, C0;

    Pic := PicardLatticeRES();
    H := Pic!Eltseq(H);

    roots := A8AsPicSeqRES(CurMinus2);
    secs  := A8AsPicSeqRES(CurMinus1);

    roots0 := [C0 : C0 in roots | IntersectionRES(H, C0) eq 0];
    secs0  := [C0 : C0 in secs  | IntersectionRES(H, C0) eq 0];

    all0 := roots0 cat secs0;

    return all0, roots0, secs0;
end function;

A8ScoreLineClassRES := function(H, CurMinus2, CurMinus1, target)
    local Pic, roots, secs, negs, prods, minp, maxp, bad, sumabs, sumsq;
    local orth, d, C0, p;

    Pic := PicardLatticeRES();
    H := Pic!Eltseq(H);

    roots := A8AsPicSeqRES(CurMinus2);
    secs  := A8AsPicSeqRES(CurMinus1);
    negs  := roots cat secs;

    prods := [IntersectionRES(H, C0) : C0 in roots];

    if #prods eq 0 then
        minp := 0;
        maxp := 0;
    else
        minp := Minimum(prods);
        maxp := Maximum(prods);
    end if;

    bad := 0;
    sumabs := 0;
    sumsq := 0;

    for p in prods do
        if p ne target then
            bad := bad + 1;
        end if;
        sumabs := sumabs + Abs(p - target);
        sumsq := sumsq + (p - target)^2;
    end for;

    orth := #[C0 : C0 in negs | IntersectionRES(H, C0) eq 0];
    d := Eltseq(H)[1];

    return [Abs(orth - 9), bad, maxp - minp, sumabs, sumsq, d, maxp];
end function;

A8FindNefPlaneClassesRES := function(CurMinus2, CurMinus1, maxd, target, maxout)
    local Pic, K, roots, secs, negs, out, d, candidates, H;
    local score, orth, orth2, orth1, rootProducts, cand;

    Pic := PicardLatticeRES();
    K := CanonicalClassRES(Pic);

    roots := A8AsPicSeqRES(CurMinus2);
    secs  := A8AsPicSeqRES(CurMinus1);
    negs  := roots cat secs;

    out := [* *];

    for d in [1..maxd] do
        candidates := A8LineCandidateClassesOfDegreeRES(d);

        for H in candidates do
            H := Pic!Eltseq(H);

            if SelfIntersectionRES(H) eq 1 and IntersectionRES(H, K) eq -3 then
                if A8IsNefAgainstRES(H, negs) then
                    score := A8ScoreLineClassRES(H, roots, secs, target);
                    orth, orth2, orth1 := A8OrthogonalNegativeCurvesRES(H, roots, secs);
                    rootProducts := [IntersectionRES(H, C0) : C0 in roots];

                    cand := <score, H, rootProducts, orth, orth2, orth1>;
                    out := A8InsertCandidateRES(out, cand, maxout);
                end if;
            end if;
        end for;
    end for;

    return out;
end function;

A8PlaneImageDataRES := function(H, CurMinus2, OrthNeg)
    local roots, Rseq, C0;

    roots := A8AsPicSeqRES(CurMinus2);
    H := PicardLatticeRES()!Eltseq(H);

    Rseq := [C0 : C0 in roots | IntersectionRES(H, C0) gt 0];

    return A8PlaneImageForClassesRES(H, Rseq, OrthNeg);
end function;
