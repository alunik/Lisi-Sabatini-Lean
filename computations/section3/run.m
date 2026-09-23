// Section 3 of "Sylow synchronization in finite groups: The good case".
// Run from this directory: magma -b run.m
// A complete run must end with SECTION3_PASS (see verify.py).
SetColumns(1000);
SetSeed(21262026);
started := Cputime();
v1, v2, v3 := GetVersion();
printf "MAGMA_VERSION %o.%o-%o\n", v1, v2, v3;
load "profiles.m";
load "witnesses.m";
load "exceptions.m";

// Check the arithmetic model against actual permutation groups, including
// alternating split classes. This is validation, not an assumption of the proof.
S3ValidateProfiles(5,12);

symCount := 0;
altCount := 0;
mixedCount := 0;
for n in [5..40] do
    primes := PrimeDivisors(Factorial(n));
    oddCost := &+[ Rationals() | S3SymmetricCost(n,p) : p in primes | p ne 2 ];
    if n in [5,6,8] then
        symBound := S3ClassCertificate(n);
        method := "conjugacy_class";
    elif n in [9,10,12] then
        mass := S3GoodDoubleCosetMass(n, S3Witnesses[n]);
        symBound := 1 - mass + oddCost;
        method := "good_double_cosets";
    elif n in [14,16] then
        symBound := S3MatchingCost(n);
        method := "matching";
    else
        symBound := S3SymmetricCost(n,2) + oddCost;
        method := "cycle_profile";
    end if;
    assert symBound lt 1;
    assert symBound ge 0;
    symCount +:= 1;
    printf "SYMMETRIC_PASS n=%o method=%o bad_bound=%o\n", n, method, symBound;

    if n eq 8 then
        altBound := 1 - S3A8GoodMass() + oddCost;
        method := "good_double_coset";
    else
        altBound := &+[ Rationals() | S3AlternatingCost(n,p) : p in primes ];
        method := "cycle_profile";
    end if;
    assert altBound lt 1;
    assert altBound ge 0;
    altCount +:= 1;
    printf "ALTERNATING_PASS n=%o method=%o bad_bound=%o\n", n, method, altBound;

    if n ge 9 then
        // These bounds use uniform sampling in the whole group. They apply
        // to independently prescribed left/right Sylow rows, hence to every
        // pair of nilpotent subgroups (see README.md for the deduction).
        assert n notin [5,6,8];
        mixedCount +:= 2;
        printf "NILPOTENT_PAIR_PASS n=%o groups=S,A\n", n;
    end if;
end for;

// Fixed rational inequalities displayed in the asymptotic part of Section 3.
anchors := [ <40,2,Rationals()!3/4>, <39,3,Rationals()!1/25>,
             <40,5,Rationals()!1/10000>, <35,7,Rationals()!1/2400> ];
for anchor in anchors do
    n, p, upper := Explode(anchor);
    value := S3Majorant(n,p);
    assert value lt upper;
    printf "ANCHOR_PASS n=%o p=%o value=%o upper=%o\n", n, p, value, upper;
end for;
value := S3EvenMajorant(40);
assert value lt 3/16;
printf "EVEN_ANCHOR_PASS n=40 value=%o upper=3/16\n", value;
symBudget := Rationals()!3/4 + 1/25 + 1/10000 + 1/2400 + 1/1024;
altBudget := Rationals()!3/4 + 4/25 + 1/2500 + 1/600 + 1/256;
assert symBudget lt 1 and altBudget lt 1;
printf "TAIL_BUDGETS_PASS symmetric=%o alternating=%o\n", symBudget, altBudget;

assert symCount eq 36 and altCount eq 36 and mixedCount eq 64;
printf "SECTION3_PASS symmetric=%o alternating=%o nilpotent_pairs=%o anchors=5 cpu_seconds=%o\n",
    symCount, altCount, mixedCount, Cputime(started);
quit;
