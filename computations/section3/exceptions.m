// Exact finite group computations for the degrees where profile bounds fail.
// No search, random choice, or probabilistic acceptance is used here.

function S3ClassCertificate(n)
    G := Sym(n);
    primes := PrimeDivisors(#G);
    Ps := [ SylowSubgroup(G, p) : p in primes ];
    Ns := [ Normalizer(G, P) : P in Ps ];
    minima := [];
    for i in [1..#primes] do
        P := Ps[i];
        assert #P eq primes[i]^Valuation(#G, primes[i]);
        reps, weights := DoubleCosetRepresentatives(G, Ns[i], Ns[i]);
        assert &+weights eq #G;
        Append(~minima, Min([ #(P meet P^g) : g in reps ]));
    end for;
    // Conjugacy-invariant sample spaces: (3)(2) or (5)(3).
    x := n eq 8 select G!(1,2,3,4,5)(6,7,8) else G!(1,2,3)(4,5);
    C := Centralizer(G, x);
    terms := [];
    for i in [1..#primes] do
        reps, weights := DoubleCosetRepresentatives(G, C, Ns[i]);
        assert &+weights eq #G;
        bad := 0;
        for k in [1..#reps] do
            if #(Ps[i] meet Ps[i]^(x^reps[k])) gt minima[i] then
                bad +:= weights[k];
            end if;
        end for;
        Append(~terms, Rationals()!bad/#G);
    end for;
    expected := n eq 5 select [Rationals() | 3/5, 1/10, 0]
        else n eq 6 select [Rationals() | 11/15, 1/10, 0]
        else [Rationals() | 10/21, 5/56, 1/336, 0];
    assert terms eq expected;
    assert minima eq (n eq 8 select [2,1,1,1] else [1,1,1]);
    assert &+terms lt 1;
    // Minimum order among all intersections implies inclusion-minimality.
    printf "CLASS_CERTIFICATE S%o primes=%o minima=%o bad_sum=%o\n",
        n, primes, minima, &+terms;
    return &+terms;
end function;

function S3GoodDoubleCosetMass(n, data)
    G := Sym(n);
    P := sub<G | [ G!a : a in data[1] ]>;
    assert #P eq 2^Valuation(#G, 2);
    reps := [ G!a : a in data[2] ];
    keys := [];
    base := [1..n];
    for g in reps do
        assert #(P meet P^g) eq 1;
        key, returnedBase := DoubleCosetCanonical(G, P, g, P : B := base);
        assert returnedBase eq base;
        assert key notin keys;
        Append(~keys, key);
    end for;
    mass := Rationals()!(#reps * #P^2)/#G;
    assert mass le 1;
    printf "DOUBLE_COSET_CERTIFICATE S%o sylow_order=%o disjoint_cosets=%o good_mass=%o\n",
        n, #P, #reps, mass;
    return mass;
end function;

function S3A8GoodMass()
    S := Sym(8);
    G := Alt(8);
    P := (sub<S | (1,2), (1,3)(2,4), (1,5)(2,6)(3,7)(4,8)>) meet G;
    assert #P eq 2^Valuation(#G, 2);
    g := S![2,3,1,5,8,7,4,6];
    assert g in G;
    assert #(P meet P^g) eq 1;
    mass := Rationals()!(#P^2)/#G;
    assert mass eq 64/315;
    printf "DOUBLE_COSET_CERTIFICATE A8 sylow_order=%o disjoint_cosets=1 good_mass=%o\n",
        #P, mass;
    return mass;
end function;
