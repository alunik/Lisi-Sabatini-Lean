/*
 * Exact arithmetic for Section 3 (symmetric and alternating groups).
 *
 * Every probability bound below is a rational number. No group of degree
 * greater than the optional validation limit is constructed here.
 *
 * If W_k is a Sylow p-subgroup on p^k points, its polynomial A_k records
 * elements of order dividing p by their number of p-cycles. The wreath
 * product recurrence is
 *   A_0 = 1, |W_0| = 1,
 *   A_(k+1) = A_k^p + (p-1)|W_k|^(p-1) X^(p^k),
 *   |W_(k+1)| = p |W_k|^p.
 * Multiplication according to the base-p digits of n gives S3Profile(n,p).
 *
 * The cyclic cost divides the prime-order element class sum by p-1:
 * every nontrivial p-group intersection contains at least p-1 nonidentity
 * elements of order p. This is a bound for every pair of Sylow p-subgroups,
 * so a strict sum of these bounds proves simultaneous avoidance for any
 * independently prescribed pairs of Sylow subgroups at distinct primes.
 */

function S3Profile(n, p)
    assert n ge 0 and IsPrime(p);
    R<X> := PolynomialRing(Integers());
    result := R!1;
    tower := R!1;
    towerOrder := 1;
    blockSize := 1;
    remaining := n;
    while remaining gt 0 do
        result *:= tower^(remaining mod p);
        remaining := remaining div p;
        if remaining gt 0 then
            tower := tower^p + (p-1)*towerOrder^(p-1)*X^blockSize;
            towerOrder := p*towerOrder^p;
            blockSize *:= p;
        end if;
    end while;
    return result;
end function;

function S3ClassSize(n, p, j)
    assert n ge 0 and p ge 2 and j ge 0 and p*j le n;
    return Factorial(n) div (p^j*Factorial(j)*Factorial(n-p*j));
end function;

function S3SymmetricCost(n, p)
    profile := S3Profile(n, p);
    cost := Rationals()!0;
    for j in [1..n div p] do
        cost +:= Coefficient(profile, j)^2 / S3ClassSize(n, p, j);
    end for;
    return cost/(p-1);
end function;

/* For n >= 5 this is the exact cyclic class-sum cost in A_n.
 * At p=2 retain only even numbers of transpositions; these S_n classes
 * do not split in A_n, and their intersections with a Sylow of A_n have
 * the same coefficients as in S3Profile(n,2).
 * At odd p all Sylow elements are even. An order-p S_n class splits only
 * when j=1 and n=p or p+1. Here the Sylow group is cyclic and its p-1
 * nonidentity elements are equally divided between the two A_n classes.
 * Thus the two half-sized classes contribute
 *   2*((p-1)/2)^2/(S3ClassSize(n,p,1)/2),
 * exactly the unsplit S_n term. There is no extra factor of two or four.
 */
function S3AlternatingCost(n, p)
    assert n ge 5 and IsPrime(p);
    if p ne 2 then
        return S3SymmetricCost(n, p);
    end if;
    profile := S3Profile(n, 2);
    cost := Rationals()!0;
    for j in [1..n div 2] do
        if IsEven(j) then
            cost +:= Coefficient(profile, j)^2 / S3ClassSize(n, 2, j);
        end if;
    end for;
    return cost;
end function;

/* Matching refinement used at n=14,16.
 * Put m=n/2. Each Sylow 2-subgroup contains a matching flip group of
 * order 2^m, with binomial(m,j) involutions of type 2^j. Two matching
 * flip groups have a nonidentity common element only if they share an
 * edge transposition. Therefore replace their full expected nonidentity
 * intersection by the expected number of common edge transpositions:
 *   Q_2 <= sum_j a(n,2,j)^2/C(n,2,j)
 *          - sum_j binomial(m,j)^2/C(n,2,j) + m^2/C(n,2,1).
 * The argument also applies to two independently prescribed Sylows.
 * The return value includes the cyclic costs at every odd prime.
 */
function S3MatchingCost(n)
    assert n ge 2 and IsEven(n);
    m := n div 2;
    cost := &+[ Rationals() | S3SymmetricCost(n,p) : p in PrimesUpTo(n) ];
    for j in [1..m] do
        cost -:= Binomial(m,j)^2 / S3ClassSize(n,2,j);
    end for;
    return cost + m^2/S3ClassSize(n,2,1);
end function;

/* The paper's M(n,p), without the cyclic improvement factor 1/(p-1). */
function S3Majorant(n, p)
    assert n ge 0 and IsPrime(p);
    m := n div p;
    cost := Rationals()!0;
    for j in [1..m] do
        coefficientBound := (p-1)^j*Binomial(m+j-1,j);
        cost +:= coefficientBound^2/S3ClassSize(n,p,j);
    end for;
    return cost;
end function;

/* The paper's M_ev(n), again without any alternating-group factor. */
function S3EvenMajorant(n)
    assert n ge 0;
    m := n div 2;
    cost := Rationals()!0;
    for j in [1..m] do
        if IsEven(j) then
            cost +:= Binomial(m+j-1,j)^2/S3ClassSize(n,2,j);
        end if;
    end for;
    return cost;
end function;

/* Independent group-theoretic validation, intended for lo=5, hi=12.
 * First compute profile coefficients from actual conjugacy classes of
 * Magma's Sylow subgroups. Then fuse actual Sylow classes into actual
 * A_n classes and compare the resulting cyclic class sum. This checks
 * split classes as well as the wreath recurrence and the parity filter.
 * No enumeration of all elements of S_n or A_n is required.
 */
procedure S3ValidateProfiles(lo, hi)
    assert 5 le lo and lo le hi;
    checks := 0;
    for n in [lo..hi] do
        S := Sym(n);
        A := Alt(n);
        alternatingClasses := Classes(A);
        for p in PrimesUpTo(n) do
            expected := S3Profile(n,p);
            observed := Parent(expected)!1;
            X := Parent(expected).1;
            P := Sylow(S,p);
            for c in Classes(P) do
                if c[1] eq p then
                    j := #Support(c[3]) div p;
                    observed +:= c[2]*X^j;
                end if;
            end for;
            assert observed eq expected;

            primeClasses := [ c : c in alternatingClasses | c[1] eq p ];
            counts := [ Integers() | 0 : c in primeClasses ];
            Q := Sylow(A,p);
            for c in Classes(Q) do
                if c[1] eq p then
                    matches := [ i : i in [1..#primeClasses] |
                        IsConjugate(A, A!c[3], primeClasses[i][3]) ];
                    assert #matches eq 1;
                    counts[matches[1]] +:= c[2];
                end if;
            end for;
            actualCost := &+[ Rationals() |
                counts[i]^2/primeClasses[i][2]/(p-1) :
                i in [1..#primeClasses] ];
            assert actualCost eq S3AlternatingCost(n,p);
            checks +:= 1;
        end for;
        printf "PROFILE_VALIDATION n=%o status=PASS\n", n;
    end for;
    printf "PROFILE_VALIDATION degrees=%o..%o prime_cases=%o status=PASS\n",
        lo, hi, checks;
end procedure;
