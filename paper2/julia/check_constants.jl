# Constants and parameter inequalities of Theorems 3.9 and 4.3.

function check_constants()
    println("Constants")
    clog2(x) = x <= 1 ? 0 : 64 - leading_zeros(x - 1)
    # Theorem 3.9: 1872 C + 64 with C = 18
    check("1872*18 + 64 = 33760", 1872 * 18 + 64 == 33760)
    # c(delta) = sqrt(delta) / (2*10^6) satisfies 4 c(delta) < 1 / (10 A_1(delta)),
    # A_1(delta) = 33760 sqrt(2) / sqrt(delta):  equivalent to 4 * 10 * 33760 * sqrt(2) < 2*10^6
    check("4 * 10 * 33760 * sqrt(2) < 2 * 10^6", 4 * 10 * 33760 * sqrt(2) < 2e6)
    check("same inequality in integers: (1350400)^2 * 2 < (2*10^6)^2",
          big(1350400)^2 * 2 < big(2_000_000)^2)

    # Step 1 of Theorem 3.9: with K = floor(s^(1-delta)/4) and beta* = K - ceil(log s) - 3,
    # b <= b' <= K, block degree <= 2K, chain degree <= 3K <= s^(1-delta) for every f <= s.
    ok = true
    for δ in (0.05, 0.1, 0.25, 0.5), s in (2^14, 2^16, 2^20, 2^24, 2^30)
        K = floor(Int, s^(1 - δ) / 4)
        βs = K - clog2(s) - 3
        βs >= 1 || continue
        for f in (K + 1, 2K, s)
            b = βs + clog2(K) + 2
            bp = βs + clog2(f) + 3
            ok &= b <= bp <= K && K + b <= 2K && b + 2bp <= 3K && 3K <= s^(1 - δ)
        end
    end
    check("chain parameters: b <= b' <= K and degrees <= 3K <= s^(1-delta)", ok)

    # Theorem 4.3: (2n)^(1-delta) <= beta*_{delta/2}(s') for s' >= n: first n where it holds
    for δ in (0.1, 0.25, 0.5, 0.9)
        n0 = 0
        for e in 8:200
            n = 2.0^e
            K = floor(n^(1 - δ / 2) / 4)
            if (2n)^(1 - δ) <= K - ceil(log2(n)) - 3
                n0 = e; break
            end
        end
        check("weights fit the chain for n >= 2^$n0 at delta = $δ", n0 > 0)
    end
end
