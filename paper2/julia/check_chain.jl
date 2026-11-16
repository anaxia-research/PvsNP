# Lemma 3.8 (chain encoding of a weighted vertex) and the exactness of contraction mod 2^(s+2).

clog2(x) = x <= 1 ? 0 : 64 - leading_zeros(x - 1)

"Tensor of the chain sub-network on (y, z), summed over all internal values by dynamic programming."
function chain_tensor(w::Vector{Int}, φ::Function, β::Int, K::Int, y::Vector{Int}, z::Int)
    f = length(w)
    k = cld(f, K)
    b = β + clog2(K) + 2
    bp = β + clog2(f) + 3
    off = K * 2^β
    blocks = [((j - 1) * K + 1):min(j * K, f) for j in 1:k]
    P = [sum(w[i] * y[i] for i in blocks[j]; init=0) for j in 1:k]
    # each block vertex admits exactly the e_j in [0, 2^b) with e_j = P_j + off
    evals = [0 <= P[j] + off < 2^b ? [P[j] + off] : Int[] for j in 1:k]
    if k == 1
        tot = 0
        for e in evals[1]
            tot += (z == φ(e - off)) ? 1 : 0
        end
        return tot
    end
    ways = Dict{Int,Int}(0 => 1)              # R_0 = 0
    for j in 1:(k - 1)
        nw = Dict{Int,Int}()
        for (R, c) in ways, e in evals[j]
            Rn = R + e
            0 <= Rn < 2^bp || continue
            nw[Rn] = get(nw, Rn, 0) + c
        end
        ways = nw
    end
    tot = 0
    for (R, c) in ways, e in evals[k]
        tot += c * ((z == φ(R + e - k * off)) ? 1 : 0)
    end
    return tot
end

function check_chain(rng)
    println("Chain encoding of weighted vertices (Lemma 3.8)")
    ok = true
    okrange = true
    for trial in 1:300
        f = rand(rng, 1:9)
        β = rand(rng, 0:3)
        K = rand(rng, 1:4)
        w = rand(rng, -2^β:2^β, f)
        kind = rand(rng, 1:3)
        θ = rand(rng, -f * 2^β:f * 2^β)
        μ = rand(rng, 1:2^max(β, 1))
        φ = kind == 1 ? (v -> v >= θ ? 1 : 0) : kind == 2 ? (v -> v == θ ? 1 : 0) :
            (v -> mod(v - θ, μ) == 0 ? 1 : 0)
        for t in 1:12
            y = rand(rng, 0:1, f)
            z = rand(rng, 0:1)
            want = (z == φ(sum(w .* y))) ? 1 : 0
            ok &= chain_tensor(w, φ, β, K, y, z) == want
        end
        # ranges of the block values and partial sums
        k = cld(f, K)
        b = β + clog2(K) + 2
        bp = β + clog2(f) + 3
        if f > K
            okrange &= 2K * 2^β < 2^b && 2 * (k - 1) * K * 2^β < 2f * 2^β < 2^bp
        end
    end
    check("chain sub-network has the tensor [z = phi(sum w_i y_i)] (300 random gates)", ok)
    check("block values < 2^b and partial sums < 2^b'", okrange)

    println("Exact recovery from the residue mod 2^(s+2)")
    ok = true
    for trial in 1:2000
        s = rand(rng, 1:40)
        Z = rand(rng, -big(2)^s:big(2)^s)
        r = mod(Z, big(2)^(s + 2))
        rec = r > big(2)^(s + 1) ? r - big(2)^(s + 2) : r
        ok &= rec == Z
    end
    check("|Z| <= 2^s is recovered from Z mod 2^(s+2)", ok)
end
