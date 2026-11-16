# The gate I_G, its base-four weights, cut ranks, split edges and the balanced-bag lemma.

function hypercube(k)
    V = 0:(2^k - 1)
    E = Tuple{Int,Int}[]
    for x in V, i in 0:(k - 1)
        y = x ⊻ (1 << i)
        x < y && push!(E, (x + 1, y + 1))
    end
    return 2^k, E
end

"I_G as a function of (x_1..x_n, y_1..y_k)."
function IG(n, E, bits)
    x = bits[1:n]; y = bits[(n + 1):end]
    for (j, (a, b)) in enumerate(E)
        x[a] + x[b] + y[j] == 1 || return 0
    end
    return 1
end

"Rank over GF(p) of an integer matrix."
function rankmod(A::Matrix{Int}, p::Int=1_000_003)
    M = mod.(A, p)
    r = 0
    rows, cols = size(M)
    for c in 1:cols
        piv = findfirst(i -> i > r && M[i, c] != 0, 1:rows)
        piv === nothing && continue
        r += 1
        M[r, :], M[piv, :] = M[piv, :], M[r, :]
        inv = powermod(M[r, c], p - 2, p)
        M[r, :] = mod.(M[r, :] .* inv, p)
        for i in 1:rows
            if i != r && M[i, c] != 0
                M[i, :] = mod.(M[i, :] .- M[i, c] .* M[r, :], p)
            end
        end
    end
    return r
end

function cutmatrix(n, E, A::Vector{Int})
    f = n + length(E)
    Bs = setdiff(1:f, A)
    Mx = zeros(Int, 2^length(A), 2^length(Bs))
    bits = zeros(Int, f)
    for r in 0:(2^length(A) - 1), c in 0:(2^length(Bs) - 1)
        for (t, i) in enumerate(A); bits[i] = (r >> (t - 1)) & 1; end
        for (t, i) in enumerate(Bs); bits[i] = (c >> (t - 1)) & 1; end
        Mx[r + 1, c + 1] = IG(n, E, copy(bits))
    end
    return Mx
end

"Greedy induced matching of split edges (proof of Lemma 9 of [Bha26])."
function induced_split_matching(n, E, A)
    inA = falses(n + length(E)); inA[A] .= true
    split = [j for (j, (a, b)) in enumerate(E) if length(unique([inA[a], inA[b], inA[n + j]])) == 2]
    adj = [Int[] for _ in 1:n]
    for (a, b) in E; push!(adj[a], b); push!(adj[b], a); end
    blocked = falses(n)
    M = Int[]
    for j in split
        a, b = E[j]
        (blocked[a] || blocked[b]) && continue
        push!(M, j)
        for u in vcat([a, b], adj[a], adj[b]); blocked[u] = true; end
    end
    return M, length(split)
end

function check_rank(rng)
    println("The gate I_G (Section 5)")
    # base-four exact-gate identity on Q_2 and Q_3 (all inputs)
    ok = true
    for k in 2:3
        n, E = hypercube(k)
        f = n + length(E)
        wx = [sum((a in e) ? 4^(j - 1) : 0 for (j, e) in enumerate(E)) for a in 1:n]
        wy = [4^(j - 1) for j in 1:length(E)]
        θ = sum(wy)
        for i in 0:(2^f - 1)
            bits = bitsof(i, f)
            val = sum(wx .* bits[1:n]) + sum(wy .* bits[(n + 1):end])
            ok &= IG(n, E, bits) == (val == θ ? 1 : 0)
        end
        ok &= maximum(vcat(wx, wy)) < 4^length(E)
    end
    check("I_G is the exact gate with base-four weights below 4^|E| (Q_2, Q_3, all inputs)", ok)

    # rank >= 2^|M| for an induced matching of split edges, and the split-edge count
    ok = true
    okcount = true
    n, E = hypercube(3)
    f = n + length(E)
    d = 3; h = 1
    c1 = min(1 / 4, h / (d + 1))
    for trial in 1:40
        sz = rand(rng, 1:10)
        A = sort(randperm(rng, f)[1:sz])
        M, nsplit = induced_split_matching(n, E, A)
        r = rankmod(cutmatrix(n, E, A))
        ok &= r >= 2^length(M)
        okcount &= nsplit >= c1 * min(length(A), f - length(A)) - 1e-9
    end
    check("cut rank of I_{Q_3} >= 2^(induced split matching), 40 random cuts", ok)
    check("at least c_1 min(|A|,|B|) split edges (Q_3, h = 1, d = 3)", okcount)

    # edge-isoperimetric inequality e(S) <= |S| log|S| / 2 on Q_4 (all subsets of size <= 8 sampled)
    ok = true
    n4, E4 = hypercube(4)
    for trial in 1:3000
        sz = rand(rng, 1:16)
        S = Set(randperm(rng, 16)[1:sz])
        eS = count(e -> (e[1] in S) && (e[2] in S), E4)
        ok &= 2eS <= sz * log2(sz) + 1e-9
    end
    check("e(S) <= |S| log2|S| / 2 for 3000 random subsets of Q_4", ok)
end

# ------------------------------------------------------------- balanced bags

"Tree decomposition from an elimination order (bags = vertex + later neighbours)."
function tree_decomposition(n, adj, order)
    pos = invperm(order)
    g = [Set(adj[v]) for v in 1:n]
    bags = Vector{Vector{Int}}(undef, n)
    parent = zeros(Int, n)
    for v in order
        later = [u for u in g[v] if pos[u] > pos[v]]
        bags[v] = vcat([v], later)
        for a in later, b in later
            a != b && push!(g[a], b)
        end
        if !isempty(later)
            parent[v] = later[argmin([pos[u] for u in later])]
        end
    end
    return bags, parent
end

function components_without(n, adj, X)
    inX = falses(n); inX[X] .= true
    comp = zeros(Int, n); c = 0
    for s in 1:n
        (inX[s] || comp[s] != 0) && continue
        c += 1; stack = [s]; comp[s] = c
        while !isempty(stack)
            u = pop!(stack)
            for w in adj[u]
                if !inX[w] && comp[w] == 0
                    comp[w] = c; push!(stack, w)
                end
            end
        end
    end
    return comp, c
end

function check_bags(rng)
    println("Balanced bags in tree decompositions (Lemma 5.2)")
    ok = true
    okvalid = true
    for trial in 1:300
        n = rand(rng, 2:14)
        adj = [Int[] for _ in 1:n]
        for a in 1:n, b in (a + 1):n
            if rand(rng) < 0.3
                push!(adj[a], b); push!(adj[b], a)
            end
        end
        order = randperm(rng, n)
        bags, parent = tree_decomposition(n, adj, order)
        # validity: every edge in some bag
        for a in 1:n, b in adj[a]
            okvalid &= any(B -> (a in B) && (b in B), bags)
        end
        wt = rand(rng, 0:4, n)
        L = sum(wt)
        found = false
        for B in bags
            comp, c = components_without(n, adj, B)
            heavy = false
            for k in 1:c
                heavy |= 2 * sum(wt[v] for v in 1:n if comp[v] == k) > L
            end
            found |= !heavy
        end
        ok &= found
    end
    check("elimination-order tree decompositions are valid", okvalid)
    check("some bag leaves every component with at most half the weight (300 graphs)", ok)
end
