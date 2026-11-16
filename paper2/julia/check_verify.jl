# Lemma 4.1 (verification networks): the power sums and the clause count.

"Add a renamed copy of N to B; return the list of its (now dangling) leg edges."
function graft_copy!(B::Builder, N::Net)
    ren = Dict{Int,Int}()
    for e in 1:N.nedges
        ren[e] = newedge!(B)
    end
    for v in N.verts
        addv!(B, [ren[e] for e in v.ports], v.T)
    end
    return [ren[e] for e in N.legs]
end

capT(t0, t1) = b -> (b[1] == 0 ? t0 : t1)

"Closed network with value sum_a Z(a)^r."
function power_net(N::Net, r::Int)
    B = Builder()
    L = [graft_copy!(B, N) for _ in 1:r]
    for j in 1:length(N.legs)
        ends = [L[k][j] for k in 1:r]
        if r == 1
            addv!(B, ends, capT(1, 1))
        else
            addv!(B, ends, eqT)
        end
    end
    return net(B)
end

function random_open_net(rng, nlegs; ninternal=3, maxent=3)
    B = Builder()
    legs = [newedge!(B) for _ in 1:nlegs]
    B.legs = copy(legs)
    internal = [newedge!(B) for _ in 1:ninternal]
    # two vertices: each internal edge joins them; legs spread over both
    split = rand(rng, 0:nlegs)
    p1 = vcat(legs[1:split], internal)
    p2 = vcat(legs[(split + 1):end], internal)
    t1 = rand(rng, -maxent:maxent, 2^length(p1))
    t2 = rand(rng, -maxent:maxent, 2^length(p2))
    idx(bits) = 1 + sum(bits[i] << (i - 1) for i in 1:length(bits); init=0)
    addv!(B, p1, bits -> t1[idx(bits)])
    addv!(B, p2, bits -> t2[idx(bits)])
    return net(B)
end

"Open network with a prescribed tensor kappa * g on nlegs legs (one table vertex)."
function table_net(vals::Vector{Int}, nlegs)
    B = Builder()
    legs = [newedge!(B) for _ in 1:nlegs]
    B.legs = copy(legs)
    idx(bits) = 1 + sum(bits[i] << (i - 1) for i in 1:length(bits); init=0)
    addv!(B, legs, bits -> vals[idx(bits)])
    return net(B)
end

function decoder_circuit(rng, q, v, w)
    # outputs: lambda_1..3 (v bits each) then eps_1..3, each a table gate of fan-in <= w
    gates = Gate[]
    for o in 1:(3v + 3)
        f = rand(rng, 0:min(w, q))
        preds = sort(unique(rand(rng, 1:q, f)))
        push!(gates, random_table_gate(rng, preds))
    end
    return Circuit(q, gates, 0)
end

"The networks V_S of Lemma 4.1; returns sum_S Z(V_S)."
function vs_sum(Dc::Circuit, N::Net, v::Int, κ::Int)
    q = Dc.m
    tot = big(0)
    for S in 0:7
        B = Builder()
        nsig = q + length(Dc.gates)
        occ = [Int[] for _ in 1:nsig]
        for (k, G) in enumerate(Dc.gates)
            ins = Int[]
            for p in G.preds
                e = newedge!(B); push!(ins, e); push!(occ[p], e)
            end
            z = newedge!(B); push!(occ[q + k], z)
            g = G.g; f = length(ins)
            addv!(B, vcat(ins, [z]), bits -> (bits[end] == g(bits[1:f]) ? 1 : 0))
        end
        outleg = Dict{Int,Int}()
        for σ in 1:nsig
            if σ > q
                d = newedge!(B)
                outleg[σ - q] = d
                eqtree!(B, vcat(occ[σ], [d]))
            elseif !isempty(occ[σ])
                eqtree!(B, occ[σ])
            end
        end
        for t in 1:3
            lam = [outleg[(t - 1) * v + j] for j in 1:v]
            eps = outleg[3v + t]
            if (S >> (t - 1)) & 1 == 1
                L = graft_copy!(B, N)
                for j in 1:v
                    addv!(B, [lam[j], L[j]], eqT)
                end
                for j in (v + 1):length(L)
                    addv!(B, [L[j]], capT(1, 0))
                end
                addv!(B, [eps], capT(1, -1))
            else
                for j in 1:v
                    addv!(B, [lam[j]], capT(1, 1))
                end
                addv!(B, [eps], capT(0, κ))
            end
        end
        tot += contract_bt(net(B))
    end
    return tot
end

function check_verify(rng)
    println("Power sums by gluing copies (Lemma 4.1(1))")
    ok = true
    for trial in 1:20
        nl = rand(rng, 1:3)
        N = random_open_net(rng, nl)
        Zs = [contract_bt(N, bitsof(i, nl)) for i in 0:(2^nl - 1)]
        for r in 1:4
            ok &= contract_bt(power_net(N, r)) == sum(Zs .^ r)
        end
    end
    check("glued copies give sum_a Z(a)^r for r = 1..4", ok)

    ok = true
    for trial in 1:200
        κ = rand(rng, 1:4)
        z = rand(rng, -6:10)
        val = z^2 * (z - κ)^2
        ok &= val >= 0 && ((val == 0) == (z == 0 || z == κ))
    end
    check("z^2 (z - kappa)^2 >= 0 with equality iff z in {0, kappa}", ok)

    println("Clause count (Lemma 4.1(2))")
    ok_gen = true
    ok_bool = true
    for trial in 1:12
        q = rand(rng, 2:3); v = 1; w = 2; Nl = 2
        Dc = decoder_circuit(rng, q, v, w)
        used = falses(q)
        for G in Dc.gates, p in G.preds
            used[p] = true
        end
        u = q - count(used)
        κ = rand(rng, 1:3)
        # (a) a general network: the identity with products of affine factors
        N = random_open_net(rng, Nl; ninternal=1, maxent=2)
        Z(lam) = contract_bt(N, vcat(lam, zeros(Int, Nl - v)))
        expect = big(0)
        for i in 0:(2^q - 1)
            val = evalc(Dc, bitsof(i, q))[(q + 1):end]
            p = big(1)
            for t in 1:3
                lam = val[((t - 1) * v + 1):(t * v)]
                ε = val[3v + t]
                p *= κ * ε + (1 - 2ε) * Z(lam)
            end
            expect += p
        end
        ok_gen &= vs_sum(Dc, N, v, κ) * 2^u == expect
        # (b) a network with values in {0, kappa}: kappa^3 times the number of violated clauses
        gvals = rand(rng, 0:1, 2^Nl)
        Nb = table_net(κ .* gvals, Nl)
        viol = 0
        for i in 0:(2^q - 1)
            val = evalc(Dc, bitsof(i, q))[(q + 1):end]
            allfalse = true
            for t in 1:3
                lam = val[((t - 1) * v + 1):(t * v)]
                ε = val[3v + t]
                X = gvals[1 + sum(lam[j] << (j - 1) for j in 1:v)]     # padded label lam 0
                allfalse &= (X == 1 - ε)
            end
            viol += allfalse
        end
        ok_bool &= vs_sum(Dc, Nb, v, κ) * 2^u == κ^3 * viol
    end
    check("sum_S Z(V_S) = 2^-u sum_i prod_t (kappa eps_t + (1-2eps_t) Z(lambda_t))", ok_gen)
    check("for values in {0,kappa}: sum_S Z(V_S) = 2^-u kappa^3 #violated clauses", ok_bool)
end
