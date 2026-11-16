# Lemmas 3.3, 3.5 and 3.6: circuits, unambiguous circuits and gap pairs as gate networks.

function check_circuit(rng)
    println("Circuits as gate networks (Lemma 3.3)")
    ok_val = true
    ok_size = true
    for trial in 1:60
        m = rand(rng, 1:4)
        C = random_circuit(rng, m, rand(rng, 1:5))
        B = circuit_net(C)
        N = net(B)
        ok_size &= N.nedges <= 2m + 4wires(C) + 6
        for i in 0:(2^m - 1)
            a = bitsof(i, m)
            ok_val &= contract_bt(N, a) == evalc(C, a)[C.out]
        end
    end
    check("Z(a) = C(a) for 60 random circuits of table and weighted gates", ok_val)
    check("size at most 2N + 4W + 6", ok_size)

    println("Unambiguous circuits (Lemma 3.5)")
    ok = true
    for trial in 1:40
        m = rand(rng, 1:3)                   # inputs a
        M = rand(rng, 1:3)                   # guess bits y
        # y must equal F(a) and G(a) must hold: at most one witness for every a
        Ftab = [rand(rng, 0:(2^M - 1)) for _ in 1:2^m]
        Gtab = rand(rng, 0:1, 2^m)
        idx(bits) = 1 + sum(bits[i] << (i - 1) for i in 1:length(bits); init=0)
        gates = Gate[]
        # gate: [ y == F(a) and G(a) ] as one table gate on all m + M inputs
        push!(gates, Gate(collect(1:(m + M)),
              bits -> (Gtab[idx(bits[1:m])] == 1 &&
                       idx(bits[(m + 1):end]) - 1 == Ftab[idx(bits[1:m])]) ? 1 : 0))
        C = Circuit(m + M, gates, m + M + 1)
        legmask = vcat(trues(m), falses(M))
        N = net(circuit_net(C; legmask=legmask))
        ok &= N.nedges <= 2m + 2M + 4wires(C) + 6
        for i in 0:(2^m - 1)
            a = bitsof(i, m)
            ok &= contract_bt(N, a) == Gtab[i + 1]
        end
    end
    check("unambiguous circuits: the network counts the unique witness", ok)

    println("Exact-kappa ambiguity")
    ok = true
    for trial in 1:30
        m = rand(rng, 1:3); M = rand(rng, 2:3)
        κ = rand(rng, 1:2^(M - 1))
        Gtab = rand(rng, 0:1, 2^m)
        idx(bits) = 1 + sum(bits[i] << (i - 1) for i in 1:length(bits); init=0)
        # accept (a,y) iff G(a) and val(y) < kappa
        gates = [Gate(collect(1:(m + M)),
                      bits -> (Gtab[idx(bits[1:m])] == 1 && idx(bits[(m + 1):end]) - 1 < κ) ? 1 : 0)]
        C = Circuit(m + M, gates, m + M + 1)
        N = net(circuit_net(C; legmask=vcat(trues(m), falses(M))))
        for i in 0:(2^m - 1)
            ok &= contract_bt(N, bitsof(i, m)) == κ * Gtab[i + 1]
        end
    end
    check("circuits with 0 or kappa witnesses: Z = kappa * W", ok)

    println("Gap pairs with a switch edge (Lemma 3.6)")
    ok = true
    for trial in 1:30
        m = rand(rng, 1:3)
        Mp = rand(rng, 1:3); Mm = rand(rng, 1:3)
        idx(bits) = 1 + sum(bits[i] << (i - 1) for i in 1:length(bits); init=0)
        Wtab = rand(rng, 0:1, 2^m)
        Btab = [rand(rng, 0:(min(2^Mp, 2^Mm) - 1)) for _ in 1:2^m]
        Atab = Btab .+ Wtab
        # make A <= 2^Mp
        Atab = min.(Atab, 2^Mp)
        Wt = Atab .- Btab
        Cp = Circuit(m + Mp, [Gate(collect(1:(m + Mp)),
                 bits -> idx(bits[(m + 1):end]) - 1 < Atab[idx(bits[1:m])] ? 1 : 0)], m + Mp + 1)
        Cm = Circuit(m + Mm, [Gate(collect(1:(m + Mm)),
                 bits -> idx(bits[(m + 1):end]) - 1 < Btab[idx(bits[1:m])] ? 1 : 0)], m + Mm + 1)
        # one network: both circuits, a switch edge c between the two pins, joined legs
        B = Builder()
        c = newedge!(B)
        function graft!(B, C, legmask, pinT)
            nsig = C.m + length(C.gates)
            occ = [Int[] for _ in 1:nsig]
            for (k, G) in enumerate(C.gates)
                ins = Int[]
                for p in G.preds
                    e = newedge!(B); push!(ins, e); push!(occ[p], e)
                end
                z = newedge!(B); push!(occ[C.m + k], z)
                g = G.g; f = length(ins)
                addv!(B, vcat(ins, [z]), bits -> (bits[end] == g(bits[1:f]) ? 1 : 0))
            end
            e = newedge!(B); push!(occ[C.out], e)
            addv!(B, [e, c], pinT)
            # inputs a: leave one dangling edge per input, to be joined later
            dang = Int[]
            for σ in 1:nsig
                if σ <= C.m && legmask[σ]
                    d = newedge!(B); push!(dang, d)
                    eqtree!(B, vcat(occ[σ], [d]))
                elseif !isempty(occ[σ])
                    eqtree!(B, occ[σ])
                end
            end
            return dang
        end
        pinp(b) = b[2] == 0 ? (b[1] == 1 ? 1 : 0) : 2^Mm
        pinm(b) = b[2] == 0 ? 2^Mp : (b[1] == 1 ? -1 : 0)
        dp = graft!(B, Cp, vcat(trues(m), falses(Mp)), pinp)
        dm = graft!(B, Cm, vcat(trues(m), falses(Mm)), pinm)
        for j in 1:m
            l = newedge!(B); push!(B.legs, l)
            addv!(B, [l, dp[j], dm[j]], eqT)
        end
        N = net(B)
        κ = 2^(Mp + Mm)
        for i in 0:(2^m - 1)
            ok &= contract_bt(N, bitsof(i, m)) == κ * Wt[i + 1]
        end
    end
    check("gap pairs: Z = 2^(M+ + M-) (A - B)", ok)
end
