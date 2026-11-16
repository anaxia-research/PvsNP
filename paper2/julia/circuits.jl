# Circuits and their gate networks (Lemmas 3.3-3.6 of the paper).

struct Gate
    preds::Vector{Int}           # signal ids (inputs are 1..m, gate k is signal m+k)
    g::Function                  # Vector{Int} -> Int (0/1)
end

struct Circuit
    m::Int
    gates::Vector{Gate}
    out::Int                     # signal id of the output
end

function evalc(C::Circuit, x::Vector{Int})
    val = zeros(Int, C.m + length(C.gates))
    val[1:C.m] = x
    for (k, G) in enumerate(C.gates)
        val[C.m + k] = G.g([val[p] for p in G.preds])
    end
    return val
end

wires(C::Circuit) = sum(length(G.preds) for G in C.gates; init=0)

"""
Gate network of a circuit.  `legmask[i]` says whether input i carries a leg (inputs without a
leg are summed over, as guess bits).  `pin` is the tensor on the output occurrence, or
`nothing` for no pin.  Returns (builder, output-occurrence edge or 0).
"""
function circuit_net(C::Circuit; legmask=trues(C.m), pin=b -> b[1] == 1 ? 1 : 0,
                     extra_pin_ports::Vector{Int}=Int[])
    B = Builder()
    nsig = C.m + length(C.gates)
    occ = [Int[] for _ in 1:nsig]
    for (k, G) in enumerate(C.gates)
        ins = Int[]
        for p in G.preds
            e = newedge!(B)
            push!(ins, e)
            push!(occ[p], e)
        end
        z = newedge!(B)
        push!(occ[C.m + k], z)
        g = G.g
        f = length(ins)
        addv!(B, vcat(ins, [z]), bits -> (bits[end] == g(bits[1:f]) ? 1 : 0))
    end
    if pin !== nothing
        e = newedge!(B)
        push!(occ[C.out], e)
        addv!(B, vcat([e], extra_pin_ports), pin)
    end
    legs = Int[]
    for σ in 1:nsig
        isleg = σ <= C.m && legmask[σ]
        if isempty(occ[σ]) && !isleg
            continue                       # an unused guess input: dropped
        end
        eqtree!(B, occ[σ]; leg=isleg)
    end
    return B
end

# ------------------------------------------------------------- random circuits

function random_table_gate(rng, preds)
    f = length(preds)
    tbl = rand(rng, 0:1, 2^f)
    return Gate(preds, bits -> tbl[1 + sum(bits[i] << (i - 1) for i in 1:f; init=0)])
end

function random_weighted_gate(rng, preds, β)
    f = length(preds)
    w = rand(rng, -2^β:2^β, f)
    kind = rand(rng, 1:4)
    θ = rand(rng, -f * 2^β:f * 2^β)
    μ = rand(rng, 1:2^β)
    if kind == 1
        φ = v -> v >= θ ? 1 : 0
    elseif kind == 2
        φ = v -> v == θ ? 1 : 0
    elseif kind == 3
        φ = v -> mod(v - θ, μ) == 0 ? 1 : 0
    else
        w = ones(Int, f)
        tb = rand(rng, 0:1, f + 1)
        φ = v -> tb[v + 1]
    end
    return Gate(preds, bits -> φ(sum(w[i] * bits[i] for i in 1:f; init=0)))
end

function random_circuit(rng, m, ngates; F=3, β=2, maxfan=5)
    gates = Gate[]
    for k in 1:ngates
        nsig = m + k - 1
        if rand(rng) < 0.6
            f = rand(rng, 1:min(F, nsig))
            preds = rand(rng, 1:nsig, f)
            push!(gates, random_table_gate(rng, preds))
        else
            f = rand(rng, 1:min(maxfan, nsig))
            preds = rand(rng, 1:nsig, f)
            push!(gates, random_weighted_gate(rng, preds, β))
        end
    end
    return Circuit(m, gates, m + ngates)
end
