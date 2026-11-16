# Exact contraction by backtracking over the internal edges.  A vertex is evaluated as soon as
# all its ports are assigned, and a zero factor prunes the branch.  This computes the same sum
# as `contract` in common.jl, and is fast on networks built from equality and gate tensors.

function contract_bt(N::Net, a::Vector{Int}=Int[])
    @assert length(a) == length(N.legs)
    x = fill(-1, N.nedges)
    for (j, e) in enumerate(N.legs)
        x[e] = a[j]
    end
    internal = setdiff(1:N.nedges, N.legs)
    # order the internal edges by a breadth-first sweep over vertices
    inc = [Int[] for _ in 1:N.nedges]
    for (vi, v) in enumerate(N.verts), e in v.ports
        push!(inc[e], vi)
    end
    order = Int[]
    seen = falses(N.nedges)
    for v in N.verts, e in v.ports
        if !seen[e] && !(e in N.legs)
            seen[e] = true
            push!(order, e)
        end
    end
    # vertices that become complete after assigning order[k]
    pos = Dict(e => k for (k, e) in enumerate(order))
    done_at = [Int[] for _ in 0:length(order)]
    for (vi, v) in enumerate(N.verts)
        k = 0
        for e in v.ports
            haskey(pos, e) && (k = max(k, pos[e]))
        end
        push!(done_at[k + 1], vi)
    end
    pre = big(1)
    for vi in done_at[1]
        v = N.verts[vi]
        pre *= v.T([x[e] for e in v.ports])
    end
    pre == 0 && return big(0)
    function rec(k)
        k > length(order) && return big(1)
        e = order[k]
        tot = big(0)
        for b in 0:1
            x[e] = b
            p = big(1)
            for vi in done_at[k + 1]
                v = N.verts[vi]
                p *= v.T([x[q] for q in v.ports])
                p == 0 && break
            end
            p == 0 && continue
            tot += p * rec(k + 1)
        end
        x[e] = -1
        return tot
    end
    return pre * rec(1)
end

# ---------------------------------------------------------------- network builders

"Mutable builder for networks."
mutable struct Builder
    nedges::Int
    verts::Vector{Vertex}
    legs::Vector{Int}
end
Builder() = Builder(0, Vertex[], Int[])
newedge!(B::Builder) = (B.nedges += 1; B.nedges)
addv!(B::Builder, ports, T) = push!(B.verts, Vertex(collect(ports), T))
net(B::Builder) = Net(B.nedges, B.verts, B.legs)

eqT(bits) = all(==(bits[1]), bits) ? 1 : 0

"""
Join the occurrences of one signal by an equality tree (Lemma 3.3 of the paper).  `occ` is a
list of edge ids, one per occurrence, each already attached at its other end; `leg` says
whether one extra occurrence is a leg (returned).  Returns the leg edge or 0.
"""
function eqtree!(B::Builder, occ::Vector{Int}; leg::Bool=false)
    ends = copy(occ)
    legedge = 0
    if leg
        legedge = newedge!(B)
        push!(ends, legedge)
        push!(B.legs, legedge)
    end
    d = length(ends)
    if d == 1
        addv!(B, ends, b -> 1)
    elseif d == 2
        addv!(B, ends, eqT)
    else
        # caterpillar of ternary equality vertices
        cur = ends[1]
        for k in 2:(d - 1)
            nxt = (k == d - 1) ? ends[d] : newedge!(B)
            addv!(B, [cur, ends[k], nxt], eqT)
            cur = nxt
        end
    end
    return legedge
end
