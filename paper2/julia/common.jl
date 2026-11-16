# Shared definitions for the checks of
# "Superlinear Lower Bounds for Unambiguous Circuits and Integer Tensor Networks".
#
# An open tensor network is stored as a list of vertices.  Each vertex has a list of ports,
# each port naming an edge (an integer), and a tensor given as a function of the bits on its
# ports.  Legs are edges that occur at exactly one port; their values are fixed from outside.

using Random

struct Vertex
    ports::Vector{Int}                  # edge ids, in port order
    T::Function                         # Vector{Int} (bits on ports) -> Int
end

struct Net
    nedges::Int
    verts::Vector{Vertex}
    legs::Vector{Int}                   # ordered list of leg edges
end

"Contraction Z(a) by summation over all internal edge assignments."
function contract(N::Net, a::Vector{Int}=Int[])
    @assert length(a) == length(N.legs)
    internal = setdiff(1:N.nedges, N.legs)
    x = zeros(Int, N.nedges)
    for (j, e) in enumerate(N.legs)
        x[e] = a[j]
    end
    Z = big(0)
    for mask in 0:(big(2)^length(internal) - 1)
        for (k, e) in enumerate(internal)
            x[e] = Int((mask >> (k - 1)) & 1)
        end
        p = big(1)
        for v in N.verts
            p *= v.T([x[e] for e in v.ports])
            p == 0 && break
        end
        Z += p
    end
    return Z
end

bitsof(i, n) = [Int((i >> (k - 1)) & 1) for k in 1:n]

"Size of a gate network: edges plus the bit lengths b_v of integer tables."
function netsize(N::Net, tablebits::Int=0)
    return N.nedges + tablebits
end

mutable struct Tally
    pass::Int
    fail::Int
end
const TALLY = Tally(0, 0)

function check(name::AbstractString, ok::Bool)
    if ok
        TALLY.pass += 1
        println("  pass  ", name)
    else
        TALLY.fail += 1
        println("  FAIL  ", name)
    end
end
