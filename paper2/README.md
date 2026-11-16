# Superlinear Lower Bounds for Unambiguous Circuits and Integer Tensor Networks

**Deep Bhattacharjee**

Checks for the second paper of the series. It cites the first paper,
[doi:10.20944/preprints202611.0576.v2](https://doi.org/10.20944/preprints202611.0576.v2).

| Proved | Open |
| :--- | :--- |
| For every δ > 0 and infinitely many N, no integer tensor network of degree N<sup>1−δ</sup> and size c(δ) N √log N contracts to a positive multiple of the E<sup>NP</sup> language W | P versus NP |
| Consequences for unambiguous circuits, circuits with a fixed number of witnesses, gap pairs and multi-output gates | Ambiguous nondeterministic circuits |
| Bounded-treewidth encodings of exact gates need (treewidth + 1) × degree ≥ f / (4 log³ f) (unconditional) | Bounds beyond N √log N by this method |

| Folder | Contents | Run |
| :--- | :--- | :--- |
| [`lean/`](lean) | Lean 4 over Mathlib, 28 theorems, axiom audit | `cd lean && lake exe cache get && lake build && lake env lean audit.lean` |
| [`julia/`](julia) | 26 exhaustive checks on small networks | `julia julia/run_all.jl` |

Contact: egspl@proton.me.
