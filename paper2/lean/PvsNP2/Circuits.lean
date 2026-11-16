/-
Circuits as networks (Lemmas 3.3-3.6): the counting identities behind them.
-/
import Mathlib

namespace PvsNP2

open Finset

/-- An unambiguous nondeterministic circuit has `0` or `1` accepting guesses. -/
theorem unambiguous_count {Y : Type*} [Fintype Y] (p : Y → Prop) [DecidablePred p]
    (h : (univ.filter p).card ≤ 1) : (univ.filter p).card = 0 ∨ (univ.filter p).card = 1 := by
  omega

/-- Size of a circuit network: with `G ≤ W + 2` gates, `2 (N + G + W + 1) ≤ 2N + 4W + 6`. -/
theorem circuit_size (N G W : ℕ) (hG : G ≤ W + 2) : 2 * (N + G + W + 1) ≤ 2 * N + 4 * W + 6 := by
  omega

/-- Unambiguous version: `M` more signals without legs. -/
theorem unambiguous_size (N M G W : ℕ) (hG : G ≤ W + 2) :
    2 * (N + M + G + W + 1) ≤ 2 * N + 2 * M + 4 * W + 6 := by
  omega

/-- The switch of Lemma 3.6: with pin constants `2^(m⁺)` and `2^(m⁻)` the two branches combine to
`2^(m⁺ + m⁻) (A - B)`. -/
theorem gap_switch (A B : ℤ) (mp mm : ℕ) :
    A * (2 ^ mp * 2 ^ mm) + (2 ^ mm * 2 ^ mp) * (-B) = 2 ^ (mp + mm) * (A - B) := by
  rw [pow_add]; ring

/-- An equality tree on `d` occurrences has at most `2d` edges (`d` leaf edges, `d - 3` inner). -/
theorem eqtree_edges (d : ℕ) (hd : 3 ≤ d) : d + (d - 3) ≤ 2 * d := by omega

end PvsNP2
