/-
The treewidth theorem (Section 5): the orientation step of the balanced-bag lemma, and the
final inequality.
-/
import Mathlib

namespace PvsNP2

open Finset

/-- Orientation step of Lemma 5.2.  If every node of a finite tree points to a neighbour, some
edge is pointed at from both ends: there is `v` with `φ (φ v) = v`. -/
theorem tree_orientation_has_two_cycle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hT : G.IsTree)
    (φ : V → V) (hφ : ∀ v, G.Adj v (φ v)) : ∃ v, φ (φ v) = v := by
  classical
  -- the map `v ↦ {v, φ v}` from nodes to edges
  let f : V → G.edgeFinset := fun v => ⟨s(v, φ v), by simpa using hφ v⟩
  have hcard : Fintype.card G.edgeFinset < Fintype.card V := by
    have h := hT.card_edgeFinset
    have hpos : 0 < Fintype.card V := by
      have : Nonempty V := hT.1.nonempty
      exact Fintype.card_pos
    simp only [Fintype.card_coe]
    omega
  obtain ⟨v, w, hne, hvw⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hs : s(v, φ v) = s(w, φ w) := congrArg Subtype.val hvw
  rcases Sym2.eq_iff.mp hs with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact absurd h1 hne
  · exact ⟨w, by rw [← h1]; exact h2⟩

/-- The final inequality of Theorem 5.3: from `∑ μᵢ ≥ c (f - ℓ)`, `∑ μᵢ + ℓ ≤ D`, `ℓ ≥ 0` and
`c ≤ 1` one gets `D ≥ c f`. -/
theorem final_inequality (μ ℓ D f c : ℝ) (hc : c ≤ 1) (hℓ : 0 ≤ ℓ)
    (h1 : c * (f - ℓ) ≤ μ) (h2 : μ + ℓ ≤ D) : c * f ≤ D := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) hℓ]

/-- For the cube `Q_k`, `c_G = min(1/4, 1/(k+1)) / (2k²) = 1/(2k²(k+1)) ≥ 1/(4k³)`. -/
theorem cube_constant (k : ℕ) (hk : 3 ≤ k) :
    (1 : ℝ) / (4 * k ^ 3) ≤ min (1 / 4) (1 / ((k : ℝ) + 1)) / (2 * k ^ 2) := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hmin : min (1 / 4 : ℝ) (1 / ((k : ℝ) + 1)) = 1 / ((k : ℝ) + 1) := by
    apply min_eq_right
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  rw [hmin, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (k : ℝ)]

end PvsNP2
