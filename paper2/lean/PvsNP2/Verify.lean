/-
The verification step (Lemma 4.1 and the proof of Theorem 4.3).

A network with `N` legs has value `Z a` on each leg assignment `a`.  The machine accepts only if
  (1) `∑ₐ Z(a)² (Z(a) - κ)² = 0`, which says that every value is `0` or `κ`, and
  (2) `∑ᵢ ∏ₜ (κ εₜ(i) + (1 - 2 εₜ(i)) Z(λₜ(i))) = 0`, which, under (1), says that no clause of
      the formula is violated by the assignment `X = Z / κ`.
-/
import Mathlib

namespace PvsNP2

open Finset

/-- `z² (z - κ)²` is nonnegative. -/
theorem sq_mul_sq_nonneg (z κ : ℤ) : 0 ≤ z ^ 2 * (z - κ) ^ 2 := by positivity

/-- `z² (z - κ)² = 0` exactly when `z ∈ {0, κ}`. -/
theorem sq_mul_sq_eq_zero_iff (z κ : ℤ) : z ^ 2 * (z - κ) ^ 2 = 0 ↔ z = 0 ∨ z = κ := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (pow_eq_zero_iff (by norm_num) |>.mp h)
    · exact Or.inr (sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h))
  · rintro (rfl | rfl) <;> ring

/-- The expansion used to compute the test (1) from three power sums. -/
theorem test_expansion (z κ : ℤ) :
    z ^ 2 * (z - κ) ^ 2 = z ^ 4 - 2 * κ * z ^ 3 + κ ^ 2 * z ^ 2 := by ring

/-- Test (1): the sum vanishes iff every value is `0` or `κ`. -/
theorem test_one_iff {A : Type*} [Fintype A] (Z : A → ℤ) (κ : ℤ) :
    ∑ a, Z a ^ 2 * (Z a - κ) ^ 2 = 0 ↔ ∀ a, Z a = 0 ∨ Z a = κ := by
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_mul_sq_nonneg (Z a) κ)]
  simp only [Finset.mem_univ, true_implies, sq_mul_sq_eq_zero_iff]

/-- Test (1) as computed from the three glued networks. -/
theorem test_one_power_sums {A : Type*} [Fintype A] (Z : A → ℤ) (κ : ℤ) :
    ∑ a, Z a ^ 2 * (Z a - κ) ^ 2
      = ∑ a, Z a ^ 4 - 2 * κ * ∑ a, Z a ^ 3 + κ ^ 2 * ∑ a, Z a ^ 2 := by
  simp only [test_expansion, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

/-- One literal: for `ε, X ∈ {0,1}`, `κ ε + (1 - 2ε) κ X = κ [X = 1 - ε]`. -/
theorem literal_factor (κ ε X : ℤ) (hε : ε = 0 ∨ ε = 1) (hX : X = 0 ∨ X = 1) :
    κ * ε + (1 - 2 * ε) * (κ * X) = κ * (if X = 1 - ε then 1 else 0) := by
  rcases hε with rfl | rfl <;> rcases hX with rfl | rfl <;> norm_num

/-- The eight networks `V_S`: the product of three binomials expands over the subsets `S`. -/
theorem three_binomials (a b : Fin 3 → ℤ) :
    ∏ t, (a t + b t) = ∑ S ∈ (univ : Finset (Fin 3)).powerset,
      (∏ t ∈ S, a t) * ∏ t ∈ univ \ S, b t :=
  Finset.prod_add a b univ

/-- Test (2).  If `Z = κ X` with `X` Boolean, the clause sum is `κ³` times the number of violated
clauses, so for `κ ≠ 0` it vanishes iff no clause is violated. -/
theorem clause_sum {I A : Type*} [Fintype I] [DecidableEq A]
    (κ : ℤ) (X : A → ℤ) (hX : ∀ a, X a = 0 ∨ X a = 1)
    (lam : Fin 3 → I → A) (eps : Fin 3 → I → ℤ) (heps : ∀ t i, eps t i = 0 ∨ eps t i = 1) :
    ∑ i, ∏ t, (κ * eps t i + (1 - 2 * eps t i) * (κ * X (lam t i)))
      = κ ^ 3 * ((univ.filter fun i => ∀ t, X (lam t i) = 1 - eps t i).card : ℤ) := by
  have h1 : ∀ i, ∏ t, (κ * eps t i + (1 - 2 * eps t i) * (κ * X (lam t i)))
      = κ ^ 3 * (if ∀ t, X (lam t i) = 1 - eps t i then 1 else 0) := by
    intro i
    simp_rw [fun t => literal_factor κ (eps t i) (X (lam t i)) (heps t i) (hX _)]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.prod_boole]
    simp only [Finset.mem_univ, true_implies]
  rw [Finset.sum_congr rfl (fun i _ => h1 i), ← Finset.mul_sum, Finset.sum_boole]

/-- Test (2) vanishes iff the assignment satisfies every clause (for `κ ≠ 0`). -/
theorem clause_sum_zero_iff {I A : Type*} [Fintype I] [DecidableEq A]
    (κ : ℤ) (hκ : κ ≠ 0) (X : A → ℤ) (hX : ∀ a, X a = 0 ∨ X a = 1)
    (lam : Fin 3 → I → A) (eps : Fin 3 → I → ℤ) (heps : ∀ t i, eps t i = 0 ∨ eps t i = 1) :
    ∑ i, ∏ t, (κ * eps t i + (1 - 2 * eps t i) * (κ * X (lam t i))) = 0
      ↔ ∀ i, ∃ t, X (lam t i) ≠ 1 - eps t i := by
  rw [clause_sum κ X hX lam eps heps]
  constructor
  · intro h i
    by_contra hne
    simp only [not_exists, ne_eq, not_not] at hne
    have hpos : 0 < (univ.filter fun i => ∀ t, X (lam t i) = 1 - eps t i).card :=
      Finset.card_pos.mpr ⟨i, by simpa using hne⟩
    have : κ ^ 3 ≠ 0 := pow_ne_zero 3 hκ
    have hc : ((univ.filter fun i => ∀ t, X (lam t i) = 1 - eps t i).card : ℤ) ≠ 0 := by
      exact_mod_cast hpos.ne'
    exact mul_ne_zero this hc h
  · intro h
    have : (univ.filter fun i => ∀ t, X (lam t i) = 1 - eps t i) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun i _ hall => (h i).elim (fun t ht => ht (hall t)))
    simp [this]

end PvsNP2
