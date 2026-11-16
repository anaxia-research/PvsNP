/-
The chain encoding of a weighted vertex (Lemma 3.8) and exact recovery (Theorem 3.9).
-/
import Mathlib

namespace PvsNP2

open Finset

/-- A block of at most `K` inputs with weights `|wᵢ| ≤ 2^β` has value in `[-K 2^β, K 2^β]`. -/
theorem block_value_bound {ι : Type*} (I : Finset ι) (w : ι → ℤ) (y : ι → ℤ) (β K : ℕ)
    (hw : ∀ i ∈ I, |w i| ≤ 2 ^ β) (hy : ∀ i ∈ I, y i = 0 ∨ y i = 1) (hI : I.card ≤ K) :
    |∑ i ∈ I, w i * y i| ≤ (K : ℤ) * 2 ^ β := by
  calc |∑ i ∈ I, w i * y i| ≤ ∑ i ∈ I, |w i * y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ I, (2 : ℤ) ^ β := by
        apply Finset.sum_le_sum
        intro i hi
        rcases hy i hi with h | h <;> simp [h, hw i hi]
    _ = (I.card : ℤ) * 2 ^ β := by simp
    _ ≤ (K : ℤ) * 2 ^ β := by
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast hI) (by positivity)

/-- The shifted block value `P + K 2^β` lies in `[0, 2^b)` for `b = β + c + 2`, `K ≤ 2^c`. -/
theorem block_value_fits (P : ℤ) (β K c : ℕ) (hP : |P| ≤ (K : ℤ) * 2 ^ β) (hK : K ≤ 2 ^ c) :
    0 ≤ P + K * 2 ^ β ∧ P + K * 2 ^ β < 2 ^ (β + c + 2) := by
  have h1 := abs_le.mp hP
  have hK' : (K : ℤ) ≤ 2 ^ c := by exact_mod_cast hK
  have h2 : (2 : ℤ) ^ (β + c + 2) = 4 * 2 ^ c * 2 ^ β := by ring
  have hb : (0 : ℤ) < 2 ^ β := by positivity
  have h3 : (K : ℤ) * 2 ^ β ≤ 2 ^ c * 2 ^ β := mul_le_mul_of_nonneg_right hK' hb.le
  have h4 : (0 : ℤ) < 2 ^ c * 2 ^ β := by positivity
  constructor
  · linarith
  · rw [h2]; linarith

/-- Running sums of the chain: `R₀ = 0`, `R_{j+1} = R_j + e_j` give `R_k = ∑_{j<k} e_j`. -/
theorem chain_running_sum (e R : ℕ → ℤ) (h0 : R 0 = 0) (hs : ∀ j, R (j + 1) = R j + e j) :
    ∀ k, R k = ∑ j ∈ range k, e j := by
  intro k
  induction k with
  | zero => simp [h0]
  | succ k ih => rw [hs, ih, Finset.sum_range_succ]

/-- The constraints determine the running sums uniquely. -/
theorem chain_unique (e R R' : ℕ → ℤ) (h0 : R 0 = 0) (h0' : R' 0 = 0)
    (hs : ∀ j, R (j + 1) = R j + e j) (hs' : ∀ j, R' (j + 1) = R' j + e j) : R = R' := by
  funext k
  rw [chain_running_sum e R h0 hs, chain_running_sum e R' h0' hs']

/-- Removing the offsets: `∑_{j<k} (P_j + K 2^β) - k K 2^β = ∑_{j<k} P_j`. -/
theorem chain_offset (P : ℕ → ℤ) (k K β : ℕ) :
    ∑ j ∈ range k, (P j + K * 2 ^ β) - k * (K * 2 ^ β) = ∑ j ∈ range k, P j := by
  rw [Finset.sum_add_distrib]; simp

/-- Exact recovery: `|Z| ≤ 2^s` is determined by its residue modulo `2^(s+2)`. -/
theorem exact_recovery (Z : ℤ) (s : ℕ) (hZ : |Z| ≤ 2 ^ s) :
    Z = if Z % 2 ^ (s + 2) > 2 ^ (s + 1) then Z % 2 ^ (s + 2) - 2 ^ (s + 2)
        else Z % 2 ^ (s + 2) := by
  have hP : (0 : ℤ) < 2 ^ s := by positivity
  have e1 : (2 : ℤ) ^ (s + 1) = 2 * 2 ^ s := by ring
  have e2 : (2 : ℤ) ^ (s + 2) = 4 * 2 ^ s := by ring
  have h := abs_le.mp hZ
  rcases le_or_gt 0 Z with hz | hz
  · have hm : Z % 2 ^ (s + 2) = Z := Int.emod_eq_of_lt hz (by rw [e2]; linarith)
    rw [hm]
    split_ifs with hh
    · exfalso; rw [e1] at hh; linarith
    · rfl
  · have hm : Z % 2 ^ (s + 2) = Z + 2 ^ (s + 2) := by
      rw [show Z % 2 ^ (s + 2) = (Z + 2 ^ (s + 2)) % 2 ^ (s + 2) by simp]
      exact Int.emod_eq_of_lt (by rw [e2]; linarith) (by rw [e2]; linarith)
    rw [hm]
    split_ifs with hh
    · ring
    · exfalso; rw [e1, e2] at hh; linarith

/-- The value of a network is at most `2^s` in absolute value when all its factors are. -/
theorem value_bound (E : ℕ) (bsum : ℕ) (Z : ℤ)
    (h : |Z| ≤ 2 ^ E * 2 ^ bsum) : |Z| ≤ 2 ^ (E + bsum) := by
  rwa [pow_add]

end PvsNP2
