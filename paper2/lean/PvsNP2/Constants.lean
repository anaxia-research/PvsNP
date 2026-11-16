/-
Constants of Theorems 3.9 and 4.3.
-/
import Mathlib

namespace PvsNP2

/-- The coefficient of Corollary 1 of [Bha26] for networks with at most `18 s` edges. -/
theorem coefficient : 1872 * 18 + 64 = 33760 := by norm_num

/-- `√2 < 1481/1000`. -/
theorem sqrt_two_lt : Real.sqrt 2 < 1481 / 1000 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- The choice `c(δ) = √δ / (2·10⁶)` leaves room for `η` in the proof of Theorem 4.3:
`4 c(δ) < 1 / (10 A₁(δ))` with `A₁(δ) = 33760 √2 / √δ`. -/
theorem room_for_eta (δ : ℝ) (hδ : 0 < δ) :
    4 * (Real.sqrt δ / 2000000) < 1 / (10 * (33760 * Real.sqrt 2 / Real.sqrt δ)) := by
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have h2 : 0 < Real.sqrt 2 := by positivity
  have hlt := sqrt_two_lt
  rw [show 1 / (10 * (33760 * Real.sqrt 2 / Real.sqrt δ))
      = Real.sqrt δ / (337600 * Real.sqrt 2) by field_simp; ring]
  rw [show 4 * (Real.sqrt δ / 2000000) = Real.sqrt δ / 500000 by ring]
  apply div_lt_div_of_pos_left hs (by positivity)
  nlinarith

/-- The time bound of the test: with test networks of size at most `4 s_n + B n` and
`η < 1/(10 A)`, the exponent `A (4 η n) ` is below `n / 2` with room `n/10`. -/
theorem exponent_room (A η n : ℝ) (hA : 0 < A) (hn : 0 < n)
    (hη' : η < 1 / (10 * A)) : A * (4 * η * n) < n / 2 - n / 10 := by
  have : A * η < 1 / 10 := by
    rw [lt_div_iff₀ (by positivity)] at hη'
    nlinarith
  nlinarith

end PvsNP2
