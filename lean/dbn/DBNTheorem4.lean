/-
  DBNTheorem4 -- Dobner's Theorem 4 in qualitative form, on the dbn island.

  Step 5 of the Lambda >= 0 (Newman's conjecture) formalization, assembled from DBNSaddleAlg
  (exact bookkeeping), DBNSaddleBounds (pointwise estimates) and DBNSaddleSum (integration and
  summation).  With `c = |t| > 0`, a strip centre `x₀`, `M₀ = 3 − x₀`, `J(s) = s + (c/4) Log((s+M₀)/2π)`,
  `γ_t(s) = γ(s+M₀) exp(−M₀ ℓ(s+M₀) + (c/4) ℓ(s+M₀)²)` and `F_{c/4}(s) = ∑ exp(−(c/4) log²n) n^{-s}`:

      ξ_c(J(s)) / γ_t(s) − F_{c/4}(s) → 0   as Im s → ∞, uniformly for |Re s − x₀| ≤ 1,

  where `ξ_c(w) = H_{-c}(−i(2w−1))` is the island's heat-flowed `H` in the variable `s = ½ + iz/2`.
  This is eq. (14) of arXiv:2005.05142 (the error rate `y^{-1/5}` and the region `|x| ≤ C y^{1/4}` are
  not needed and not proved).

  Nothing here is RH.  conjecture1_proved = False.
-/
import Mathlib
import DBNSaddleSum

open Complex Filter Topology
open scoped Real

namespace DBNSaddle

/-- **Dobner's Theorem 4, qualitative form.** -/
theorem theorem4 {c : ℝ} (hc : 0 < c) (x₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Y : ℝ, ∀ s : ℂ, |s.re - x₀| ≤ 1 → Y ≤ s.im →
      ‖DBN.H (-c) (-I * (2 * J c (3 - x₀) s - 1)) / γt c (3 - x₀) s - DBNFtZero.F (c / 4) s‖ ≤ ε := by
  obtain ⟨Y₀, hY₀⟩ := error_sum_small hc x₀ hε
  refine ⟨max Y₀ 1, fun s hx hY => ?_⟩
  have hy : 0 < s.im := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hY)
  have hxx := abs_le.mp hx
  have hb : 0 < (s + ((3 - x₀ : ℝ) : ℂ)).re := by simp; linarith
  have hb0 : s + ((3 - x₀ : ℝ) : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  have hb1 : s + ((3 - x₀ : ℝ) : ℂ) - 1 ≠ 0 := fun h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  obtain ⟨hsum, hsmall⟩ := hY₀ s hx (le_trans (le_max_left _ _) hY)
  have hxi := xi_J_eq hc hb hb0 hb1 hsum
  have hγ := γt_ne_zero (c := c) hb hb0 hb1
  rw [hxi, mul_div_cancel_left₀ _ hγ, add_sub_cancel_left]
  exact hsmall

end DBNSaddle
