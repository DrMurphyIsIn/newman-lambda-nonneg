/-
  DBNFtZeroHigh -- the Gaussian-weighted Dirichlet series has zeros at arbitrarily large height.

  Newman / Lambda >= 0 programme, step 2b (Dobner's use of Theorem 5 in section 3.1, Rouche
  replaced by the zero-free form of Hurwitz already on this island).  See
  telperion/docs/NEWMAN_LAMBDA_NONNEG_SCOPING_2026-10-10.md.

  `F c` has a zero `s₀` (DBNFtZero).  Along Bohr's shifts `τ_j → ∞` (DBNBohr) the functions
  `s ↦ F c (s + τ_j I)` converge to `F c` locally uniformly.  If all but finitely many of them were
  zero-free on the unit disc around `s₀`, Hurwitz (`DBN.hurwitz_ne_zero`) would make `F c s₀ ≠ 0`.
  So infinitely many of them have a zero in the disc, i.e. `F c` has zeros of imaginary part
  `≥ Im s₀ + τ_j - 1`, arbitrarily large.

  Nothing here is RH.  conjecture1_proved = False.
-/
import Mathlib
import DBNBohr
import DBNFtZero
import DBNHurwitz

open Complex Filter Topology

namespace DBNFtZero

/-- `F c` has zeros of arbitrarily large imaginary part. -/
theorem exists_zero_im_ge {c : ℝ} (hc : 0 < c) (T : ℝ) : ∃ s : ℂ, F c s = 0 ∧ T ≤ s.im := by
  obtain ⟨s₀, hs₀⟩ := exists_zero hc
  obtain ⟨τ, hτ, hconv⟩ :=
    DBNBohr.exists_shifts_tendstoLocallyUniformly (gaussCoeff c) (lseriesSummable hc)
  by_contra h
  push Not at h
  -- every zero of F c has imaginary part < T
  have hτ_top : Tendsto (fun j => (τ j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hτ.tendsto_atTop
  have hF : ∀ᶠ j in atTop, DifferentiableOn ℂ (fun s => F c (s + (τ j : ℂ) * I))
      (Metric.ball s₀ 1) ∧ ∀ z ∈ Metric.ball s₀ 1, F c (z + (τ j : ℂ) * I) ≠ 0 := by
    filter_upwards [hτ_top.eventually_ge_atTop (T - s₀.im + 1)] with j hj
    refine ⟨((differentiable_F hc).comp (differentiable_id.add_const _)).differentiableOn, ?_⟩
    intro z hz hzero
    have h1 := h _ hzero
    have h2 : |z.im - s₀.im| < 1 := by
      have := Complex.abs_im_le_norm (z - s₀)
      rw [Complex.sub_im] at this
      exact lt_of_le_of_lt this (by simpa [dist_eq_norm] using hz)
    rw [Complex.add_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, Complex.I_re,
      Complex.I_im] at h1
    have := abs_lt.mp h2
    linarith [this.1, this.2]
  have hne : ∃ z, F c z ≠ 0 := ⟨0, fun h0 => by
    have := one_le_norm_F hc 0
    rw [Complex.ofReal_zero, h0, norm_zero] at this
    linarith⟩
  exact DBN.hurwitz_ne_zero Metric.isOpen_ball hF (differentiable_F hc)
    (hconv.tendstoLocallyUniformlyOn) hne (Metric.mem_ball_self one_pos) hs₀

end DBNFtZero
