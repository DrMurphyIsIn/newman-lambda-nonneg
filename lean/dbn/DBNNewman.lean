/-
  DBNNewman -- Newman's conjecture (Rodgers-Tao's theorem) on the dbn island: for every `t < 0`,
  `H_t` has a zero off the real axis.  Step 6 of the Lambda >= 0 formalization following Dobner
  (arXiv:2005.05142, section 3.1); see NEWMAN_LAMBDA_NONNEG_SCOPING_2026-10-10.md.

  Proof.  `c = -t > 0`.  `F = F_{c/4}` has a zero `s₀` (DBNFtZero).  Along Bohr's shifts `τ_j → ∞`
  (DBNBohr) the functions `s ↦ F(s + iτ_j)` converge to `F` locally uniformly; by Theorem 4
  (DBNTheorem4) so do the functions `s ↦ h(s + iτ_j)`, `h = ξ_c ∘ J / γ_t`, on the disc `|s − s₀| < 1`.
  If all but finitely many of them were zero-free on the disc, Hurwitz (`DBN.hurwitz_ne_zero`) would
  make `F s₀ ≠ 0`; so some `h(z + iτ_j)` vanishes with `|z − s₀| < 1` and `τ_j` as large as we like.
  Then `ξ_c(J(w)) = 0` for `w = z + iτ_j`, i.e. `H_t(Z) = 0` for `Z = −i(2J(w) − 1)`, and
  `Im Z = 1 − 2 Re J(w) = 1 − 2(Re w + (c/4) log(|w + M₀|/2π)) < 0` once `τ_j` is large.

  In the island's sInf-free vocabulary this is `Λ ≥ 0`: no `t < 0` has all zeros of `H_t` real.
  Together with the registry's `dbn_debruijn_real_zeros` (`Λ ≤ 1/2`) and the judged
  `dbn_real_zeros_of_qrh_unconditional` (`Λ ≤ 9/32`, cross-pin), the kernel-checked picture of the
  de Bruijn-Newman constant is `0 ≤ Λ ≤ 9/32`.  `Λ = 0` is RH and is NOT proved.
  conjecture1_proved = False.
-/
import Mathlib
import DBNTheorem4
import DBNFtZeroHigh

open Complex Filter Topology Metric
open scoped Real

namespace DBNSaddle

open DBNGaussConv DBNStirling

/-- The normalised function `h(w) = ξ_c(J(w)) / γ_t(w)`. -/
noncomputable def hfun (c M₀ : ℝ) (w : ℂ) : ℂ :=
  DBN.H (-c) (-I * (2 * J c M₀ w - 1)) / γt c M₀ w

lemma differentiableAt_hfun {c M₀ : ℝ} {w : ℂ} (hre : 0 < (w + M₀).re) (him : 0 < w.im) :
    DifferentiableAt ℂ (hfun c M₀) w := by
  have hb0 : w + M₀ ≠ 0 := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  have hb1 : w + M₀ - 1 ≠ 0 := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  have hre' : 0 < w.re + M₀ := by simpa using hre
  have hslit : (w + M₀) / 2 ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
  have hell : DifferentiableAt ℂ (fun v : ℂ => ell (v + M₀)) w := by
    have h1 : DifferentiableAt ℂ (fun v : ℂ => log ((v + M₀) / 2)) w :=
      ((differentiableAt_id.add_const _).div_const _).clog hslit
    have h2 : DifferentiableAt ℂ (fun v : ℂ => log ((v + M₀) / 2) - (Real.log π : ℂ)) w :=
      h1.sub_const _
    exact h2.const_mul _
  have hJ : DifferentiableAt ℂ (J c M₀) w := by
    unfold J
    exact differentiableAt_id.add (hell.const_mul _)
  have hγt : DifferentiableAt ℂ (γt c M₀) w := by
    have h3 : DifferentiableAt ℂ
        (fun v : ℂ => -(M₀ : ℂ) * ell (v + M₀) + (c / 4 : ℂ) * ell (v + M₀) ^ 2) w :=
      (hell.const_mul _).add ((hell.pow 2).const_mul _)
    exact ((differentiableAt_γ hre).comp w (differentiableAt_id.add_const _)).mul h3.cexp
  have hH : DifferentiableAt ℂ (fun v : ℂ => DBN.H (-c) (-I * (2 * J c M₀ v - 1))) w :=
    (DBN.differentiable_H (-c)).differentiableAt.comp w (((hJ.const_mul 2).sub_const 1).const_mul _)
  exact hH.div hγt (γt_ne_zero hre hb0 hb1)

/-- `Im (−i(2J(w) − 1)) = 1 − 2 Re J(w)` and `Re J(w) = Re w + (c/4) log(‖w+M₀‖/(2π))`. -/
lemma re_J {c M₀ : ℝ} {w : ℂ} (hw : w + M₀ ≠ 0) :
    (J c M₀ w).re = w.re + c / 4 * (Real.log ‖w + M₀‖ - Real.log (2 * π)) := by
  have e : J c M₀ w = w + ((c / 4 : ℝ) : ℂ) * (log ((w + M₀) / 2) - (Real.log π : ℂ)) := by
    rw [J, ell]; push_cast; ring
  rw [e, Complex.add_re, Complex.re_ofReal_mul, Complex.sub_re, Complex.log_re, Complex.ofReal_re,
    norm_div, Complex.norm_ofNat, Real.log_div (norm_ne_zero_iff.mpr hw) two_ne_zero,
    Real.log_mul two_ne_zero Real.pi_pos.ne']
  ring

lemma im_Z {c M₀ : ℝ} (w : ℂ) : (-I * (2 * J c M₀ w - 1)).im = 1 - 2 * (J c M₀ w).re := by
  simp [Complex.mul_im, Complex.sub_re, Complex.sub_im]

/-- **Newman's conjecture on the dbn island** (Rodgers-Tao 2018; proof after Dobner 2020):
for every `t < 0`, `H_t` has a non-real zero. -/
theorem dbn_newman_of_neg {t : ℝ} (ht : t < 0) : ∃ z : ℂ, DBN.H t z = 0 ∧ z.im ≠ 0 := by
  set c : ℝ := -t with hcdef
  have hc : 0 < c := by linarith
  have hc4 : 0 < c / 4 := by positivity
  have htc : t = -c := by rw [hcdef]; ring
  -- the zero of F and the strip around it
  obtain ⟨s₀, hs₀⟩ := DBNFtZero.exists_zero hc4
  set x₀ : ℝ := s₀.re with hx₀
  set M₀ : ℝ := 3 - x₀ with hM₀
  set F : ℂ → ℂ := DBNFtZero.F (c / 4) with hFdef
  have hFdiff : Differentiable ℂ F := DBNFtZero.differentiable_F hc4
  have hFne : ∃ z, F z ≠ 0 := ⟨0, fun h0 => by
    have := DBNFtZero.one_le_norm_F hc4 0
    rw [Complex.ofReal_zero] at this
    rw [hFdef] at h0
    rw [h0, norm_zero] at this
    linarith⟩
  -- Bohr's shifts
  obtain ⟨τ, hτ, hconv⟩ := DBNBohr.exists_shifts_tendstoLocallyUniformly (DBNFtZero.gaussCoeff (c / 4))
    (DBNFtZero.lseriesSummable hc4)
  have hτ_top : Tendsto (fun j => (τ j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hτ.tendsto_atTop
  -- the shifted normalised functions
  set G : ℕ → ℂ → ℂ := fun j s => hfun c M₀ (s + (τ j : ℂ) * I) with hGdef
  set U : Set ℂ := ball s₀ 1 with hUdef
  -- geometry of the disc
  have hre_ball : ∀ s ∈ U, |s.re - x₀| ≤ 1 := fun s hs => by
    have := Complex.abs_re_le_norm (s - s₀)
    rw [Complex.sub_re] at this
    exact this.trans (by simpa [dist_eq_norm] using (mem_ball.mp hs).le)
  have him_ball : ∀ s ∈ U, s₀.im - 1 ≤ s.im := fun s hs => by
    have := Complex.abs_im_le_norm (s - s₀)
    rw [Complex.sub_im] at this
    have h2 : ‖s - s₀‖ ≤ 1 := by simpa [dist_eq_norm] using (mem_ball.mp hs).le
    linarith [abs_le.mp (this.trans h2)]
  -- height threshold for differentiability: Im (s + τ_j i) > 0 and Re (s + τ_j i + M₀) > 0 on U
  have hdiff : ∀ j : ℕ, |s₀.im| + 2 ≤ (τ j : ℝ) → DifferentiableOn ℂ (G j) U := by
    intro j hj s hs
    have h1 := him_ball s hs
    have h2 := hre_ball s hs
    have hxx := abs_le.mp h2
    refine (differentiableAt_hfun (c := c) (M₀ := M₀) ?_ ?_).comp s
      (differentiableAt_id.add_const _) |>.differentiableWithinAt
    · simp [hM₀]; linarith
    · simp; linarith [abs_le.mp (le_refl |s₀.im|)]
  -- local uniform convergence of G j to F on U
  have hconvG : TendstoLocallyUniformlyOn G F atTop U := by
    rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε s hs
    obtain ⟨Y, hY⟩ := theorem4 hc x₀ (half_pos hε)
    have hB := (Metric.tendstoLocallyUniformlyOn_iff.mp (hconv.tendstoLocallyUniformlyOn (s := U)))
      (ε / 2) (half_pos hε) s hs
    obtain ⟨tset, htset, hBev⟩ := hB
    refine ⟨tset ∩ U, inter_mem htset self_mem_nhdsWithin, ?_⟩
    have hev2 : ∀ᶠ j in atTop, Y - (s₀.im - 1) ≤ (τ j : ℝ) :=
      hτ_top.eventually_ge_atTop _
    filter_upwards [hBev, hev2] with j hj1 hj2 y hy
    have hyU := hy.2
    have hyre := hre_ball y hyU
    have hyim := him_ball y hyU
    have hY' : Y ≤ (y + (τ j : ℂ) * I).im := by simp; linarith
    have hre' : |(y + (τ j : ℂ) * I).re - x₀| ≤ 1 := by simpa using hyre
    have h4 := hY (y + (τ j : ℂ) * I) hre' hY'
    have hB' := hj1 y hy.1
    -- dist (F y) (G j y) ≤ dist (F y) (F (y + τ i)) + dist (F (y + τ i)) (G j y)
    calc dist (F y) (G j y) ≤ dist (F y) (F (y + (τ j : ℂ) * I)) + dist (F (y + (τ j : ℂ) * I)) (G j y) :=
          dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by
          refine add_lt_add_of_lt_of_le hB' ?_
          rw [dist_eq_norm, norm_sub_rev]
          exact h4
      _ = ε := by ring
  -- Hurwitz: the shifted functions cannot all be zero-free on U
  have hnot : ¬ ∀ᶠ j in atTop, ∀ z ∈ U, G j z ≠ 0 := by
    intro hev
    have hF : ∀ᶠ j in atTop, DifferentiableOn ℂ (G j) U ∧ ∀ z ∈ U, G j z ≠ 0 := by
      filter_upwards [hτ_top.eventually_ge_atTop (|s₀.im| + 2), hev] with j hj1 hj2
      exact ⟨hdiff j hj1, hj2⟩
    exact DBN.hurwitz_ne_zero isOpen_ball hF hFdiff hconvG hFne (mem_ball_self one_pos) hs₀
  rw [Filter.not_eventually] at hnot
  -- height threshold for the zero to be off the real axis
  set T : ℝ := |s₀.im| + 2 + 2 * π * Real.exp (4 * (2 + |x₀|) / c) with hT
  have hev : ∀ᶠ j in atTop, T ≤ (τ j : ℝ) := hτ_top.eventually_ge_atTop T
  obtain ⟨j, hj, hjT⟩ := (hnot.and_eventually hev).exists
  push Not at hj
  obtain ⟨z, hzU, hGz⟩ := hj
  set w : ℂ := z + (τ j : ℂ) * I with hw
  have hzre := hre_ball z hzU
  have hzim := him_ball z hzU
  have hxx := abs_le.mp hzre
  have hwim' : w.im = z.im + τ j := by simp [hw]
  have hwim : s₀.im - 1 + τ j ≤ w.im := by rw [hwim']; linarith
  have hwim_pos : 0 < w.im := by
    have := abs_le.mp (le_refl |s₀.im|)
    have hT' : |s₀.im| + 2 ≤ (τ j : ℝ) := by
      have : 0 ≤ 2 * π * Real.exp (4 * (2 + |x₀|) / c) := by positivity
      linarith
    linarith
  have hwre : 0 < (w + M₀).re := by
    have : (w + M₀).re = z.re + M₀ := by simp [hw]
    rw [this, hM₀]; linarith
  have hwb0 : w + M₀ ≠ 0 := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  have hwb1 : w + M₀ - 1 ≠ 0 := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  -- the zero of H
  have hH : DBN.H (-c) (-I * (2 * J c M₀ w - 1)) = 0 := by
    have : hfun c M₀ w = 0 := hGz
    rw [hfun, div_eq_zero_iff] at this
    exact this.resolve_right (γt_ne_zero hwre hwb0 hwb1)
  refine ⟨-I * (2 * J c M₀ w - 1), by rw [htc]; exact hH, ?_⟩
  rw [im_Z, re_J hwb0]
  -- Re J(w) > 1/2
  have hnorm : (τ j : ℝ) - |s₀.im| - 1 ≤ ‖w + M₀‖ := by
    have h1 : (w + M₀).im ≤ |(w + M₀).im| := le_abs_self _
    have h2 := Complex.abs_im_le_norm (w + M₀)
    have h3 : (w + M₀).im = w.im := by simp
    have := abs_le.mp (le_refl |s₀.im|)
    linarith
  have hpos : 0 < (τ j : ℝ) - |s₀.im| - 1 := by
    have : 0 < 2 * π * Real.exp (4 * (2 + |x₀|) / c) := by positivity
    linarith
  have hlog : 4 * (2 + |x₀|) / c ≤ Real.log ‖w + M₀‖ - Real.log (2 * π) := by
    have hE : 2 * π * Real.exp (4 * (2 + |x₀|) / c) ≤ ‖w + M₀‖ := by linarith
    rw [← Real.log_div (norm_ne_zero_iff.mpr hwb0) (by positivity),
      ← Real.log_exp (4 * (2 + |x₀|) / c)]
    apply Real.log_le_log (Real.exp_pos _)
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hJre : 1 / 2 < w.re + c / 4 * (Real.log ‖w + M₀‖ - Real.log (2 * π)) := by
    have h1 : c / 4 * (4 * (2 + |x₀|) / c) = 2 + |x₀| := by field_simp
    have h2 : c / 4 * (4 * (2 + |x₀|) / c) ≤ c / 4 * (Real.log ‖w + M₀‖ - Real.log (2 * π)) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have h3 : w.re = z.re := by simp [hw]
    have := abs_le.mp (le_refl |x₀|)
    linarith
  intro h0
  linarith

end DBNSaddle

/-- Registry node `RH_dbn_newman`, statement verbatim (`Statements.RH_dbn_newman`). -/
theorem dbn_newman :
    ∀ t : ℝ, t < 0 → ∃ z : ℂ, DBN.H t z = 0 ∧ z.im ≠ 0 :=
  fun _ ht => DBNSaddle.dbn_newman_of_neg ht
