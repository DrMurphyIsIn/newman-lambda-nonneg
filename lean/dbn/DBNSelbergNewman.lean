/-
  DBNSelbergNewman -- Dobner's Theorem 4 and the Hurwitz transfer for an abstract element `F` of the
  extended Selberg class (`DBNSelberg.ExtSelbergData`), generalizing DBNTheorem4 and DBNNewman from ζ.
  Programme item 3 of RH_PROGRAM_2026-10-10.md; see SELBERG_NEWMAN_DESIGN_2026-10-10.md, row
  "DBNTheorem4, DBNNewman -> DBNSelbergNewman".

  The summation module DBNSelbergSaddleSum is not finished, so its output is taken here as the
  explicit hypothesis `ErrorSumSmall F`: for `c > 0`, a strip centre `x₀`, `M₀ = 3 − x₀`, the error
  series `∑ a(n) a_n n^{-s} E_n(s)` is summable and `≤ ε` in norm once `Im s` is large, uniformly
  for `|Re s − x₀| ≤ 1`.  Everything else is proved:

  * `theorem4_of`: `ξ_c(J_F(s)) / γ_t(s) − F_{c/4}(s) → 0` as `Im s → ∞`, uniformly on the strip,
    where `ξ_c(w) = F.flow (−c) (−i(2w−1))`; from Dobner's (9) (`xi_eq_tsum_Bn`), the exact
    bookkeeping (`tsum_Bn_J_eq`), `γ_t ≠ 0` (from `P(s+M₀) ≠ 0` above the roots of `P`) and
    `ErrorSumSmall`.
  * `differentiable_flow`: the Gaussian convolution `F.flow (−c)` is entire (differentiation under
    the integral sign, dominated by the Gaussian times a Cauchy-estimate bound for `Ξ'` on a strip).
    For ζ this was free (`DBN.differentiable_H`).
  * `selberg_newman_of`: for every `t < 0`, `F.flow t` has a non-real zero.  Transfer as in
    DBNNewman: `F_{c/4}` has a zero `s₀`; along Bohr's shifts `τ_j` the normalised functions
    `h(s + iτ_j)` converge locally uniformly to `F_{c/4}` on `|s − s₀| < 1`; Hurwitz
    (`DBN.hurwitz_ne_zero`) forces a zero `z` of some `h(· + iτ_j)` with `τ_j` large; then
    `ξ_c(J_F(w)) = 0` for `w = z + iτ_j` and `Im(−i(2J_F(w)−1)) = 1 − 2 Re J_F(w) < 0` because
    `Re J_F(w) = Re w + (c/2)(log Q + ∑ λ_j log‖λ_j(w+M₀)+μ_j‖) → ∞` as `∑ λ_j > 0`.

  Nothing here is about the zeros of ζ or of any `F`; `conjecture1_proved = False`.
-/
import Mathlib
import DBNSelbergData
import DBNSelbergGauss
import DBNSelbergSaddleAlg
import DBNSelbergFtZero
import DBNBohr
import DBNHurwitz
import DBNSaddleAlg
import DBNSelbergSaddleSum
import DBNSelbergZeta

open Complex Filter Topology Metric MeasureTheory
open scoped Real

namespace DBNSelberg

namespace ExtSelbergData

open DBNGaussConv

variable (F : ExtSelbergData)

/-- The output of DBNSelbergSaddleSum (`error_sum_small`), taken as a hypothesis here. -/
def ErrorSumSmall (F : ExtSelbergData) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ x₀ : ℝ, ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ s : ℂ, |s.re - x₀| ≤ 1 → Y ≤ s.im →
    (Summable fun n : ℕ+ => F.a n * (DBNSaddle.coef c n : ℂ) * (1 / (n : ℂ) ^ s) * F.EF c (3 - x₀) n s) ∧
    ‖∑' n : ℕ+, F.a n * (DBNSaddle.coef c n : ℂ) * (1 / (n : ℂ) ^ s) * F.EF c (3 - x₀) n s‖ ≤ ε

/-! ### The roots of `P` lie below some height -/

/-- A nonzero polynomial has finitely many roots: above some height `R` it does not vanish. -/
lemma exists_im_bound_P_ne_zero : ∃ R : ℝ, ∀ b : ℂ, R ≤ b.im → F.P.eval b ≠ 0 := by
  classical
  refine ⟨1 + ∑ r ∈ F.P.roots.toFinset, ‖r‖, fun b hb hroot => ?_⟩
  have hmem : b ∈ F.P.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots F.P_ne_zero, Polynomial.IsRoot.def]
    exact hroot
  have h1 : ‖b‖ ≤ ∑ r ∈ F.P.roots.toFinset, ‖r‖ :=
    Finset.single_le_sum (f := fun r : ℂ => ‖r‖) (fun r _ => norm_nonneg r) hmem
  have h2 := Complex.abs_im_le_norm b
  have h3 := le_abs_self b.im
  linarith

/-! ### The backward heat flow is entire -/

lemma continuous_gaussKer (c : ℝ) : Continuous (gaussKer c) := by
  unfold gaussKer
  fun_prop

/-- Cauchy's estimate: `Ξ'` is bounded on every horizontal strip. -/
lemma exists_deriv_Ξ_strip_bounded (B : ℝ) :
    ∃ C : ℝ, ∀ w : ℂ, |w.im| ≤ B → ‖deriv F.Ξ w‖ ≤ C := by
  obtain ⟨C, hC⟩ := F.Ξ_strip_bounded (B + 1)
  refine ⟨C, fun w hw => ?_⟩
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := w) (R := 1) (f := F.Ξ)
    one_pos F.Ξ_differentiable.diffContOnCl (fun z hz => hC z ?_)
  · simpa using h
  · have h1 : ‖z - w‖ = 1 := by simpa [dist_eq_norm] using hz
    have h2 := Complex.abs_im_le_norm (z - w)
    rw [Complex.sub_im, h1] at h2
    have h3 := abs_le.mp h2
    have h4 := abs_le.mp hw
    rw [abs_le]
    constructor <;> linarith

/-- Differentiation under the Gaussian integral. -/
lemma hasDerivAt_flowIntegral {c : ℝ} (hc : 0 < c) (z₀ : ℂ) :
    HasDerivAt (fun z : ℂ => ∫ ω : ℝ, gaussKer c ω * F.Ξ (z + ω))
      (∫ ω : ℝ, gaussKer c ω * deriv F.Ξ (z₀ + ω)) z₀ := by
  obtain ⟨C, hC⟩ := F.exists_deriv_Ξ_strip_bounded (|z₀.im| + 1)
  obtain ⟨C₀, hC₀⟩ := F.Ξ_strip_bounded |z₀.im|
  have hcont : ∀ z : ℂ, Continuous fun ω : ℝ => gaussKer c ω * F.Ξ (z + ω) := fun z =>
    (continuous_gaussKer c).mul (F.Ξ_differentiable.continuous.comp (by fun_prop))
  have hderiv_cont : Continuous (deriv F.Ξ) :=
    (F.Ξ_differentiable.contDiff (n := 1)).continuous_deriv le_rfl
  have hcont' : Continuous fun ω : ℝ => gaussKer c ω * deriv F.Ξ (z₀ + ω) :=
    (continuous_gaussKer c).mul (hderiv_cont.comp (by fun_prop))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := z₀)
    (s := ball z₀ 1)
    (F := fun z ω => gaussKer c ω * F.Ξ (z + ω))
    (F' := fun z ω => gaussKer c ω * deriv F.Ξ (z + ω))
    (bound := fun ω => ‖gaussKer c ω‖ * C) (ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => (hcont z).aestronglyMeasurable) ?_
    hcont'.aestronglyMeasurable ?_ ?_ ?_
  · exact key.2
  · refine ((integrable_gaussK hc).norm.mul_const C₀).mono' (hcont z₀).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [norm_mul]
    gcongr
    apply hC₀
    simp
  · refine ae_of_all _ fun ω z hz => ?_
    rw [norm_mul]
    gcongr
    apply hC
    have h1 : ‖z - z₀‖ < 1 := by simpa [dist_eq_norm] using hz
    have h2 := Complex.abs_im_le_norm (z - z₀)
    rw [Complex.sub_im] at h2
    have h3 := abs_le.mp (h2.trans h1.le)
    have h4 := abs_le.mp (le_refl |z₀.im|)
    simp only [Complex.add_im, Complex.ofReal_im, add_zero]
    rw [abs_le]
    constructor <;> linarith
  · exact (integrable_gaussK hc).norm.mul_const C
  · refine ae_of_all _ fun ω z _ => ?_
    exact ((F.Ξ_differentiable (z + ω)).hasDerivAt.comp_add_const z (ω : ℂ)).const_mul _

/-- The Gaussian convolution `F.flow (-c)`, `c > 0`, is entire. -/
lemma differentiable_flow {c : ℝ} (hc : 0 < c) : Differentiable ℂ (F.flow (-c)) := by
  have e : F.flow (-c) = fun z =>
      (1 / ((Real.sqrt (4 * π * c) : ℝ) : ℂ)) * ∫ ω : ℝ, gaussKer c ω * F.Ξ (z + ω) := by
    funext z
    simp only [flow, neg_neg]
  rw [e]
  exact fun z => ((F.hasDerivAt_flowIntegral hc z).differentiableAt).const_mul _

/-! ### Theorem 4 -/

/-- **Dobner's Theorem 4 for `F`, qualitative form**, modulo `ErrorSumSmall`. -/
theorem theorem4_of (herr : F.ErrorSumSmall) {c : ℝ} (hc : 0 < c) (x₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Y : ℝ, ∀ s : ℂ, |s.re - x₀| ≤ 1 → Y ≤ s.im →
      ‖F.flow (-c) (-I * (2 * F.JF c (3 - x₀) s - 1)) / F.γtF c (3 - x₀) s - F.Ft (c / 4) s‖ ≤ ε := by
  obtain ⟨Y₀, hY₀⟩ := herr c hc x₀ ε hε
  obtain ⟨R, hR⟩ := F.exists_im_bound_P_ne_zero
  refine ⟨max Y₀ R, fun s hx hY => ?_⟩
  have hxx := abs_le.mp hx
  have hb : 0 < (s + ((3 - x₀ : ℝ) : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hP : F.P.eval (s + ((3 - x₀ : ℝ) : ℂ)) ≠ 0 := by
    apply hR
    simp only [Complex.add_im, Complex.ofReal_im, add_zero]
    exact le_trans (le_max_right _ _) hY
  obtain ⟨hsum, hsmall⟩ := hY₀ s hx (le_trans (le_max_left _ _) hY)
  have hxi := F.xi_eq_tsum_Bn hc (a := 2) one_lt_two (F.JF c (3 - x₀) s)
  rw [hxi, F.tsum_Bn_J_eq hc hb hP hsum (a₀ := 2) two_pos,
    mul_div_cancel_left₀ _ (F.γtF_ne_zero hb hP), add_sub_cancel_left]
  exact hsmall

/-! ### The transfer -/

/-- The normalised function `h(w) = ξ_c(J_F(w)) / γ_t(w)`. -/
noncomputable def hfunF (c M₀ : ℝ) (w : ℂ) : ℂ :=
  F.flow (-c) (-I * (2 * F.JF c M₀ w - 1)) / F.γtF c M₀ w

lemma differentiableAt_ellF_shift {M₀ : ℝ} {w : ℂ} (hre : 0 < (w + M₀).re) :
    DifferentiableAt ℂ (fun v : ℂ => F.ellF (v + M₀)) w := by
  unfold ellF
  refine (differentiableAt_const _).add ?_
  have h : DifferentiableAt ℂ
      (∑ j : Fin F.r, fun v : ℂ => (F.lam j : ℂ) * log (F.lam j * (v + M₀) + F.mu j)) w := by
    refine DifferentiableAt.sum fun j _ => ?_
    refine DifferentiableAt.const_mul ?_ _
    refine DifferentiableAt.clog (by fun_prop) ?_
    exact mem_slitPlane_iff.mpr (Or.inl (F.re_lam_mul_add_mu_pos hre j))
  have heq : (∑ j : Fin F.r, fun v : ℂ => (F.lam j : ℂ) * log (F.lam j * (v + M₀) + F.mu j)) =
      fun v => ∑ j, (F.lam j : ℂ) * log (F.lam j * (v + M₀) + F.mu j) := by
    funext v
    simp [Finset.sum_apply]
  rwa [heq] at h

lemma differentiableAt_hfunF {c M₀ : ℝ} (hc : 0 < c) {w : ℂ} (hre : 0 < (w + M₀).re)
    (hP : F.P.eval (w + M₀) ≠ 0) : DifferentiableAt ℂ (F.hfunF c M₀) w := by
  have hell := F.differentiableAt_ellF_shift hre
  have hJ : DifferentiableAt ℂ (F.JF c M₀) w := by
    unfold JF
    exact differentiableAt_id.add (hell.const_mul _)
  have hγt : DifferentiableAt ℂ (F.γtF c M₀) w := by
    have h3 : DifferentiableAt ℂ
        (fun v : ℂ => -(M₀ : ℂ) * F.ellF (v + M₀) + (c / 4 : ℂ) * F.ellF (v + M₀) ^ 2) w :=
      (hell.const_mul _).add ((hell.pow 2).const_mul _)
    exact ((F.differentiableAt_gammaF hre).comp w (differentiableAt_id.add_const _)).mul h3.cexp
  have hH : DifferentiableAt ℂ (fun v : ℂ => F.flow (-c) (-I * (2 * F.JF c M₀ v - 1))) w :=
    (F.differentiable_flow hc).differentiableAt.comp w
      (((hJ.const_mul 2).sub_const 1).const_mul _)
  exact hH.div hγt (F.γtF_ne_zero hre hP)

/-- `Re J_F(w) = Re w + (c/2)(log Q + ∑_j λ_j log‖λ_j(w+M₀)+μ_j‖)`. -/
lemma re_JF (c M₀ : ℝ) (w : ℂ) :
    (F.JF c M₀ w).re =
      w.re + c / 2 * (Real.log F.Q + ∑ j, F.lam j * Real.log ‖F.lam j * (w + M₀) + F.mu j‖) := by
  have e : F.JF c M₀ w = w + ((c / 2 : ℝ) : ℂ) * F.ellF (w + M₀) := by
    rw [JF]
    push_cast
    ring
  rw [e, Complex.add_re, Complex.re_ofReal_mul, ellF, Complex.add_re, Complex.ofReal_re,
    Complex.re_sum]
  simp only [Complex.re_ofReal_mul, Complex.log_re]

lemma im_Z (c M₀ : ℝ) (w : ℂ) :
    (-I * (2 * F.JF c M₀ w - 1)).im = 1 - 2 * (F.JF c M₀ w).re := by
  simp [Complex.mul_im, Complex.sub_re, Complex.sub_im]

/-- Growth: `Re J_F(w) > 1/2` once `Im w` is large, uniformly for `Re w ≥ x₀ − 1`, because
`∑ λ_j > 0`. -/
lemma exists_re_JF_gt {c : ℝ} (hc : 0 < c) (M₀ x₀ : ℝ) :
    ∃ T : ℝ, ∀ w : ℂ, x₀ - 1 ≤ w.re → T ≤ w.im → 1 / 2 < (F.JF c M₀ w).re := by
  have hL : 0 < ∑ j, F.lam j := F.deg_pos
  have htend : Tendsto (fun y : ℝ =>
      (x₀ - 1 + c / 2 * (Real.log F.Q + ∑ j, F.lam j * Real.log (F.lam j / 2))) +
        c / 2 * ((∑ j, F.lam j) * Real.log y)) atTop atTop :=
    tendsto_atTop_add_const_left _ _
      ((Real.tendsto_log_atTop.const_mul_atTop hL).const_mul_atTop (by positivity))
  have h1 := htend.eventually_gt_atTop (1 / 2)
  have h2 : ∀ᶠ y : ℝ in atTop, 0 < y := eventually_gt_atTop 0
  have h3 : ∀ᶠ y : ℝ in atTop, ∀ j, 2 * ‖F.mu j‖ ≤ F.lam j * y := by
    rw [Filter.eventually_all]
    intro j
    have hlj := F.lam_pos j
    filter_upwards [eventually_ge_atTop (2 * ‖F.mu j‖ / F.lam j)] with y hy
    rw [div_le_iff₀ hlj] at hy
    linarith
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp ((h1.and h2).and h3)
  refine ⟨T, fun w hre hTw => ?_⟩
  obtain ⟨⟨hA, hy⟩, hmu⟩ := hT w.im hTw
  rw [F.re_JF]
  have hsum : ∑ j, F.lam j * Real.log (F.lam j / 2) + (∑ j, F.lam j) * Real.log w.im ≤
      ∑ j, F.lam j * Real.log ‖F.lam j * (w + M₀) + F.mu j‖ := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have hlj := F.lam_pos j
    rw [← mul_add, ← Real.log_mul (x := F.lam j / 2) (by positivity) hy.ne']
    refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) hlj.le
    have him : (F.lam j * (w + M₀) + F.mu j).im = F.lam j * w.im + (F.mu j).im := by simp
    have h2 := Complex.abs_im_le_norm (F.mu j)
    have h3 : (F.lam j * (w + M₀) + F.mu j).im ≤ ‖F.lam j * (w + M₀) + F.mu j‖ :=
      (le_abs_self _).trans (Complex.abs_im_le_norm _)
    have h4 := neg_abs_le (F.mu j).im
    rw [him] at h3
    have := hmu j
    linarith
  have hc2 : 0 ≤ c / 2 := by positivity
  have := mul_le_mul_of_nonneg_left hsum hc2
  linarith

/-- **Newman's conjecture for `F`** (after Dobner 2020), modulo `ErrorSumSmall`: for every
`t < 0`, `F.flow t` has a non-real zero. -/
theorem selberg_newman_of (herr : F.ErrorSumSmall) :
    ∀ t : ℝ, t < 0 → ∃ z : ℂ, F.flow t z = 0 ∧ z.im ≠ 0 := by
  intro t ht
  set c : ℝ := -t with hcdef
  have hc : 0 < c := by linarith
  have hc4 : 0 < c / 4 := by positivity
  have htc : t = -c := by rw [hcdef]; ring
  -- the zero of F_{c/4} and the strip around it
  obtain ⟨s₀, hs₀⟩ := F.exists_zero_Ft hc4
  set x₀ : ℝ := s₀.re with hx₀
  set M₀ : ℝ := 3 - x₀ with hM₀
  have hFdiff : Differentiable ℂ (F.Ft (c / 4)) := F.differentiable_Ft hc4
  have hFne : ∃ z, F.Ft (c / 4) z ≠ 0 := F.exists_Ft_ne_zero hc4
  -- Bohr's shifts
  obtain ⟨τ, hτ, hconv⟩ := DBNBohr.exists_shifts_tendstoLocallyUniformly (F.ftCoeff (c / 4))
    (F.lseriesSummable_ftCoeff hc4)
  have hconv' : TendstoLocallyUniformly (fun j s => F.Ft (c / 4) (s + (τ j : ℂ) * I))
    (F.Ft (c / 4)) atTop := hconv
  have hτ_top : Tendsto (fun j => (τ j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hτ.tendsto_atTop
  obtain ⟨R, hR⟩ := F.exists_im_bound_P_ne_zero
  obtain ⟨T₁, hT₁⟩ := F.exists_re_JF_gt hc M₀ x₀
  -- the shifted normalised functions
  set G : ℕ → ℂ → ℂ := fun j s => F.hfunF c M₀ (s + (τ j : ℂ) * I) with hGdef
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
  have habs := abs_le.mp (le_refl |s₀.im|)
  have habsR := le_abs_self R
  -- height threshold for differentiability: Re (s + τ_j i + M₀) > 0 and P ≠ 0 there, on U
  have hdiff : ∀ j : ℕ, |s₀.im| + 2 + |R| ≤ (τ j : ℝ) → DifferentiableOn ℂ (G j) U := by
    intro j hj s hs
    have h1 := him_ball s hs
    have h2 := hre_ball s hs
    have hxx := abs_le.mp h2
    refine (F.differentiableAt_hfunF hc (M₀ := M₀) ?_ ?_).comp s
      (differentiableAt_id.add_const _) |>.differentiableWithinAt
    · simp [hM₀]; linarith
    · apply hR
      simp
      linarith
  -- local uniform convergence of G j to F_{c/4} on U
  have hconvG : TendstoLocallyUniformlyOn G (F.Ft (c / 4)) atTop U := by
    rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε s hs
    obtain ⟨Y, hY⟩ := F.theorem4_of herr hc x₀ (half_pos hε)
    have hB := (Metric.tendstoLocallyUniformlyOn_iff.mp (hconv'.tendstoLocallyUniformlyOn (s := U)))
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
    calc dist (F.Ft (c / 4) y) (G j y)
        ≤ dist (F.Ft (c / 4) y) (F.Ft (c / 4) (y + (τ j : ℂ) * I)) +
          dist (F.Ft (c / 4) (y + (τ j : ℂ) * I)) (G j y) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by
          refine add_lt_add_of_lt_of_le hB' ?_
          rw [dist_eq_norm, norm_sub_rev]
          exact h4
      _ = ε := by ring
  -- Hurwitz: the shifted functions cannot all be zero-free on U
  have hnot : ¬ ∀ᶠ j in atTop, ∀ z ∈ U, G j z ≠ 0 := by
    intro hev
    have hF : ∀ᶠ j in atTop, DifferentiableOn ℂ (G j) U ∧ ∀ z ∈ U, G j z ≠ 0 := by
      filter_upwards [hτ_top.eventually_ge_atTop (|s₀.im| + 2 + |R|), hev] with j hj1 hj2
      exact ⟨hdiff j hj1, hj2⟩
    exact DBN.hurwitz_ne_zero isOpen_ball hF hFdiff hconvG hFne (mem_ball_self one_pos) hs₀
  rw [Filter.not_eventually] at hnot
  -- height threshold for the zero to be off the real axis
  set T : ℝ := max (|s₀.im| + 2 + |R|) (T₁ + |s₀.im| + 1) with hT
  have hev : ∀ᶠ j in atTop, T ≤ (τ j : ℝ) := hτ_top.eventually_ge_atTop T
  obtain ⟨j, hj, hjT⟩ := (hnot.and_eventually hev).exists
  push Not at hj
  obtain ⟨z, hzU, hGz⟩ := hj
  set w : ℂ := z + (τ j : ℂ) * I with hw
  have hzre := hre_ball z hzU
  have hzim := him_ball z hzU
  have hxx := abs_le.mp hzre
  have hwim' : w.im = z.im + τ j := by simp [hw]
  have hwre' : w.re = z.re := by simp [hw]
  have hT1 : |s₀.im| + 2 + |R| ≤ (τ j : ℝ) := le_trans (le_max_left _ _) hjT
  have hT2 : T₁ + |s₀.im| + 1 ≤ (τ j : ℝ) := le_trans (le_max_right _ _) hjT
  have hwre : 0 < (w + M₀).re := by
    simp only [Complex.add_re, Complex.ofReal_re, hwre', hM₀]
    linarith
  have hwP : F.P.eval (w + M₀) ≠ 0 := by
    apply hR
    simp only [Complex.add_im, Complex.ofReal_im, add_zero, hwim']
    linarith
  -- the zero of the flow
  have hH : F.flow (-c) (-I * (2 * F.JF c M₀ w - 1)) = 0 := by
    have : F.hfunF c M₀ w = 0 := hGz
    rw [hfunF, div_eq_zero_iff] at this
    exact this.resolve_right (F.γtF_ne_zero hwre hwP)
  refine ⟨-I * (2 * F.JF c M₀ w - 1), by rw [htc]; exact hH, ?_⟩
  rw [F.im_Z]
  have hJ := hT₁ w (by rw [hwre']; linarith) (by rw [hwim']; linarith)
  intro h0
  linarith

end ExtSelbergData

end DBNSelberg

/-! ### The unconditional theorem and the ζ control

`DBNSelbergSaddleSum.error_sum_small` is exactly `ErrorSumSmall F`, so the registered statement
follows. `zetaData` (DBNSelbergZeta) is the ζ instance; its flow is `DBN.H t` for `t < 0`, so the
general theorem recovers `dbn_newman` (DBNNewman) as a corollary: the control that the
generalization specializes to the proved ζ case. Nothing here is about `Λ_F = 0`. -/

/-- **Newman's conjecture for the extended Selberg class** (Dobner's theorem, in the form the dbn
island states it): for every `F : ExtSelbergData` and every `t < 0`, the heat flow `F.flow t` has a
non-real zero. The registered statement of node `RH_dbn_selberg_newman`. -/
theorem selberg_newman (F : DBNSelberg.ExtSelbergData) :
    ∀ t : ℝ, t < 0 → ∃ z : ℂ, F.flow t z = 0 ∧ z.im ≠ 0 :=
  F.selberg_newman_of F.error_sum_small

/-- The ζ control: the general theorem applied to `zetaData` recovers `dbn_newman`. -/
theorem dbn_newman_of_selberg : ∀ t : ℝ, t < 0 → ∃ z : ℂ, DBN.H t z = 0 ∧ z.im ≠ 0 :=
  DBNSelberg.dbn_newman_of_zetaData_newman (selberg_newman DBNSelberg.zetaData)
