/-
  DBNSaddleAlg -- the exact saddle-point bookkeeping for Dobner's Theorem 4.

  Step 5a of the Lambda >= 0 (Newman's conjecture) formalization; see
  NEWMAN_LAMBDA_NONNEG_SCOPING_2026-10-10.md section 6.

  With `b = s + M₀` (a base point with `Re b ≥ 1`), `ℓ(b) = ½ Log(b/2π)`, `J(s) = s + (c/2) ℓ(b)`,
  `γ_t(s) = γ(b) exp(-M₀ ℓ(b) + (c/4) ℓ(b)²)`, `h_n = (c/2) log n`, `a_n = exp(-h_n²/c) = exp(-(c/4) log²n)`,
  the `n`-th Gaussian-convolved term on the contour `Re v = Re b + h_n` is EXACTLY
      B_n(J(s)) = γ_t(s) · a_n n^{-s} · e^{M₀²/c} (πc)^{-1/2} ∫_ℝ K_n(σ) e^{-σ²/c + 2iM₀σ/c} dσ,
  where `K_n(σ) = ρ(δ) exp(Q(δ))`, `δ = h_n + iσ`, `ρ(δ) = (b+δ)(b+δ-1)/(b(b-1))` and
  `Q(δ) = L((b+δ)/2) - L(b/2) - (δ/2) Log(b/2)` with `DBNStirling.L` (so that
  `γ(b+δ) = γ(b) ρ(δ) exp(Q(δ) + δ ℓ(b))`).  Since `(πc)^{-1/2} ∫ e^{-σ²/c + 2iM₀σ/c} = e^{-M₀²/c}`,
      B_n(J(s)) = γ_t(s) a_n n^{-s} (1 + E_n(s)),   E_n = e^{M₀²/c}(πc)^{-1/2} ∫ (K_n - 1) e^{-σ²/c+2iM₀σ/c}.
  The analytic content (bounds on `K_n - 1`) is in the next module; this one is algebra, Fubini-free.

  Nothing here is RH.  conjecture1_proved = False.
-/
import Mathlib
import DBNStirling
import DBNGaussConv
import DBNFtZero

open Complex Filter Topology MeasureTheory Set
open scoped Real

namespace DBNSaddle

open DBNGaussConv DBNStirling

/-! ### Definitions -/

/-- `ℓ(b) = ½ (Log (b/2) − log π)`, i.e. `½ Log (b/(2π))`. -/
noncomputable def ell (b : ℂ) : ℂ := (1 / 2 : ℂ) * (log (b / 2) - (Real.log π : ℂ))

/-- Dobner's shift `J(s) = s + (c/2) ℓ(s + M₀)`. -/
noncomputable def J (c M₀ : ℝ) (s : ℂ) : ℂ := s + (c / 2 : ℂ) * ell (s + M₀)

/-- `γ_t(s) = γ(b) exp(−M₀ ℓ(b) + (c/4) ℓ(b)²)`, `b = s + M₀`. -/
noncomputable def γt (c M₀ : ℝ) (s : ℂ) : ℂ :=
  γ (s + M₀) * cexp (-(M₀ : ℂ) * ell (s + M₀) + (c / 4 : ℂ) * ell (s + M₀) ^ 2)

/-- `h_n = (c/2) log n`. -/
noncomputable def hh (c : ℝ) (n : ℕ+) : ℝ := c / 2 * Real.log n

/-- `a_n = exp (−h_n²/c) = exp (−(c/4) log² n)`. -/
noncomputable def coef (c : ℝ) (n : ℕ+) : ℝ := Real.exp (-(hh c n) ^ 2 / c)

/-- The polynomial ratio `ρ(δ) = (b+δ)(b+δ−1)/(b(b−1))`. -/
noncomputable def ρ (b δ : ℂ) : ℂ := (b + δ) * (b + δ - 1) / (b * (b - 1))

/-- `Q(δ) = L((b+δ)/2) − L(b/2) − (δ/2) Log(b/2)`. -/
noncomputable def Q (b δ : ℂ) : ℂ := L ((b + δ) / 2) - L (b / 2) - δ / 2 * log (b / 2)

/-- `δ_n(σ) = h_n + iσ`. -/
noncomputable def δ (c : ℝ) (n : ℕ+) (σ : ℝ) : ℂ := ((hh c n : ℝ) : ℂ) + σ * I

/-- `K_n(σ) = ρ(δ) exp(Q(δ))`. -/
noncomputable def K (c M₀ : ℝ) (n : ℕ+) (s : ℂ) (σ : ℝ) : ℂ :=
  ρ (s + M₀) (δ c n σ) * cexp (Q (s + M₀) (δ c n σ))

/-- The Gaussian weight `e^{-σ²/c + 2iM₀σ/c}`. -/
noncomputable def gw (c M₀ : ℝ) (σ : ℝ) : ℂ :=
  cexp (-(σ : ℂ) ^ 2 / c + 2 * (M₀ : ℂ) * σ * I / c)

/-- The relative error `E_n(s) = e^{M₀²/c} (πc)^{-1/2} ∫ (K_n(σ) − 1) gw(σ) dσ`. -/
noncomputable def E (c M₀ : ℝ) (n : ℕ+) (s : ℂ) : ℂ :=
  cexp ((M₀ ^ 2 / c : ℝ)) * (1 / ((Real.sqrt (π * c) : ℝ) : ℂ)) *
    ∫ σ : ℝ, (K c M₀ n s σ - 1) * gw c M₀ σ

/-! ### `γ` through Stirling's `L` -/

/-- `γ(v) = (1/16) v (v−1) exp(−(v/2) log π + L(v/2))` on `Re v > 0`. -/
theorem γ_eq_exp {v : ℂ} (hv : 0 < v.re) :
    γ v = (1 / 16 : ℂ) * v * (v - 1) * cexp (-(v / 2) * (Real.log π : ℂ) + L (v / 2)) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hre : 0 < (v / 2).re := by simp; linarith
  rw [γ, Gamma_eq_exp_L hre, cpow_def_of_ne_zero hπ, ← Complex.ofReal_log Real.pi_pos.le,
    mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- The ratio identity `γ(b+δ) = γ(b) ρ(δ) exp(Q(δ) + δ ℓ(b))`. -/
theorem γ_add_eq {b δ : ℂ} (hb : 0 < b.re) (hbδ : 0 < (b + δ).re) (hb0 : b ≠ 0) (hb1 : b - 1 ≠ 0) :
    γ (b + δ) = γ b * ρ b δ * cexp (Q b δ + δ * ell b) := by
  have key : -((b + δ) / 2) * (Real.log π : ℂ) + L ((b + δ) / 2) =
      (-(b / 2) * (Real.log π : ℂ) + L (b / 2)) + (Q b δ + δ * ell b) := by
    rw [Q, ell]; ring
  rw [γ_eq_exp hbδ, γ_eq_exp hb, key, Complex.exp_add, ρ]
  have hbb : b * (b - 1) ≠ 0 := mul_ne_zero hb0 hb1
  field_simp

/-! ### The per-`σ` identity -/

lemma one_div_cpow_eq (n : ℕ+) (w : ℂ) :
    (1 / (n : ℂ) ^ w) = cexp (-(Real.log n : ℂ) * w) := by
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  rw [cpow_def_of_ne_zero hn, one_div, ← Complex.exp_neg]
  congr 1
  rw [← Complex.natCast_log]
  ring

/-- `log n = 2 h_n / c`. -/
lemma log_eq_hh {c : ℝ} (hc : c ≠ 0) (n : ℕ+) : (Real.log n : ℂ) = 2 * (hh c n : ℂ) / c := by
  have : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  rw [hh]
  push_cast
  field_simp

lemma hh_nonneg {c : ℝ} (hc : 0 < c) (n : ℕ+) : 0 ≤ hh c n := by
  unfold hh
  have : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have := Real.log_nonneg this
  positivity

/-- **The exact per-`σ` identity.**  On the contour `Re v = Re s + M₀ + h_n`, parametrised by
`τ = Im s + σ`, the `B`-integrand at `J(s)` is
`γ_t(s) · a_n n^{-s} · e^{M₀²/c} · K_n(σ) gw(σ)`. -/
theorem BIntegrand_J_eq {c M₀ : ℝ} (hc : 0 < c) (n : ℕ+) {s : ℂ} (hb : 0 < (s + M₀).re)
    (hb0 : s + M₀ ≠ 0) (hb1 : s + M₀ - 1 ≠ 0) (σ : ℝ) :
    BIntegrand c (s.re + M₀ + hh c n) n (J c M₀ s) (s.im + σ) =
      γt c M₀ s * ((coef c n : ℂ) * (1 / (n : ℂ) ^ s)) *
        (cexp ((M₀ ^ 2 / c : ℝ)) * (K c M₀ n s σ * gw c M₀ σ)) := by
  set b : ℂ := s + M₀ with hbdef
  have hv : ((s.re + M₀ + hh c n : ℝ) : ℂ) + ((s.im + σ : ℝ) : ℂ) * I = b + δ c n σ := by
    rw [hbdef, δ]
    have := Complex.re_add_im s
    push_cast
    linear_combination this
  have hbδ : 0 < (b + δ c n σ).re := by
    rw [Complex.add_re, δ]
    simp
    linarith [hh_nonneg hc n]
  have hL : BIntegrand c (s.re + M₀ + hh c n) n (J c M₀ s) (s.im + σ) =
      γ b * ρ b (δ c n σ) * cexp ((Q b (δ c n σ) + δ c n σ * ell b) +
        (-(Real.log n : ℂ) * (b + δ c n σ)) + (b + δ c n σ - J c M₀ s) ^ 2 / c) := by
    rw [BIntegrand, hv, γ_add_eq hb hbδ hb0 hb1, one_div_cpow_eq]
    simp only [Complex.exp_add]
    ring
  have hR : γt c M₀ s * ((coef c n : ℂ) * (1 / (n : ℂ) ^ s)) *
      (cexp ((M₀ ^ 2 / c : ℝ)) * (K c M₀ n s σ * gw c M₀ σ)) =
      γ b * ρ b (δ c n σ) * cexp ((-(M₀ : ℂ) * ell b + (c / 4 : ℂ) * ell b ^ 2) +
        ((-(hh c n) ^ 2 / c : ℝ) : ℂ) + (-(Real.log n : ℂ) * s) + ((M₀ ^ 2 / c : ℝ) : ℂ) +
        Q b (δ c n σ) + (-(σ : ℂ) ^ 2 / c + 2 * (M₀ : ℂ) * σ * I / c)) := by
    rw [γt, coef, K, gw, one_div_cpow_eq, Complex.ofReal_exp]
    simp only [Complex.exp_add]
    rw [← hbdef]
    ring
  rw [hL, hR]
  congr 2
  rw [J, ← hbdef, log_eq_hh hc.ne']
  simp only [δ]
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

/-! ### The integrated identity -/

lemma γt_ne_zero {c M₀ : ℝ} {s : ℂ} (hb : 0 < (s + M₀).re) (hb0 : s + M₀ ≠ 0)
    (hb1 : s + M₀ - 1 ≠ 0) : γt c M₀ s ≠ 0 := by
  rw [γt, γ_eq_exp hb]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hb0) hb1)
    (Complex.exp_ne_zero _)) (Complex.exp_ne_zero _)

lemma coef_pos (c : ℝ) (n : ℕ+) : 0 < coef c n := Real.exp_pos _

lemma gw_eq (c M₀ : ℝ) (σ : ℝ) :
    gw c M₀ σ = cexp ((-(1 / c) : ℂ) * (σ : ℂ) ^ 2 + (2 * (M₀ : ℂ) * I / c) * σ + 0) := by
  rw [gw]
  congr 1
  ring

lemma integrable_gw {c : ℝ} (hc : 0 < c) (M₀ : ℝ) : Integrable (gw c M₀) := by
  have h := integrable_cexp_quadratic' (b := (-(1 / c) : ℂ)) (by simp; positivity)
    (2 * (M₀ : ℂ) * I / c) 0
  exact h.congr (ae_of_all _ fun σ => (gw_eq c M₀ σ).symm)

/-- `(πc)^{-1/2} ∫ gw = e^{-M₀²/c}`. -/
lemma integral_gw {c : ℝ} (hc : 0 < c) (M₀ : ℝ) :
    (1 / ((Real.sqrt (π * c) : ℝ) : ℂ)) * ∫ σ : ℝ, gw c M₀ σ = cexp (-(M₀ ^ 2 / c : ℝ)) := by
  simp_rw [gw_eq]
  rw [integral_cexp_quadratic (b := (-(1 / c) : ℂ)) (by simp; positivity)]
  have hsq : ((π : ℂ) / -(-(1 / c) : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt (π * c) : ℝ) : ℂ) := by
    rw [show (π : ℂ) / -(-(1 / c) : ℂ) = (((π * c : ℝ)) : ℂ) by push_cast; field_simp,
      Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    norm_num
  rw [hsq]
  have hne : ((Real.sqrt (π * c) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity)).ne'
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [← mul_assoc, one_div, inv_mul_cancel₀ hne, one_mul]
  congr 1
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- **The integrated identity**: `B_n(J(s)) = γ_t(s) a_n n^{-s} (1 + E_n(s))` on the contour
`Re v = Re s + M₀ + h_n`. -/
theorem B_J_eq {c M₀ : ℝ} (hc : 0 < c) (n : ℕ+) {s : ℂ} (hb : 0 < (s + M₀).re)
    (hb0 : s + M₀ ≠ 0) (hb1 : s + M₀ - 1 ≠ 0) :
    B c (s.re + M₀ + hh c n) n (J c M₀ s) =
      γt c M₀ s * ((coef c n : ℂ) * (1 / (n : ℂ) ^ s)) * (1 + E c M₀ n s) := by
  have hb' : 0 < s.re + M₀ := by simpa using hb
  set C : ℂ := γt c M₀ s * ((coef c n : ℂ) * (1 / (n : ℂ) ^ s)) * cexp ((M₀ ^ 2 / c : ℝ)) with hC
  have hC0 : C ≠ 0 := by
    rw [hC]
    refine mul_ne_zero (mul_ne_zero (γt_ne_zero hb hb0 hb1) (mul_ne_zero ?_ ?_)) (Complex.exp_ne_zero _)
    · exact_mod_cast (coef_pos c n).ne'
    · rw [one_div]
      refine inv_ne_zero ?_
      rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
      left
      exact_mod_cast n.ne_zero
  -- B as an integral over σ of C · K · gw
  have hpt : ∀ σ : ℝ, BIntegrand c (s.re + M₀ + hh c n) n (J c M₀ s) (s.im + σ) =
      C * (K c M₀ n s σ * gw c M₀ σ) := by
    intro σ
    rw [BIntegrand_J_eq hc n hb hb0 hb1 σ, hC]
    ring
  have hint : Integrable fun σ : ℝ => K c M₀ n s σ * gw c M₀ σ := by
    have h1 : Integrable fun σ : ℝ => BIntegrand c (s.re + M₀ + hh c n) n (J c M₀ s) (s.im + σ) :=
      (integrable_BIntegrand hc (by linarith [hh_nonneg hc n]) n (J c M₀ s)).comp_add_left s.im
    simp_rw [hpt] at h1
    exact (integrable_const_mul_iff (IsUnit.mk0 _ hC0) _).mp h1
  have hB : B c (s.re + M₀ + hh c n) n (J c M₀ s) =
      (1 / ((Real.sqrt (π * c) : ℝ) : ℂ)) * ∫ σ : ℝ, C * (K c M₀ n s σ * gw c M₀ σ) := by
    rw [B]
    congr 1
    rw [← integral_add_left_eq_self _ s.im]
    exact integral_congr_ae (ae_of_all _ fun σ => hpt σ)
  rw [hB, integral_const_mul, E]
  have hsplit : ∫ σ : ℝ, (K c M₀ n s σ - 1) * gw c M₀ σ =
      (∫ σ : ℝ, K c M₀ n s σ * gw c M₀ σ) - ∫ σ : ℝ, gw c M₀ σ := by
    rw [← integral_sub hint (integrable_gw hc M₀)]
    congr 1
    funext σ
    ring
  rw [hsplit, hC]
  have hg := integral_gw hc M₀
  have this : cexp ((M₀ ^ 2 / c : ℝ)) * cexp (-(M₀ ^ 2 / c : ℝ)) = 1 := by
    rw [← Complex.exp_add]; simp
  linear_combination (γt c M₀ s * ((coef c n : ℂ) * (1 / (n : ℂ) ^ s)) * cexp ((M₀ ^ 2 / c : ℝ))) * hg
    + (γt c M₀ s * ((coef c n : ℂ) * (1 / (n : ℂ) ^ s))) * this

/-! ### Moving the contour of `B` -/

/-- The integrand of `B` as a function of the complex variable `v`. -/
noncomputable def Fv (c : ℝ) (n : ℕ+) (s : ℂ) (v : ℂ) : ℂ :=
  γ v * (1 / (n : ℂ) ^ v) * cexp ((v - s) ^ 2 / c)

lemma BIntegrand_eq_Fv (c a : ℝ) (n : ℕ+) (s : ℂ) (τ : ℝ) :
    BIntegrand c a n s τ = Fv c n s ((a : ℂ) + τ * I) := rfl

lemma differentiableAt_γ {v : ℂ} (hv : 0 < v.re) : DifferentiableAt ℂ γ v := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hΓ : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w / 2)) v := by
    refine (Complex.differentiableAt_Gamma _ fun m => ?_).comp v (differentiableAt_id.div_const 2)
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hp : DifferentiableAt ℂ (fun w : ℂ => (π : ℂ) ^ (-w / 2)) v :=
    (differentiableAt_id.neg.div_const 2).const_cpow (Or.inl hπ)
  unfold γ
  exact ((((differentiableAt_const _).mul differentiableAt_id).mul
    (differentiableAt_id.sub_const 1)).mul hp).mul hΓ

lemma differentiableAt_Fv (c : ℝ) (n : ℕ+) (s : ℂ) {v : ℂ} (hv : 0 < v.re) :
    DifferentiableAt ℂ (Fv c n s) v := by
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  have h1 : DifferentiableAt ℂ (fun w : ℂ => 1 / (n : ℂ) ^ w) v := by
    refine (differentiableAt_const _).div (differentiableAt_id.const_cpow (Or.inl hn)) ?_
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl hn
  unfold Fv
  exact ((differentiableAt_γ hv).mul h1).mul
    ((((differentiableAt_id.sub_const s).pow 2).div_const _).cexp)

/-- `π^{-x/2} Γ(x/2)` is bounded on `[a, a']` for `0 < a`. -/
lemma exists_gamma_bound {a a' : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, ∀ x ∈ Icc a a', π ^ (-x / 2) * Real.Gamma (x / 2) ≤ C := by
  have hcont : ContinuousOn (fun x : ℝ => π ^ (-x / 2) * Real.Gamma (x / 2)) (Icc a a') := by
    intro x hx
    refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ ?_)
    · exact (Real.continuousAt_const_rpow Real.pi_pos.ne').comp (by fun_prop)
    · refine (Real.differentiableAt_Gamma fun m => ?_).continuousAt.comp (by fun_prop)
      intro h
      have := hx.1
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn hcont).bddAbove
  exact ⟨C, fun x hx => hC ⟨x, hx, rfl⟩⟩

/-- The horizontal bound for `Fv` on the rectangle: `x ∈ [a, a']`, `|y| ≥ |Im s|`. -/
lemma norm_Fv_le {c : ℝ} (hc : 0 < c) {a a' : ℝ} (ha : 0 < a) (n : ℕ+) (s : ℂ) {Cγ : ℝ}
    (hCγ : ∀ x ∈ Icc a a', π ^ (-x / 2) * Real.Gamma (x / 2) ≤ Cγ) {x : ℝ} (hx : x ∈ Icc a a')
    {y : ℝ} (hy : |s.im| ≤ |y|) :
    ‖Fv c n s ((x : ℂ) + y * I)‖ ≤
      (1 / 16) * (a' + |y|) * (a' + |y| + 1) * Cγ *
        Real.exp (((a' + |s.re|) ^ 2 - (|y| - |s.im|) ^ 2) / c) := by
  have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
  have ha' : 0 < a' := lt_of_lt_of_le hx0 hx.2
  have hΓa : 0 ≤ Real.Gamma (a / 2) := Real.Gamma_nonneg_of_nonneg (by positivity)
  have hCγ0 : 0 ≤ Cγ := le_trans (mul_nonneg (by positivity) hΓa) (hCγ a ⟨le_rfl, le_trans hx.1 hx.2⟩)
  have h := norm_BIntegrand_le c hx0 n s y
  rw [BIntegrand_eq_Fv] at h
  refine h.trans ?_
  have hn : (n : ℝ) ^ (-x) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast n.pos) (by linarith)
  have hG := hCγ x hx
  have hΓ0 : 0 ≤ Real.Gamma (x / 2) := Real.Gamma_nonneg_of_nonneg (by positivity)
  have hexp : Real.exp (((x - s.re) ^ 2 - (y - s.im) ^ 2) / c) ≤
      Real.exp (((a' + |s.re|) ^ 2 - (|y| - |s.im|) ^ 2) / c) := by
    apply Real.exp_le_exp.mpr
    refine div_le_div_of_nonneg_right ?_ hc.le
    have h1 : (x - s.re) ^ 2 ≤ (a' + |s.re|) ^ 2 := by
      have : |x - s.re| ≤ a' + |s.re| := by
        calc |x - s.re| ≤ |x| + |s.re| := abs_sub _ _
          _ ≤ a' + |s.re| := by rw [abs_of_pos hx0]; linarith [hx.2]
      nlinarith [abs_nonneg (x - s.re), sq_abs (x - s.re), abs_nonneg s.re]
    have h2 : (|y| - |s.im|) ^ 2 ≤ (y - s.im) ^ 2 := by
      have : |y| - |s.im| ≤ |y - s.im| := abs_sub_abs_le_abs_sub _ _
      have h0 : 0 ≤ |y| - |s.im| := by linarith
      nlinarith [sq_abs (y - s.im), abs_nonneg (y - s.im)]
    linarith
  have hy0 : 0 ≤ |y| := abs_nonneg y
  have h1 : (x + |y|) * (x + |y| + 1) ≤ (a' + |y|) * (a' + |y| + 1) :=
    mul_le_mul (by linarith [hx.2]) (by linarith [hx.2]) (by positivity) (by linarith)
  have hA : 0 ≤ (a' + |y|) * (a' + |y| + 1) := mul_nonneg (by linarith) (by linarith)
  calc (1 / 16) * (x + |y|) * (x + |y| + 1) * π ^ (-x / 2) * Real.Gamma (x / 2) * (n : ℝ) ^ (-x) *
        Real.exp (((x - s.re) ^ 2 - (y - s.im) ^ 2) / c)
      = (1 / 16) * ((x + |y|) * (x + |y| + 1)) * (π ^ (-x / 2) * Real.Gamma (x / 2)) *
          (n : ℝ) ^ (-x) * Real.exp (((x - s.re) ^ 2 - (y - s.im) ^ 2) / c) := by ring
    _ ≤ (1 / 16) * ((a' + |y|) * (a' + |y| + 1)) * Cγ * 1 *
          Real.exp (((a' + |s.re|) ^ 2 - (|y| - |s.im|) ^ 2) / c) := by
        refine mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) hG
          (mul_nonneg (by positivity) hΓ0) (mul_nonneg (by norm_num) hA)) hn (by positivity)
          (mul_nonneg (mul_nonneg (by norm_num) hA) hCγ0)) hexp (Real.exp_pos _).le ?_
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA) hCγ0) zero_le_one
    _ = _ := by ring

/-- **The contour of `B` may be moved**: `B c a n s = B c a' n s` for `0 < a ≤ a'`. -/
theorem B_shift {c : ℝ} (hc : 0 < c) {a a' : ℝ} (ha : 0 < a) (haa : a ≤ a') (n : ℕ+) (s : ℂ) :
    B c a n s = B c a' n s := by
  unfold B
  congr 1
  show (∫ τ : ℝ, Fv c n s ((a : ℂ) + τ * I)) = ∫ τ : ℝ, Fv c n s ((a' : ℂ) + τ * I)
  have ha' : 0 < a' := lt_of_lt_of_le ha haa
  obtain ⟨Cγ, hCγ⟩ := exists_gamma_bound (a' := a') ha
  -- the rectangle identity
  have hrect : ∀ T : ℝ,
      (∫ x in a..a', Fv c n s (x + -(T : ℂ) * I)) - (∫ x in a..a', Fv c n s (x + T * I)) =
        I * (∫ y in (-T)..T, Fv c n s (a + y * I)) - I * (∫ y in (-T)..T, Fv c n s (a' + y * I)) := by
    intro T
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (Fv c n s) ⟨a, -T⟩ ⟨a', T⟩
      (fun v hv => by
        refine (differentiableAt_Fv c n s ?_).differentiableWithinAt
        have := (Complex.mem_reProdIm.mp hv).1
        change v.re ∈ uIcc a a' at this
        rw [uIcc_of_le haa] at this
        linarith [this.1])
    simp only [smul_eq_mul, Complex.ofReal_neg] at h
    linear_combination h
  -- the horizontal sides tend to zero
  have hD : 0 ≤ (a' + |s.re|) ^ 2 := sq_nonneg _
  have hΓa : 0 ≤ Real.Gamma (a / 2) := Real.Gamma_nonneg_of_nonneg (by positivity)
  have hCγ0 : 0 ≤ Cγ := le_trans (mul_nonneg (by positivity) hΓa) (hCγ a ⟨le_rfl, haa⟩)
  have hhoriz : ∀ T : ℝ, |s.im| ≤ T → ∀ y : ℝ, |y| = T →
      ‖∫ x in a..a', Fv c n s (x + y * I)‖ ≤
        ((1 / 16) * (a' + T) * (a' + T + 1) * Cγ *
          Real.exp (((a' + |s.re|) ^ 2 - (T - |s.im|) ^ 2) / c)) * |a' - a| := by
    intro T hT y hy
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [uIoc_of_le haa] at hx
    have hx' : x ∈ Icc a a' := ⟨hx.1.le, hx.2⟩
    have := norm_Fv_le hc ha n s hCγ hx' (y := y) (by rw [hy]; exact hT)
    rwa [hy] at this
  -- the bound decays like e^{-T}
  set D : ℝ := (a' + |s.re|) ^ 2 with hDdef
  have hdecay : ∀ T : ℝ, |s.im| + 3 * c ≤ T →
      (1 / 16) * (a' + T) * (a' + T + 1) * Cγ * Real.exp ((D - (T - |s.im|) ^ 2) / c) ≤
        (Cγ * Real.exp (D / c + 3 * |s.im| + 2 * (a' + 1))) * Real.exp (-T) := by
    intro T hT
    have hT0 : 0 ≤ T := by linarith [abs_nonneg s.im]
    have hpoly : (a' + T) * (a' + T + 1) ≤ Real.exp (2 * (a' + T + 1)) := by
      have h1 : a' + T + 1 ≤ Real.exp (a' + T + 1) := by
        have := Real.add_one_le_exp (a' + T + 1); linarith
      calc (a' + T) * (a' + T + 1) ≤ (a' + T + 1) * (a' + T + 1) :=
            mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        _ ≤ Real.exp (a' + T + 1) * Real.exp (a' + T + 1) :=
            mul_le_mul h1 h1 (by linarith) (Real.exp_pos _).le
        _ = Real.exp (2 * (a' + T + 1)) := by rw [← Real.exp_add]; ring_nf
    have hsq : 3 * (T - |s.im|) ≤ (T - |s.im|) ^ 2 / c := by
      rw [le_div_iff₀ hc]
      nlinarith
    have hexp : Real.exp ((D - (T - |s.im|) ^ 2) / c) ≤ Real.exp (D / c - 3 * (T - |s.im|)) := by
      apply Real.exp_le_exp.mpr
      rw [sub_div]
      linarith
    calc (1 / 16) * (a' + T) * (a' + T + 1) * Cγ * Real.exp ((D - (T - |s.im|) ^ 2) / c)
        ≤ 1 * Real.exp (2 * (a' + T + 1)) * Cγ * Real.exp (D / c - 3 * (T - |s.im|)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right ?_ hCγ0) hexp (Real.exp_pos _).le
            (by positivity)
          calc (1 / 16) * (a' + T) * (a' + T + 1) ≤ 1 * ((a' + T) * (a' + T + 1)) := by
                nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ a' + T) (by linarith : (0:ℝ) ≤ a' + T + 1)]
            _ ≤ 1 * Real.exp (2 * (a' + T + 1)) := by linarith
      _ = (Cγ * Real.exp (D / c + 3 * |s.im| + 2 * (a' + 1))) * Real.exp (-T) := by
          rw [one_mul, show Real.exp (2 * (a' + T + 1)) * Cγ * Real.exp (D / c - 3 * (T - |s.im|)) =
            Cγ * Real.exp (2 * (a' + T + 1) + (D / c - 3 * (T - |s.im|))) by
              rw [Real.exp_add]; ring, mul_assoc, ← Real.exp_add]
          congr 2
          ring
  have hzero : Tendsto (fun T : ℝ => ((Cγ * Real.exp (D / c + 3 * |s.im| + 2 * (a' + 1))) *
      Real.exp (-T)) * |a' - a|) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul
      (Cγ * Real.exp (D / c + 3 * |s.im| + 2 * (a' + 1)))).mul_const |a' - a|
    simpa using this
  have hside_pos : Tendsto (fun T : ℝ => ∫ x in a..a', Fv c n s (x + T * I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hzero
    filter_upwards [eventually_ge_atTop (|s.im| + 3 * c)] with T hT
    have hT' : |s.im| ≤ T := by linarith
    have hyT : |T| = T := abs_of_nonneg (by linarith [abs_nonneg s.im])
    exact (hhoriz T hT' T hyT).trans (mul_le_mul_of_nonneg_right (hdecay T hT) (abs_nonneg _))
  have hside_neg : Tendsto (fun T : ℝ => ∫ x in a..a', Fv c n s (x + -(T : ℂ) * I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hzero
    filter_upwards [eventually_ge_atTop (|s.im| + 3 * c)] with T hT
    have hT' : |s.im| ≤ T := by linarith
    have hyT : |-T| = T := by rw [abs_neg]; exact abs_of_nonneg (by linarith [abs_nonneg s.im])
    have := (hhoriz T hT' (-T) hyT).trans (mul_le_mul_of_nonneg_right (hdecay T hT) (abs_nonneg _))
    simpa only [Complex.ofReal_neg] using this
  -- the vertical sides converge to the full-line integrals
  have hV : ∀ b : ℝ, 0 < b → Tendsto (fun T : ℝ => ∫ y in (-T)..T, Fv c n s (b + y * I)) atTop
      (𝓝 (∫ y : ℝ, Fv c n s (b + y * I))) := fun b hb =>
    intervalIntegral_tendsto_integral (integrable_BIntegrand hc hb n s) tendsto_neg_atTop_atBot
      tendsto_id
  have hL : Tendsto (fun T : ℝ => I * (∫ y in (-T)..T, Fv c n s (a + y * I)) -
      I * (∫ y in (-T)..T, Fv c n s (a' + y * I))) atTop
      (𝓝 (I * (∫ y : ℝ, Fv c n s (a + y * I)) - I * (∫ y : ℝ, Fv c n s (a' + y * I)))) :=
    ((hV a ha).const_mul I).sub ((hV a' ha').const_mul I)
  have hR : Tendsto (fun T : ℝ => I * (∫ y in (-T)..T, Fv c n s (a + y * I)) -
      I * (∫ y in (-T)..T, Fv c n s (a' + y * I))) atTop (𝓝 0) := by
    simp_rw [← hrect]
    simpa using hside_neg.sub hside_pos
  have := tendsto_nhds_unique hL hR
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h' : (∫ y : ℝ, Fv c n s (a + y * I)) - ∫ y : ℝ, Fv c n s (a' + y * I) = 0 := by
    have : I * ((∫ y : ℝ, Fv c n s (a + y * I)) - ∫ y : ℝ, Fv c n s (a' + y * I)) = 0 := by
      rw [mul_sub]; exact this
    exact (mul_eq_zero.mp this).resolve_left hI
  exact sub_eq_zero.mp h'

/-! ### Summation over `n` -/

/-- `a_n` is the `n`-th Gaussian coefficient of `DBNFtZero.F (c/4)`. -/
lemma coef_eq_gaussCoeff {c : ℝ} (hc : 0 < c) (n : ℕ+) :
    (coef c n : ℂ) = DBNFtZero.gaussCoeff (c / 4) n := by
  rw [coef, hh, DBNFtZero.gaussCoeff]
  congr 2
  field_simp
  ring

lemma summable_coef_term {c : ℝ} (hc : 0 < c) (s : ℂ) :
    Summable fun n : ℕ+ => (coef c n : ℂ) * (1 / (n : ℂ) ^ s) := by
  have h := DBNFtZero.lseriesSummable (by positivity : (0 : ℝ) < c / 4) s
  have h2 := (summable_pnat_iff_summable_nat
    (f := fun n : ℕ => LSeries.term (DBNFtZero.gaussCoeff (c / 4)) s n)).mpr h
  refine h2.congr fun n => ?_
  rw [LSeries.term_of_ne_zero n.ne_zero, coef_eq_gaussCoeff hc]
  ring

/-- `∑_{n ≥ 1} a_n n^{-s} = F_{c/4}(s)` (Dobner's `F_t` with `|t| = c`). -/
lemma tsum_coef_eq_F {c : ℝ} (hc : 0 < c) (s : ℂ) :
    ∑' n : ℕ+, (coef c n : ℂ) * (1 / (n : ℂ) ^ s) = DBNFtZero.F (c / 4) s := by
  rw [DBNFtZero.F, LSeries, (DBNFtZero.lseriesSummable (by positivity) s).tsum_eq_zero_add,
    LSeries.term_zero, zero_add,
    ← tsum_pnat_eq_tsum_succ (f := fun n : ℕ => LSeries.term (DBNFtZero.gaussCoeff (c / 4)) s n)]
  congr 1
  funext n
  rw [LSeries.term_of_ne_zero n.ne_zero, coef_eq_gaussCoeff hc]
  ring

/-- **Theorem 4, exact form**: `ξ_c(J(s)) = γ_t(s) (F_{c/4}(s) + ∑_n a_n n^{-s} E_n(s))`, given that
the error series converges. -/
theorem xi_J_eq {c M₀ : ℝ} (hc : 0 < c) {s : ℂ} (hb : 0 < (s + M₀).re) (hb0 : s + M₀ ≠ 0)
    (hb1 : s + M₀ - 1 ≠ 0)
    (hsum : Summable fun n : ℕ+ => (coef c n : ℂ) * (1 / (n : ℂ) ^ s) * E c M₀ n s) :
    DBN.H (-c) (-I * (2 * J c M₀ s - 1)) =
      γt c M₀ s * (DBNFtZero.F (c / 4) s +
        ∑' n : ℕ+, (coef c n : ℂ) * (1 / (n : ℂ) ^ s) * E c M₀ n s) := by
  have hb' : 0 < s.re + M₀ := by simpa using hb
  set a₀ : ℝ := max 2 (s.re + M₀) with ha₀
  have ha₀1 : 1 < a₀ := lt_of_lt_of_le one_lt_two (le_max_left _ _)
  rw [xi_eq_tsum_B hc ha₀1 (J c M₀ s)]
  have hterm : ∀ n : ℕ+, B c a₀ n (J c M₀ s) =
      γt c M₀ s * ((coef c n : ℂ) * (1 / (n : ℂ) ^ s)) +
        γt c M₀ s * ((coef c n : ℂ) * (1 / (n : ℂ) ^ s) * E c M₀ n s) := by
    intro n
    rcases le_total a₀ (s.re + M₀ + hh c n) with h | h
    · rw [B_shift hc (by linarith) h n, B_J_eq hc n hb hb0 hb1]
      ring
    · rw [← B_shift hc (by linarith [hh_nonneg hc n]) h n, B_J_eq hc n hb hb0 hb1]
      ring
  simp_rw [hterm]
  rw [((summable_coef_term hc s).mul_left _).tsum_add (hsum.mul_left _), tsum_mul_left,
    tsum_mul_left, tsum_coef_eq_F hc, mul_add]

end DBNSaddle
