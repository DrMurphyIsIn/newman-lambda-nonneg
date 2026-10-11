/-
  DBNSelbergSaddleSum -- integrating the saddle-point estimates and summing over `n`, for an
  element `F` of the extended Selberg class.

  Generalizes DBNSaddleSum (the ζ case) from `aFar`/`A₁`/`A₂`/`near_majorant`/`far_majorant`/
  `norm_E_le` through `error_sum_small`; see SELBERG_NEWMAN_DESIGN_2026-10-10.md (row
  "DBNSaddleSum -> DBNSelbergSaddleSum").  Fix `c > 0`, a strip centre `x₀`, and the base shift
  `M₀ = 3 − x₀` (so `2 ≤ Re b ≤ 4` on the strip `|Re s − x₀| ≤ 1`, `b = s + M₀`).

  * The unified pointwise bound of DBNSelbergSaddleBounds,
        ‖K_n(σ) − 1‖ ≤ NbF(y,h,σ) + e^{((h+|σ|)² − y²/4)/(8c)} (1 + GbF(y,h,σ)),
    is integrated against `e^{-σ²/c}`.  Once `y ≥ 8c·CN` the near-field exponential
    `e^{CN(1+h+|σ|)²/y}` is dominated by the Gaussian, and both pieces take the form
    `A(y,h) (1+|σ|)^k e^{-(3/(4c))σ² + a|σ|}` with `k = deg P + 2`.
  * Absorbing `a_n = e^{-h²/c}` (for `y ≥ 8c(CN + CG)`) leaves
        ‖a(n) a_n n^{-s} E_n(s)‖ ≤ C₁ ‖a(n)‖ (1+h)^k e^{-h²/(2c)} n^{1-x₀} / y
                                  + C₂ ‖a(n)‖ (1+h)^k e^{-11h²/(24c)} n^{1-x₀} e^{-y²/(32c) + πΛy},
    `Λ = ∑ λ_j`.  The weights are summable because `(1+h)^k e^{-κh²} n^{β+2}` is bounded in `n`
    and `∑ ‖a(n)‖ n^{-2} < ∞` (the `summable` field at `s = 2`).
  * Hence `∑_n ‖a(n) a_n n^{-s} E_n(s)‖ → 0` as `y → ∞`, uniformly on the strip: `error_sum_small`,
    whose statement is the body of `DBNSelberg.ExtSelbergData.ErrorSumSmall` (DBNSelbergNewman).

  Nothing here is RH.  conjecture1_proved = False.
-/
import Mathlib
import DBNSelbergData
import DBNSelbergSaddleBounds
import DBNSelbergSaddleAlg
import DBNSelbergGauss
import DBNSaddleSum
import DBNSaddleAlg

open Complex Filter Topology MeasureTheory Set
open scoped Real

namespace DBNSelberg

open DBNGaussConv DBNStirling DBNSaddle

/-! ### Gaussian-polynomial integrals of arbitrary degree -/

/-- `Igk k b a = e^{(a+k)²/(2b)} √(π/(b/2))`, the bound of `integral_gauss_poly_le`. -/
noncomputable def Igk (k : ℕ) (b a : ℝ) : ℝ := Real.exp ((a + k) ^ 2 / (2 * b)) * Real.sqrt (π / (b / 2))

lemma Igk_nonneg (k : ℕ) (b a : ℝ) : 0 ≤ Igk k b a := by unfold Igk; positivity

lemma integral_gauss_poly_le_Igk {b : ℝ} (hb : 0 < b) (a : ℝ) (k : ℕ) :
    ∫ σ : ℝ, (1 + |σ|) ^ k * Real.exp (-b * σ ^ 2 + a * |σ|) ≤ Igk k b a :=
  integral_gauss_poly_le hb a k

/-- `(1 + h + |σ|)^k ≤ (1+h)^k (1+|σ|)^k` for `h ≥ 0`. -/
lemma one_add_add_abs_pow_le {h : ℝ} (hh0 : 0 ≤ h) (σ : ℝ) (k : ℕ) :
    (1 + h + |σ|) ^ k ≤ (1 + h) ^ k * (1 + |σ|) ^ k := by
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ k
  nlinarith [abs_nonneg σ, mul_nonneg hh0 (abs_nonneg σ)]

namespace ExtSelbergData

variable (F : ExtSelbergData)

lemma Lam_pos : 0 < ∑ j, F.lam j := F.deg_pos

/-! ### The majorants in Gaussian-polynomial form -/

/-- The far-field linear coefficient `a = CG(1+h)/y + πΛ`. -/
noncomputable def aFarF (y h : ℝ) : ℝ := F.CG * (1 + h) / y + π * (∑ j, F.lam j)

/-- Near-field amplitude `A₁F = CN (1+h)^k / y · e^{2 CN (1+h)²/y}`. -/
noncomputable def A₁F (y h : ℝ) : ℝ :=
  F.CN * (1 + h) ^ (F.P.natDegree + 2) / y * Real.exp (2 * F.CN * (1 + h) ^ 2 / y)

/-- Far-field amplitude
`A₂F = e^{-y²/(32c)} e^{h²/(4c)} · (1 + CG) (1+h)^k e^{CG(1+h)h/y + πΛy + CG}`. -/
noncomputable def A₂F (c y h : ℝ) : ℝ :=
  Real.exp (-y ^ 2 / (32 * c)) * Real.exp (h ^ 2 / (4 * c)) *
    ((1 + F.CG) * (1 + h) ^ (F.P.natDegree + 2) * Real.exp (F.CG * (1 + h) * h / y + π * (∑ j, F.lam j) * y + F.CG))

lemma aFarF_nonneg {y : ℝ} (hy : 0 < y) {h : ℝ} (hh0 : 0 ≤ h) : 0 ≤ F.aFarF y h := by
  unfold aFarF
  have := F.CG_nonneg
  have := F.Lam_pos
  have := Real.pi_pos
  positivity

lemma A₁F_nonneg {y : ℝ} (hy : 0 < y) {h : ℝ} (hh0 : 0 ≤ h) : 0 ≤ F.A₁F y h := by
  unfold A₁F
  have := F.CN_nonneg
  positivity

lemma A₂F_nonneg (c y : ℝ) {h : ℝ} (hh0 : 0 ≤ h) : 0 ≤ F.A₂F c y h := by
  unfold A₂F
  have := F.CG_nonneg
  positivity

/-- The near-field majorant in Gaussian-polynomial form, for `y ≥ 8c·CN`. -/
lemma near_majorant {c : ℝ} (hc : 0 < c) {y : ℝ} (hyN : 8 * c * F.CN ≤ y) {h : ℝ} (hh0 : 0 ≤ h)
    (σ : ℝ) :
    Real.exp (-σ ^ 2 / c) * F.NbF y h σ ≤
      F.A₁F y h * ((1 + |σ|) ^ (F.P.natDegree + 2) * Real.exp (-(3 / (4 * c)) * σ ^ 2 + 0 * |σ|)) := by
  have hCN := F.one_le_CN
  have hCN0 := F.CN_nonneg
  have hy : 0 < y := by nlinarith
  have hσ := abs_nonneg σ
  have hsq : |σ| ^ 2 = σ ^ 2 := sq_abs σ
  have hpow := one_add_add_abs_pow_le hh0 σ (F.P.natDegree + 2)
  have hexp : -σ ^ 2 / c + F.CN * (1 + h + |σ|) ^ 2 / y ≤
      2 * F.CN * (1 + h) ^ 2 / y + (-(3 / (4 * c)) * σ ^ 2 + 0 * |σ|) := by
    have h1 : F.CN * (1 + h + |σ|) ^ 2 / y ≤ 2 * F.CN * (1 + h) ^ 2 / y + 2 * F.CN * σ ^ 2 / y := by
      rw [← add_div, div_le_div_iff_of_pos_right hy]
      nlinarith [sq_nonneg (1 + h - |σ|)]
    have h2 : 2 * F.CN * σ ^ 2 / y ≤ σ ^ 2 / (4 * c) := by
      rw [div_le_div_iff₀ hy (by positivity)]
      nlinarith [sq_nonneg σ, mul_nonneg (sq_nonneg σ) (by linarith : (0:ℝ) ≤ y - 8 * c * F.CN)]
    have h4 : -σ ^ 2 / c + σ ^ 2 / (4 * c) = -(3 / (4 * c)) * σ ^ 2 := by field_simp; ring
    linarith
  calc Real.exp (-σ ^ 2 / c) * F.NbF y h σ
      = (F.CN * (1 + h + |σ|) ^ (F.P.natDegree + 2) / y) *
          Real.exp (-σ ^ 2 / c + F.CN * (1 + h + |σ|) ^ 2 / y) := by
        rw [NbF, Real.exp_add]; ring
    _ ≤ (F.CN * ((1 + h) ^ (F.P.natDegree + 2) * (1 + |σ|) ^ (F.P.natDegree + 2)) / y) *
          Real.exp (2 * F.CN * (1 + h) ^ 2 / y + (-(3 / (4 * c)) * σ ^ 2 + 0 * |σ|)) := by
        gcongr
    _ = _ := by rw [A₁F, Real.exp_add]; ring

/-- The far-field majorant in Gaussian-polynomial form. -/
lemma far_majorant {c : ℝ} (hc : 0 < c) {y : ℝ} (hy : 0 < y) {h : ℝ} (hh0 : 0 ≤ h) (σ : ℝ) :
    Real.exp (-σ ^ 2 / c) * (Real.exp (((h + |σ|) ^ 2 - y ^ 2 / 4) / (8 * c)) * (1 + F.GbF y h σ)) ≤
      F.A₂F c y h * ((1 + |σ|) ^ (F.P.natDegree + 2) *
        Real.exp (-(3 / (4 * c)) * σ ^ 2 + F.aFarF y h * |σ|)) := by
  have hσ := abs_nonneg σ
  have hCG := F.one_le_CG
  have hCG0 := F.CG_nonneg
  have hΛ := F.Lam_pos
  have hpi := Real.pi_pos
  have hexp1 : -σ ^ 2 / c + ((h + |σ|) ^ 2 - y ^ 2 / 4) / (8 * c) ≤
      -y ^ 2 / (32 * c) + h ^ 2 / (4 * c) + -(3 / (4 * c)) * σ ^ 2 := by
    have : (h + |σ|) ^ 2 ≤ 2 * h ^ 2 + 2 * σ ^ 2 := by nlinarith [sq_nonneg (h - |σ|), sq_abs σ]
    have e : -σ ^ 2 / c + ((h + |σ|) ^ 2 - y ^ 2 / 4) / (8 * c) -
        (-y ^ 2 / (32 * c) + h ^ 2 / (4 * c) + -(3 / (4 * c)) * σ ^ 2) =
        ((h + |σ|) ^ 2 - (2 * h ^ 2 + 2 * σ ^ 2)) / (8 * c) := by field_simp; ring
    have : ((h + |σ|) ^ 2 - (2 * h ^ 2 + 2 * σ ^ 2)) / (8 * c) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    linarith
  set X : ℝ := F.CG * (1 + h) * h / y + π * (∑ j, F.lam j) * y + F.CG with hXdef
  have hX : F.CG * (1 + h) * (h + |σ|) / y + π * (∑ j, F.lam j) * (y + |σ|) + F.CG = X + F.aFarF y h * |σ| := by
    rw [hXdef, aFarF]; field_simp; ring
  have hX0 : 0 ≤ X + F.aFarF y h * |σ| := by
    have := F.aFarF_nonneg hy hh0
    rw [hXdef]; positivity
  have hE1 : 1 ≤ Real.exp (X + F.aFarF y h * |σ|) := Real.one_le_exp_iff.mpr hX0
  have hpow := one_add_add_abs_pow_le hh0 σ (F.P.natDegree + 2)
  have hpow1 : 1 ≤ (1 + h) ^ (F.P.natDegree + 2) * (1 + |σ|) ^ (F.P.natDegree + 2) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) (one_le_pow₀ (by linarith))
  have hGb : 1 + F.GbF y h σ ≤ (1 + F.CG) * ((1 + h) ^ (F.P.natDegree + 2) * (1 + |σ|) ^ (F.P.natDegree + 2)) *
      Real.exp (X + F.aFarF y h * |σ|) := by
    rw [GbF, hX]
    set E := Real.exp (X + F.aFarF y h * |σ|)
    set B := (1 + h) ^ (F.P.natDegree + 2) * (1 + |σ|) ^ (F.P.natDegree + 2)
    have h0 : 0 ≤ (1 + h + |σ|) ^ (F.P.natDegree + 2) := by positivity
    have h1 : F.CG * (1 + h + |σ|) ^ (F.P.natDegree + 2) * E ≤ F.CG * B * E := by gcongr
    have h2 : 1 ≤ B * E := one_le_mul_of_one_le_of_one_le hpow1 hE1
    nlinarith
  have hL : Real.exp (-σ ^ 2 / c) * (Real.exp (((h + |σ|) ^ 2 - y ^ 2 / 4) / (8 * c)) * (1 + F.GbF y h σ)) =
      Real.exp (-σ ^ 2 / c + ((h + |σ|) ^ 2 - y ^ 2 / 4) / (8 * c)) * (1 + F.GbF y h σ) := by
    rw [Real.exp_add]; ring
  rw [hL]
  calc Real.exp (-σ ^ 2 / c + ((h + |σ|) ^ 2 - y ^ 2 / 4) / (8 * c)) * (1 + F.GbF y h σ)
      ≤ Real.exp (-y ^ 2 / (32 * c) + h ^ 2 / (4 * c) + -(3 / (4 * c)) * σ ^ 2) *
        ((1 + F.CG) * ((1 + h) ^ (F.P.natDegree + 2) * (1 + |σ|) ^ (F.P.natDegree + 2)) * Real.exp (X + F.aFarF y h * |σ|)) :=
        mul_le_mul (Real.exp_le_exp.mpr hexp1) hGb (by linarith [F.GbF_nonneg y hh0 σ])
          (Real.exp_pos _).le
    _ = _ := by
        rw [A₂F, hXdef]
        simp only [Real.exp_add]
        ring

/-! ### The integrated estimate -/

/-- **The integrated estimate**: for `2 ≤ Re b ≤ 4`, `y = Im s ≥ max Y₀ (8c·CN)`,
`‖E_n(s)‖ ≤ e^{M₀²/c}(πc)^{-1/2} (A₁F Igk(3/(4c), 0) + A₂F Igk(3/(4c), aFarF))`. -/
theorem norm_EF_le {c M₀ : ℝ} (hc : 0 < c) (n : ℕ+) {s : ℂ} (hb2 : 2 ≤ (s + M₀).re)
    (hb4 : (s + M₀).re ≤ 4) (hy0 : F.Y₀ ≤ s.im) (hyN : 8 * c * F.CN ≤ s.im) :
    ‖F.EF c M₀ n s‖ ≤ (Real.exp (M₀ ^ 2 / c) / Real.sqrt (π * c)) *
      (F.A₁F s.im (hh c n) * Igk (F.P.natDegree + 2) (3 / (4 * c)) 0 +
        F.A₂F c s.im (hh c n) * Igk (F.P.natDegree + 2) (3 / (4 * c)) (F.aFarF s.im (hh c n))) := by
  set y := s.im with hydef
  set h := hh c n with hhdef
  have hh0 : 0 ≤ h := hh_nonneg hc n
  have hy : 0 < y := by linarith [F.two_le_Y₀]
  have hbim : (s + M₀).im = y := by simp [hydef]
  set k := F.P.natDegree + 2 with hk
  -- pointwise bound on the integrand
  have hpt : ∀ σ : ℝ, ‖(F.KF c M₀ n s σ - 1) * gw c M₀ σ‖ ≤
      F.A₁F y h * ((1 + |σ|) ^ k * Real.exp (-(3 / (4 * c)) * σ ^ 2 + 0 * |σ|)) +
      F.A₂F c y h * ((1 + |σ|) ^ k * Real.exp (-(3 / (4 * c)) * σ ^ 2 + F.aFarF y h * |σ|)) := by
    intro σ
    rw [norm_mul, norm_gw]
    have hK := F.norm_KF_sub_one_le_unified hc (b := s + M₀) hb2 hb4 (by rw [hbim]; exact hy0) hh0 σ
    rw [hbim] at hK
    have : F.KF c M₀ n s σ = F.ρF (s + M₀) (((h : ℝ) : ℂ) + σ * I) *
        cexp (F.QF (s + M₀) (((h : ℝ) : ℂ) + σ * I)) := rfl
    rw [this]
    calc ‖F.ρF (s + M₀) (((h : ℝ) : ℂ) + σ * I) * cexp (F.QF (s + M₀) (((h : ℝ) : ℂ) + σ * I)) - 1‖ *
          Real.exp (-σ ^ 2 / c)
        ≤ (F.NbF y h σ + Real.exp (((h + |σ|) ^ 2 - y ^ 2 / 4) / (8 * c)) * (1 + F.GbF y h σ)) *
          Real.exp (-σ ^ 2 / c) := mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le
      _ = Real.exp (-σ ^ 2 / c) * F.NbF y h σ +
          Real.exp (-σ ^ 2 / c) *
            (Real.exp (((h + |σ|) ^ 2 - y ^ 2 / 4) / (8 * c)) * (1 + F.GbF y h σ)) := by
          ring
      _ ≤ _ := add_le_add (F.near_majorant hc hyN hh0 σ) (F.far_majorant hc hy hh0 σ)
  have hint1 := integrable_gauss_poly (b := 3 / (4 * c)) (by positivity) 0 k
  have hint2 := integrable_gauss_poly (b := 3 / (4 * c)) (by positivity) (F.aFarF y h) k
  have hmaj : Integrable fun σ : ℝ =>
      F.A₁F y h * ((1 + |σ|) ^ k * Real.exp (-(3 / (4 * c)) * σ ^ 2 + 0 * |σ|)) +
      F.A₂F c y h * ((1 + |σ|) ^ k * Real.exp (-(3 / (4 * c)) * σ ^ 2 + F.aFarF y h * |σ|)) :=
    (hint1.const_mul _).add (hint2.const_mul _)
  rw [EF, norm_mul, norm_mul, Complex.norm_exp, norm_div, norm_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr (by positivity))]
  simp only [Complex.ofReal_re]
  have hL : Real.exp (M₀ ^ 2 / c) * (1 / Real.sqrt (π * c)) *
      ‖∫ σ : ℝ, (F.KF c M₀ n s σ - 1) * gw c M₀ σ‖ =
      Real.exp (M₀ ^ 2 / c) / Real.sqrt (π * c) * ‖∫ σ : ℝ, (F.KF c M₀ n s σ - 1) * gw c M₀ σ‖ := by
    ring
  rw [hL]
  have hI := MeasureTheory.norm_integral_le_of_norm_le hmaj (ae_of_all _ hpt)
  rw [integral_add (hint1.const_mul _) (hint2.const_mul _), MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul] at hI
  have hA1 := F.A₁F_nonneg hy hh0
  have hA2 := F.A₂F_nonneg c y hh0
  have hK0 : 0 ≤ Real.exp (M₀ ^ 2 / c) / Real.sqrt (π * c) := by positivity
  have hI1 := integral_gauss_poly_le_Igk (b := 3 / (4 * c)) (by positivity) 0 k
  have hI2 := integral_gauss_poly_le_Igk (b := 3 / (4 * c)) (by positivity) (F.aFarF y h) k
  calc Real.exp (M₀ ^ 2 / c) / Real.sqrt (π * c) * ‖∫ σ : ℝ, (F.KF c M₀ n s σ - 1) * gw c M₀ σ‖
      ≤ Real.exp (M₀ ^ 2 / c) / Real.sqrt (π * c) *
        (F.A₁F y h * (∫ σ : ℝ, (1 + |σ|) ^ k * Real.exp (-(3 / (4 * c)) * σ ^ 2 + 0 * |σ|)) +
         F.A₂F c y h *
          (∫ σ : ℝ, (1 + |σ|) ^ k * Real.exp (-(3 / (4 * c)) * σ ^ 2 + F.aFarF y h * |σ|))) :=
        mul_le_mul_of_nonneg_left hI hK0
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hK0
        exact add_le_add (mul_le_mul_of_nonneg_left hI1 hA1) (mul_le_mul_of_nonneg_left hI2 hA2)

/-! ### Absorbing the coefficient `a_n = e^{-h²/c}` -/

/-- Near field: `a_n A₁F ≤ (CN e^{1/(2c)}/y) (1+h)^k e^{-h²/(2c)}` for `y ≥ 8c·CN`. -/
lemma coef_A₁F_le {c : ℝ} (hc : 0 < c) {y : ℝ} (hyN : 8 * c * F.CN ≤ y) {h : ℝ} (hh0 : 0 ≤ h) :
    Real.exp (-h ^ 2 / c) * F.A₁F y h ≤
      (F.CN * Real.exp (1 / (2 * c)) / y) *
        ((1 + h) ^ (F.P.natDegree + 2) * Real.exp (-(1 / (2 * c)) * h ^ 2)) := by
  have hCN := F.one_le_CN
  have hCN0 := F.CN_nonneg
  have hy : 0 < y := by nlinarith
  have h1 : 2 * F.CN * (1 + h) ^ 2 / y ≤ (1 + h ^ 2) / (2 * c) := by
    rw [div_le_div_iff₀ hy (by positivity)]
    have h2 : (1 + h) ^ 2 ≤ 2 * (1 + h ^ 2) := by nlinarith [sq_nonneg (h - 1)]
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ (1 + h) ^ 2) (by linarith : (0:ℝ) ≤ y - 8 * c * F.CN),
      mul_nonneg (by positivity : (0:ℝ) ≤ F.CN * c) (by linarith : (0:ℝ) ≤ 2 * (1 + h ^ 2) - (1 + h) ^ 2)]
  have hexp : Real.exp (-h ^ 2 / c) * Real.exp (2 * F.CN * (1 + h) ^ 2 / y) ≤
      Real.exp (1 / (2 * c)) * Real.exp (-(1 / (2 * c)) * h ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : -h ^ 2 / c + (1 + h ^ 2) / (2 * c) = 1 / (2 * c) + -(1 / (2 * c)) * h ^ 2 := by
      field_simp; ring
    linarith
  calc Real.exp (-h ^ 2 / c) * F.A₁F y h
      = (F.CN * (1 + h) ^ (F.P.natDegree + 2) / y) *
          (Real.exp (-h ^ 2 / c) * Real.exp (2 * F.CN * (1 + h) ^ 2 / y)) := by
        rw [A₁F]; ring
    _ ≤ (F.CN * (1 + h) ^ (F.P.natDegree + 2) / y) *
          (Real.exp (1 / (2 * c)) * Real.exp (-(1 / (2 * c)) * h ^ 2)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by ring

/-- The far-field constant `D₂F(c)`. -/
noncomputable def D₂F (c : ℝ) : ℝ :=
  (1 + F.CG) * Real.exp (F.CG + 1 / (32 * c) +
    (4 * c / 3) * (π * (∑ j, F.lam j) + ((F.P.natDegree + 2 : ℕ) : ℝ)) ^ 2 + 1 / (24 * c)) *
    Real.sqrt (π / ((3 / (4 * c)) / 2))

lemma D₂F_nonneg (c : ℝ) : 0 ≤ F.D₂F c := by
  unfold D₂F; have := F.CG_nonneg; positivity

/-- Far field: `a_n A₂F Igk(3/(4c), aFarF) ≤ D₂F (1+h)^k e^{-11h²/(24c)} e^{-y²/(32c) + πΛy}` for
`y ≥ 8c·CG`. -/
lemma coef_A₂F_le {c : ℝ} (hc : 0 < c) {y : ℝ} (hyG : 8 * c * F.CG ≤ y) {h : ℝ} (hh0 : 0 ≤ h) :
    Real.exp (-h ^ 2 / c) * (F.A₂F c y h * Igk (F.P.natDegree + 2) (3 / (4 * c)) (F.aFarF y h)) ≤
      F.D₂F c * ((1 + h) ^ (F.P.natDegree + 2) * Real.exp (-(11 / (24 * c)) * h ^ 2)) *
        Real.exp (-y ^ 2 / (32 * c) + π * (∑ j, F.lam j) * y) := by
  have hCG := F.one_le_CG
  have hCG0 := F.CG_nonneg
  have hΛ := F.Lam_pos
  have hpi := Real.pi_pos
  have hy : 0 < y := by nlinarith
  set kR : ℝ := ((F.P.natDegree + 2 : ℕ) : ℝ) with hkR
  have hkR0 : 0 ≤ kR := by rw [hkR]; positivity
  set Λ : ℝ := ∑ j, F.lam j with hΛdef
  -- `CG (1+h) h / y ≤ (1+h) h / (8c)` and `CG (1+h) / y ≤ (1+h)/(8c)`
  have hdiv1 : F.CG * (1 + h) * h / y ≤ (1 + h) * h / (8 * c) := by
    rw [div_le_div_iff₀ hy (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 1 + h) hh0)
      (by linarith : (0:ℝ) ≤ y - 8 * c * F.CG)]
  have hdiv2 : F.CG * (1 + h) / y ≤ (1 + h) / (8 * c) := by
    rw [div_le_div_iff₀ hy (by positivity)]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 + h) (by linarith : (0:ℝ) ≤ y - 8 * c * F.CG)]
  have hE1 : F.CG * (1 + h) * h / y ≤ h ^ 2 / (4 * c) + 1 / (32 * c) := by
    refine hdiv1.trans ?_
    rw [show h ^ 2 / (4 * c) + 1 / (32 * c) = (8 * h ^ 2 + 1) / (32 * c) by field_simp; ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (2 * h - 1), hc]
  have ha : F.aFarF y h ≤ (1 + h) / (8 * c) + π * Λ := by
    unfold aFarF; linarith
  have ha0 : 0 ≤ F.aFarF y h := F.aFarF_nonneg hy hh0
  have hE2 : (F.aFarF y h + kR) ^ 2 / (2 * (3 / (4 * c))) ≤
      (4 * c / 3) * (π * Λ + kR) ^ 2 + (h ^ 2 / (24 * c) + 1 / (24 * c)) := by
    have hsq : (F.aFarF y h + kR) ^ 2 ≤ 2 * (π * Λ + kR) ^ 2 + 2 * ((1 + h) / (8 * c)) ^ 2 := by
      have h0 : F.aFarF y h + kR ≤ (π * Λ + kR) + (1 + h) / (8 * c) := by linarith
      have h00 : 0 ≤ F.aFarF y h + kR := by linarith
      calc (F.aFarF y h + kR) ^ 2 ≤ ((π * Λ + kR) + (1 + h) / (8 * c)) ^ 2 := by gcongr
        _ ≤ _ := by nlinarith [sq_nonneg ((π * Λ + kR) - (1 + h) / (8 * c))]
    have h1h : (1 + h) ^ 2 ≤ 2 * h ^ 2 + 2 := by nlinarith [sq_nonneg (h - 1)]
    have hdiv : (F.aFarF y h + kR) ^ 2 / (2 * (3 / (4 * c))) = (2 * c / 3) * (F.aFarF y h + kR) ^ 2 := by
      field_simp; ring
    rw [hdiv]
    calc (2 * c / 3) * (F.aFarF y h + kR) ^ 2
        ≤ (2 * c / 3) * (2 * (π * Λ + kR) ^ 2 + 2 * ((1 + h) / (8 * c)) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (4 * c / 3) * (π * Λ + kR) ^ 2 + (1 + h) ^ 2 / (48 * c) := by field_simp; ring
      _ ≤ (4 * c / 3) * (π * Λ + kR) ^ 2 + (2 * h ^ 2 + 2) / (48 * c) := by gcongr
      _ = _ := by field_simp; ring
  -- assemble
  have hLHS : Real.exp (-h ^ 2 / c) * (F.A₂F c y h * Igk (F.P.natDegree + 2) (3 / (4 * c)) (F.aFarF y h)) =
      ((1 + F.CG) * (1 + h) ^ (F.P.natDegree + 2) * Real.sqrt (π / ((3 / (4 * c)) / 2))) *
        Real.exp (-h ^ 2 / c + -y ^ 2 / (32 * c) + h ^ 2 / (4 * c) +
          (F.CG * (1 + h) * h / y + π * Λ * y + F.CG) +
          (F.aFarF y h + kR) ^ 2 / (2 * (3 / (4 * c)))) := by
    rw [A₂F, Igk, hkR, hΛdef]
    simp only [Real.exp_add]
    ring
  have hRHS : F.D₂F c * ((1 + h) ^ (F.P.natDegree + 2) * Real.exp (-(11 / (24 * c)) * h ^ 2)) *
      Real.exp (-y ^ 2 / (32 * c) + π * Λ * y) =
      ((1 + F.CG) * (1 + h) ^ (F.P.natDegree + 2) * Real.sqrt (π / ((3 / (4 * c)) / 2))) *
        Real.exp ((F.CG + 1 / (32 * c) + (4 * c / 3) * (π * Λ + kR) ^ 2 + 1 / (24 * c)) +
          -(11 / (24 * c)) * h ^ 2 + (-y ^ 2 / (32 * c) + π * Λ * y)) := by
    rw [D₂F, hkR, hΛdef]
    simp only [Real.exp_add]
    ring
  rw [hLHS, hRHS]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have hid : -h ^ 2 / c + h ^ 2 / (4 * c) + h ^ 2 / (4 * c) + h ^ 2 / (24 * c) =
      -(11 / (24 * c)) * h ^ 2 := by field_simp; ring
  linarith

/-! ### Summability of the weights -/

/-- `(1+h)^k e^{-κh²} n^β ≤ e^{(k + 2(β+2)/c)²/(4κ)} n^{-2}`, `h = (c/2) log n`: the weight is
`n^{-2}` times a bounded function of `n`. -/
lemma weight_le_rpow_neg_two {c : ℝ} (hc : 0 < c) {κ : ℝ} (hκ : 0 < κ) (k : ℕ) (β : ℝ) (n : ℕ+) :
    (1 + hh c n) ^ k * Real.exp (-κ * (hh c n) ^ 2) * (n : ℝ) ^ β ≤
      Real.exp ((k + 2 * (β + 2) / c) ^ 2 / (4 * κ)) * (n : ℝ) ^ (-(2 : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hh0 := hh_nonneg hc n
  have hlog : Real.log n = 2 * hh c n / c := by unfold hh; field_simp
  have hpow : (1 + hh c n) ^ k ≤ Real.exp (k * hh c n) := by
    calc (1 + hh c n) ^ k ≤ (Real.exp (hh c n)) ^ k := by
          gcongr; linarith [Real.add_one_le_exp (hh c n)]
      _ = Real.exp (k * hh c n) := by rw [← Real.exp_nat_mul]
  have hsplit : (n : ℝ) ^ β = Real.exp (Real.log n * (β + 2)) * (n : ℝ) ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_def_of_pos hnpos, ← Real.rpow_add hnpos]; ring_nf
  have hkey : k * hh c n + -κ * (hh c n) ^ 2 + 2 * hh c n / c * (β + 2) ≤
      (k + 2 * (β + 2) / c) ^ 2 / (4 * κ) := by
    have h2 : 2 * hh c n / c * (β + 2) = (k + 2 * (β + 2) / c - k) * hh c n := by
      field_simp; ring
    rw [h2, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * κ * hh c n - (k + 2 * (β + 2) / c))]
  calc (1 + hh c n) ^ k * Real.exp (-κ * (hh c n) ^ 2) * (n : ℝ) ^ β
      = ((1 + hh c n) ^ k * Real.exp (-κ * (hh c n) ^ 2) * Real.exp (Real.log n * (β + 2))) *
          (n : ℝ) ^ (-(2 : ℝ)) := by
        rw [hsplit]; ring
    _ ≤ (Real.exp (k * hh c n) * Real.exp (-κ * (hh c n) ^ 2) * Real.exp (Real.log n * (β + 2))) *
          (n : ℝ) ^ (-(2 : ℝ)) := by
        gcongr
    _ = Real.exp (k * hh c n + -κ * (hh c n) ^ 2 + 2 * hh c n / c * (β + 2)) * (n : ℝ) ^ (-(2 : ℝ)) := by
        rw [← Real.exp_add, ← Real.exp_add, hlog]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hkey) (by positivity)

/-- `‖a(n)‖ (1+h)^k e^{-κ h²} n^β` is summable over `n ≥ 1` for every `κ > 0`, from
`∑ ‖a(n)‖ n^{-2} < ∞`. -/
lemma summable_weight_a {c : ℝ} (hc : 0 < c) {κ : ℝ} (hκ : 0 < κ) (k : ℕ) (β : ℝ) :
    Summable fun n : ℕ+ =>
      ‖F.a n‖ * ((1 + hh c n) ^ k * Real.exp (-κ * (hh c n) ^ 2) * (n : ℝ) ^ β) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((F.summable_norm_a_mul_rpow (a := 2) one_lt_two).mul_left
      (Real.exp ((k + 2 * (β + 2) / c) ^ 2 / (4 * κ))))
  · have := hh_nonneg hc n; positivity
  · have h := weight_le_rpow_neg_two hc hκ k β n
    calc ‖F.a n‖ * ((1 + hh c n) ^ k * Real.exp (-κ * (hh c n) ^ 2) * (n : ℝ) ^ β)
        ≤ ‖F.a n‖ * (Real.exp ((k + 2 * (β + 2) / c) ^ 2 / (4 * κ)) * (n : ℝ) ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ = _ := by ring

/-! ### The uniform estimate on the strip -/

/-- The near- and far-field weights (summable in `n`), with the strip centre `x₀` built in through
the factor `n^{1-x₀} ≥ n^{-x}` for `|x - x₀| ≤ 1`. -/
noncomputable def T₁F (c x₀ : ℝ) (n : ℕ+) : ℝ :=
  ‖F.a n‖ * ((1 + hh c n) ^ (F.P.natDegree + 2) * Real.exp (-(1 / (2 * c)) * (hh c n) ^ 2) *
    (n : ℝ) ^ (1 - x₀))

noncomputable def T₂F (c x₀ : ℝ) (n : ℕ+) : ℝ :=
  ‖F.a n‖ * ((1 + hh c n) ^ (F.P.natDegree + 2) * Real.exp (-(11 / (24 * c)) * (hh c n) ^ 2) *
    (n : ℝ) ^ (1 - x₀))

lemma summable_T₁F {c : ℝ} (hc : 0 < c) (x₀ : ℝ) : Summable (F.T₁F c x₀) :=
  F.summable_weight_a hc (κ := 1 / (2 * c)) (by positivity) (F.P.natDegree + 2) (1 - x₀)

lemma summable_T₂F {c : ℝ} (hc : 0 < c) (x₀ : ℝ) : Summable (F.T₂F c x₀) :=
  F.summable_weight_a hc (κ := 11 / (24 * c)) (by positivity) (F.P.natDegree + 2) (1 - x₀)

/-- The constant in front of the near-field weight. -/
noncomputable def C₁F (c x₀ : ℝ) : ℝ :=
  (Real.exp ((3 - x₀) ^ 2 / c) / Real.sqrt (π * c)) *
    (F.CN * Real.exp (1 / (2 * c)) * Igk (F.P.natDegree + 2) (3 / (4 * c)) 0)

/-- The constant in front of the far-field weight. -/
noncomputable def C₂F (c x₀ : ℝ) : ℝ := (Real.exp ((3 - x₀) ^ 2 / c) / Real.sqrt (π * c)) * F.D₂F c

/-- **Per-term bound on the strip**: for `|Re s − x₀| ≤ 1` and `Im s ≥ max Y₀ (8c·CN) (8c·CG)`,
`‖a(n) a_n n^{-s} E_n(s)‖ ≤ C₁F T₁F(n)/y + C₂F T₂F(n) e^{-y²/(32c) + πΛy}` with `M₀ = 3 − x₀`. -/
theorem norm_term_le_weights {c : ℝ} (hc : 0 < c) (x₀ : ℝ) (n : ℕ+) {s : ℂ}
    (hx : |s.re - x₀| ≤ 1) (hy0 : F.Y₀ ≤ s.im) (hyN : 8 * c * F.CN ≤ s.im)
    (hyG : 8 * c * F.CG ≤ s.im) :
    ‖F.a n * (coef c n : ℂ) * (1 / (n : ℂ) ^ s) * F.EF c (3 - x₀) n s‖ ≤
      F.C₁F c x₀ * F.T₁F c x₀ n / s.im +
        F.C₂F c x₀ * F.T₂F c x₀ n *
          Real.exp (-s.im ^ 2 / (32 * c) + π * (∑ j, F.lam j) * s.im) := by
  have hxx := abs_le.mp hx
  have hb2 : 2 ≤ (s + ((3 - x₀ : ℝ) : ℂ)).re := by simp; linarith
  have hb4 : (s + ((3 - x₀ : ℝ) : ℂ)).re ≤ 4 := by simp; linarith
  have hy : 0 < s.im := by linarith [F.two_le_Y₀]
  have hh0 := hh_nonneg hc n
  have hE := F.norm_EF_le hc n hb2 hb4 hy0 hyN
  have hcoef : ‖(coef c n : ℂ)‖ = Real.exp (-(hh c n) ^ 2 / c) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (coef_pos c n)]; rfl
  have hn : ‖(1 / (n : ℂ) ^ s)‖ ≤ (n : ℝ) ^ (1 - x₀) := by
    rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos n.pos, one_div,
      ← Real.rpow_neg (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast n.pos) (by linarith)
  have hn0 : 0 ≤ (n : ℝ) ^ (1 - x₀) := by positivity
  have hA1 := F.coef_A₁F_le hc hyN hh0
  have hA2 := F.coef_A₂F_le hc hyG hh0
  have hIg1 := Igk_nonneg (F.P.natDegree + 2) (3 / (4 * c)) 0
  have hIg2 := Igk_nonneg (F.P.natDegree + 2) (3 / (4 * c)) (F.aFarF s.im (hh c n))
  have hA1' := F.A₁F_nonneg hy hh0
  have hA2' := F.A₂F_nonneg c s.im hh0
  have hK₀0 : 0 ≤ Real.exp ((3 - x₀) ^ 2 / c) / Real.sqrt (π * c) := by positivity
  have ha0 := norm_nonneg (F.a n)
  rw [norm_mul, norm_mul, norm_mul, hcoef]
  calc ‖F.a n‖ * Real.exp (-(hh c n) ^ 2 / c) * ‖(1 / (n : ℂ) ^ s)‖ * ‖F.EF c (3 - x₀) n s‖
      ≤ ‖F.a n‖ * Real.exp (-(hh c n) ^ 2 / c) * (n : ℝ) ^ (1 - x₀) *
        ((Real.exp ((3 - x₀) ^ 2 / c) / Real.sqrt (π * c)) *
          (F.A₁F s.im (hh c n) * Igk (F.P.natDegree + 2) (3 / (4 * c)) 0 +
            F.A₂F c s.im (hh c n) *
              Igk (F.P.natDegree + 2) (3 / (4 * c)) (F.aFarF s.im (hh c n)))) := by
        gcongr
    _ = (Real.exp ((3 - x₀) ^ 2 / c) / Real.sqrt (π * c)) * ‖F.a n‖ * (n : ℝ) ^ (1 - x₀) *
          (Real.exp (-(hh c n) ^ 2 / c) * F.A₁F s.im (hh c n)) *
          Igk (F.P.natDegree + 2) (3 / (4 * c)) 0 +
        (Real.exp ((3 - x₀) ^ 2 / c) / Real.sqrt (π * c)) * ‖F.a n‖ * (n : ℝ) ^ (1 - x₀) *
          (Real.exp (-(hh c n) ^ 2 / c) * (F.A₂F c s.im (hh c n) *
            Igk (F.P.natDegree + 2) (3 / (4 * c)) (F.aFarF s.im (hh c n)))) := by
        ring
    _ ≤ (Real.exp ((3 - x₀) ^ 2 / c) / Real.sqrt (π * c)) * ‖F.a n‖ * (n : ℝ) ^ (1 - x₀) *
          ((F.CN * Real.exp (1 / (2 * c)) / s.im) *
            ((1 + hh c n) ^ (F.P.natDegree + 2) * Real.exp (-(1 / (2 * c)) * (hh c n) ^ 2))) *
          Igk (F.P.natDegree + 2) (3 / (4 * c)) 0 +
        (Real.exp ((3 - x₀) ^ 2 / c) / Real.sqrt (π * c)) * ‖F.a n‖ * (n : ℝ) ^ (1 - x₀) *
          (F.D₂F c * ((1 + hh c n) ^ (F.P.natDegree + 2) *
              Real.exp (-(11 / (24 * c)) * (hh c n) ^ 2)) *
            Real.exp (-s.im ^ 2 / (32 * c) + π * (∑ j, F.lam j) * s.im)) := by
        gcongr
    _ = _ := by
        rw [C₁F, C₂F, T₁F, T₂F]
        ring

/-- **The error series is small, uniformly on the strip.**  With `M₀ = 3 − x₀`: for every `c > 0`,
`x₀` and `ε > 0` there is `Y` such that for all `s` with `|Re s − x₀| ≤ 1` and `Im s ≥ Y` the error
series converges and `‖∑_n a(n) a_n n^{-s} E_n(s)‖ ≤ ε`.  The statement is the body of
`ErrorSumSmall F` (DBNSelbergNewman). -/
theorem error_sum_small :
    ∀ c : ℝ, 0 < c → ∀ x₀ : ℝ, ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ s : ℂ, |s.re - x₀| ≤ 1 → Y ≤ s.im →
      (Summable fun n : ℕ+ => F.a n * (DBNSaddle.coef c n : ℂ) * (1 / (n : ℂ) ^ s) *
        F.EF c (3 - x₀) n s) ∧
      ‖∑' n : ℕ+, F.a n * (DBNSaddle.coef c n : ℂ) * (1 / (n : ℂ) ^ s) *
        F.EF c (3 - x₀) n s‖ ≤ ε := by
  intro c hc x₀ ε hε
  have hΛ := F.Lam_pos
  have hpi := Real.pi_pos
  set Λ : ℝ := ∑ j, F.lam j with hΛdef
  set S₁ : ℝ := F.C₁F c x₀ * ∑' n : ℕ+, F.T₁F c x₀ n with hS₁
  set S₂ : ℝ := F.C₂F c x₀ * ∑' n : ℕ+, F.T₂F c x₀ n with hS₂
  -- the bound function tends to zero
  have hlim : Tendsto (fun y : ℝ => S₁ / y + S₂ * Real.exp (-y ^ 2 / (32 * c) + π * Λ * y)) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => S₁ / y) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have h2 : Tendsto (fun y : ℝ => Real.exp (-y ^ 2 / (32 * c) + π * Λ * y)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ Real.tendsto_exp_neg_atTop_nhds_zero
      filter_upwards [eventually_ge_atTop (32 * c * (π * Λ + 1))] with y hy
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have hy0 : 0 ≤ y := le_trans (by positivity) hy
      rw [div_add' _ _ _ (by positivity : (32 * c : ℝ) ≠ 0), div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hy0 (by linarith : (0:ℝ) ≤ y - 32 * c * (π * Λ + 1))]
    simpa using h1.add (h2.const_mul S₂)
  have hev : ∀ᶠ y : ℝ in atTop, S₁ / y + S₂ * Real.exp (-y ^ 2 / (32 * c) + π * Λ * y) < ε :=
    hlim.eventually (gt_mem_nhds hε)
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.mp hev
  refine ⟨max Y₁ (max F.Y₀ (max (8 * c * F.CN) (8 * c * F.CG))), fun s hx hY => ?_⟩
  have hy0 : F.Y₀ ≤ s.im := le_trans (le_max_of_le_right (le_max_left _ _)) hY
  have hyN : 8 * c * F.CN ≤ s.im :=
    le_trans (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))) hY
  have hyG : 8 * c * F.CG ≤ s.im :=
    le_trans (le_max_of_le_right (le_max_of_le_right (le_max_right _ _))) hY
  have hy : 0 < s.im := by linarith [F.two_le_Y₀]
  have hpt := fun n => F.norm_term_le_weights hc x₀ n hx hy0 hyN hyG
  have hbound : Summable fun n : ℕ+ => F.C₁F c x₀ * F.T₁F c x₀ n / s.im +
      F.C₂F c x₀ * F.T₂F c x₀ n * Real.exp (-s.im ^ 2 / (32 * c) + π * Λ * s.im) :=
    (((F.summable_T₁F hc x₀).mul_left _).div_const _).add
      (((F.summable_T₂F hc x₀).mul_left _).mul_right _)
  have hsum : Summable fun n : ℕ+ =>
      F.a n * (coef c n : ℂ) * (1 / (n : ℂ) ^ s) * F.EF c (3 - x₀) n s :=
    Summable.of_norm_bounded hbound hpt
  refine ⟨hsum, ?_⟩
  calc ‖∑' n : ℕ+, F.a n * (coef c n : ℂ) * (1 / (n : ℂ) ^ s) * F.EF c (3 - x₀) n s‖
      ≤ ∑' n : ℕ+, ‖F.a n * (coef c n : ℂ) * (1 / (n : ℂ) ^ s) * F.EF c (3 - x₀) n s‖ :=
        norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ+, (F.C₁F c x₀ * F.T₁F c x₀ n / s.im +
          F.C₂F c x₀ * F.T₂F c x₀ n * Real.exp (-s.im ^ 2 / (32 * c) + π * Λ * s.im)) :=
        hsum.norm.tsum_le_tsum hpt hbound
    _ = S₁ / s.im + S₂ * Real.exp (-s.im ^ 2 / (32 * c) + π * Λ * s.im) := by
        rw [(((F.summable_T₁F hc x₀).mul_left _).div_const _).tsum_add
          (((F.summable_T₂F hc x₀).mul_left _).mul_right _), tsum_div_const, tsum_mul_right,
          tsum_mul_left, tsum_mul_left, hS₁, hS₂]
    _ ≤ ε := (hY₁ s.im (le_trans (le_max_left _ _) hY)).le

end ExtSelbergData

end DBNSelberg
