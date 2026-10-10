/-
  DBNSaddleSum -- integrating the saddle-point estimates and summing over `n`.

  Step 5c of the Lambda >= 0 (Newman's conjecture) formalization; see
  NEWMAN_LAMBDA_NONNEG_SCOPING_2026-10-10.md section 6.  Fix `c > 0`, a strip centre `x₀`, and the
  base shift `M₀ = 3 − x₀` (so `2 ≤ Re b ≤ 4` on the strip `|Re s − x₀| ≤ 1`, `b = s + M₀`).

  * A single pointwise bound valid for every `n` and every `σ` (no case split on `n`):
        ‖K_n(σ) − 1‖ ≤ N(y,h,σ) + e^{((h+|σ|)² − y²/4)/(8c)} (1 + G(y,h,σ)),
    the near-field bound where `h + |σ| ≤ y/2` and the global bound elsewhere, the Gaussian factor
    `e^{((h+|σ|)²−y²/4)/(8c)} ≥ 1` playing the role of the indicator of the far region.
  * Integrated against `e^{-σ²/c}` this gives
        a_n n^{-x} ‖E_n(s)‖ ≤ C₁ e^{-h²/(2c)} (h²+h+1) n^{-x} / y + C₂ e^{-(11/24) h²/c} (2+h)² n^{-x} e^{-y²/(32c) + πy}
    for `y ≥ y₀`, both coefficients summable in `n` uniformly on the strip, hence
        ∑_n a_n n^{-x} ‖E_n(s)‖ → 0   as `y → ∞`, uniformly for `|x − x₀| ≤ 1`.

  Nothing here is RH.  conjecture1_proved = False.
-/
import Mathlib
import DBNSaddleBounds

open Complex Filter Topology MeasureTheory Set
open scoped Real

namespace DBNSaddle

open DBNGaussConv DBNStirling

/-! ### Gaussian-polynomial-exponential integrals -/

/-- `(1+|σ|)^k e^{a|σ|} ≤ e^{(a+k)|σ|}` (`1 + t ≤ e^t`). -/
lemma one_add_abs_pow_mul_exp_le (k : ℕ) (a σ : ℝ) :
    (1 + |σ|) ^ k * Real.exp (a * |σ|) ≤ Real.exp ((a + k) * |σ|) := by
  have h1 : (1 + |σ|) ^ k ≤ Real.exp (k * |σ|) := by
    calc (1 + |σ|) ^ k ≤ (Real.exp |σ|) ^ k := by
          gcongr
          have := Real.add_one_le_exp |σ|; linarith
      _ = Real.exp (k * |σ|) := by rw [← Real.exp_nat_mul]
  calc (1 + |σ|) ^ k * Real.exp (a * |σ|) ≤ Real.exp (k * |σ|) * Real.exp (a * |σ|) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp ((a + k) * |σ|) := by rw [← Real.exp_add]; ring_nf

/-- Completing the square: `−bσ² + a|σ| ≤ −(b/2)σ² + a²/(2b)` for `b > 0`. -/
lemma neg_mul_sq_add_le {b : ℝ} (hb : 0 < b) (a σ : ℝ) :
    -b * σ ^ 2 + a * |σ| ≤ -(b / 2) * σ ^ 2 + a ^ 2 / (2 * b) := by
  have h : 0 ≤ (b / 2) * (|σ| - a / b) ^ 2 := by positivity
  have hs : |σ| ^ 2 = σ ^ 2 := sq_abs σ
  have : (b / 2) * (|σ| - a / b) ^ 2 = (b / 2) * σ ^ 2 - a * |σ| + a ^ 2 / (2 * b) := by
    field_simp
    ring_nf
    rw [hs]
  linarith

/-- The master majorant `e^{-(b/2)σ²}` bounds `(1+|σ|)^k e^{-bσ² + a|σ|}` up to the constant
`e^{(a+k)²/(2b)}`. -/
lemma gauss_poly_le {b : ℝ} (hb : 0 < b) (a : ℝ) (k : ℕ) (σ : ℝ) :
    (1 + |σ|) ^ k * Real.exp (-b * σ ^ 2 + a * |σ|) ≤
      Real.exp ((a + k) ^ 2 / (2 * b)) * Real.exp (-(b / 2) * σ ^ 2) := by
  calc (1 + |σ|) ^ k * Real.exp (-b * σ ^ 2 + a * |σ|)
      = (1 + |σ|) ^ k * Real.exp (a * |σ|) * Real.exp (-b * σ ^ 2) := by
        rw [Real.exp_add]; ring
    _ ≤ Real.exp ((a + k) * |σ|) * Real.exp (-b * σ ^ 2) :=
        mul_le_mul_of_nonneg_right (one_add_abs_pow_mul_exp_le k a σ) (Real.exp_pos _).le
    _ = Real.exp (-b * σ ^ 2 + (a + k) * |σ|) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-(b / 2) * σ ^ 2 + (a + k) ^ 2 / (2 * b)) :=
        Real.exp_le_exp.mpr (neg_mul_sq_add_le hb _ _)
    _ = _ := by rw [← Real.exp_add]; ring_nf

lemma integrable_gauss_poly {b : ℝ} (hb : 0 < b) (a : ℝ) (k : ℕ) :
    Integrable fun σ : ℝ => (1 + |σ|) ^ k * Real.exp (-b * σ ^ 2 + a * |σ|) := by
  refine ((integrable_exp_neg_mul_sq (b := b / 2) (by positivity)).const_mul
    (Real.exp ((a + k) ^ 2 / (2 * b)))).mono' (by fun_prop : Continuous fun σ : ℝ =>
      (1 + |σ|) ^ k * Real.exp (-b * σ ^ 2 + a * |σ|)).aestronglyMeasurable (ae_of_all _ fun σ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact gauss_poly_le hb a k σ

lemma integral_gauss_poly_le {b : ℝ} (hb : 0 < b) (a : ℝ) (k : ℕ) :
    ∫ σ : ℝ, (1 + |σ|) ^ k * Real.exp (-b * σ ^ 2 + a * |σ|) ≤
      Real.exp ((a + k) ^ 2 / (2 * b)) * Real.sqrt (π / (b / 2)) := by
  rw [← integral_gaussian (b / 2), ← MeasureTheory.integral_const_mul]
  refine integral_mono (integrable_gauss_poly hb a k)
    ((integrable_exp_neg_mul_sq (by positivity)).const_mul _) fun σ => gauss_poly_le hb a k σ

/-! ### The unified pointwise bound -/

/-- `Pt h σ = (h+|σ|)² + (h+|σ|) + 1 ≥ P(δ)` for `δ = h + iσ`. -/
noncomputable def Pt (h σ : ℝ) : ℝ := (h + |σ|) ^ 2 + (h + |σ|) + 1

/-- The near-field majorant `Nb y h σ = 8 Pt/y · e^{2 Pt/y}`. -/
noncomputable def Nb (y h σ : ℝ) : ℝ := 8 * Pt h σ / y * Real.exp (2 * Pt h σ / y)

/-- The far-field majorant `Gb y h σ = 2 (2+h+|σ|)² e^{(3+h)(h+|σ|)/(2y) + π(y+|σ|) + 1}`. -/
noncomputable def Gb (y h σ : ℝ) : ℝ :=
  2 * (2 + h + |σ|) ^ 2 * Real.exp ((3 + h) * (h + |σ|) / (2 * y) + π * (y + |σ|) + 1)

lemma Pt_nonneg (h σ : ℝ) : 0 ≤ Pt h σ := by unfold Pt; nlinarith [sq_nonneg (h + |σ| + 1 / 2)]

lemma Nb_nonneg {y : ℝ} (hy : 0 < y) (h σ : ℝ) : 0 ≤ Nb y h σ := by
  unfold Nb
  have := Pt_nonneg h σ
  exact mul_nonneg (div_nonneg (by linarith) hy.le) (Real.exp_pos _).le

lemma Gb_nonneg (y h σ : ℝ) : 0 ≤ Gb y h σ := by unfold Gb; positivity

lemma norm_hδ_le {h : ℝ} (hh0 : 0 ≤ h) (σ : ℝ) : ‖((h : ℝ) : ℂ) + σ * I‖ ≤ h + |σ| := by
  calc ‖((h : ℝ) : ℂ) + σ * I‖ ≤ ‖((h : ℝ) : ℂ)‖ + ‖(σ : ℂ) * I‖ := norm_add_le _ _
    _ = h + |σ| := by simp [abs_of_nonneg hh0]

lemma P_le_Pt {h : ℝ} (hh0 : 0 ≤ h) (σ : ℝ) : P (((h : ℝ) : ℂ) + σ * I) ≤ Pt h σ := by
  have h1 := norm_hδ_le hh0 σ
  have h0 := norm_nonneg (((h : ℝ) : ℂ) + σ * I)
  unfold P Pt
  nlinarith

/-- **Unified pointwise bound**: for `2 ≤ Re b ≤ 4`, `y = Im b ≥ 2`, `δ = h + iσ` with `h ≥ 0`,
    `‖ρ e^Q − 1‖ ≤ Nb y h σ + e^{((h+|σ|)² − y²/4)/(8c)} (1 + Gb y h σ)`. -/
theorem norm_K_sub_one_le_unified {c : ℝ} (hc : 0 < c) {b : ℂ} (hb2 : 2 ≤ b.re) (hb4 : b.re ≤ 4)
    (hy : 2 ≤ b.im) {h : ℝ} (hh0 : 0 ≤ h) (σ : ℝ) :
    ‖ρ b (((h : ℝ) : ℂ) + σ * I) * cexp (Q b (((h : ℝ) : ℂ) + σ * I)) - 1‖ ≤
      Nb b.im h σ + Real.exp (((h + |σ|) ^ 2 - b.im ^ 2 / 4) / (8 * c)) * (1 + Gb b.im h σ) := by
  set δ : ℂ := ((h : ℝ) : ℂ) + σ * I with hδdef
  have hypos : 0 < b.im := by linarith
  have hbn_y : b.im ≤ ‖b‖ := le_trans (le_abs_self _) (Complex.abs_im_le_norm b)
  have hbn : 2 ≤ ‖b‖ := le_trans hy hbn_y
  have hbpos : 0 < ‖b‖ := by linarith
  have hδn : ‖δ‖ ≤ h + |σ| := norm_hδ_le hh0 σ
  have hδre : 0 ≤ δ.re := by simp [hδdef, hh0]
  have hδre' : δ.re = h := by simp [hδdef]
  have hδim : δ.im = σ := by simp [hδdef]
  have hb1 : b - 1 ≠ 0 := fun h0 => by
    have := congrArg Complex.im h0
    simp at this
    linarith
  have hNb := Nb_nonneg hypos h σ
  have hGb := Gb_nonneg b.im h σ
  by_cases hreg : h + |σ| ≤ b.im / 2
  · -- near field
    have hbδim : 0 < (b + δ).im := by
      rw [Complex.add_im, hδim]
      have := abs_le.mp (le_refl |σ|)
      linarith
    have hδb : ‖δ‖ ≤ ‖b‖ / 2 := by linarith
    have hnear := norm_K_sub_one_le (by linarith) hbn hypos hδre hbδim hδb
    have hPP : P δ ≤ Pt h σ := P_le_Pt hh0 σ
    have hP0 := P_pos δ
    have hmono : 8 * P δ / ‖b‖ * Real.exp (2 * P δ / ‖b‖) ≤ Nb b.im h σ := by
      unfold Nb
      have h1 : 8 * P δ / ‖b‖ ≤ 8 * Pt h σ / b.im := by
        rw [div_le_div_iff₀ hbpos hypos]
        nlinarith [Pt_nonneg h σ]
      have h2 : 2 * P δ / ‖b‖ ≤ 2 * Pt h σ / b.im := by
        rw [div_le_div_iff₀ hbpos hypos]
        nlinarith [Pt_nonneg h σ]
      exact mul_le_mul h1 (Real.exp_le_exp.mpr h2) (Real.exp_pos _).le
        (div_nonneg (by linarith [Pt_nonneg h σ]) hypos.le)
    calc _ ≤ 8 * P δ / ‖b‖ * Real.exp (2 * P δ / ‖b‖) := hnear
      _ ≤ Nb b.im h σ := hmono
      _ ≤ _ := le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le (by linarith))
  · -- far field
    push Not at hreg
    have hK := norm_K_le (b := b) (δ := δ) (by linarith) hbn hδre hb1
    have hG : 2 * (‖b‖ + ‖δ‖ + 1) ^ 2 / ‖b‖ ^ 2 *
        Real.exp ((b.re + δ.re - 1) * ‖δ‖ / (2 * ‖b‖) + π * (|b.im| + |δ.im|) + 1) ≤ Gb b.im h σ := by
      unfold Gb
      have hb1' : 1 ≤ ‖b‖ := by linarith
      have h1 : 2 * (‖b‖ + ‖δ‖ + 1) ^ 2 / ‖b‖ ^ 2 ≤ 2 * (2 + h + |σ|) ^ 2 := by
        rw [div_le_iff₀ (by positivity)]
        have : ‖b‖ + ‖δ‖ + 1 ≤ (2 + h + |σ|) * ‖b‖ := by nlinarith [abs_nonneg σ]
        have h0 : 0 ≤ ‖b‖ + ‖δ‖ + 1 := by positivity
        calc 2 * (‖b‖ + ‖δ‖ + 1) ^ 2 ≤ 2 * ((2 + h + |σ|) * ‖b‖) ^ 2 := by gcongr
          _ = 2 * (2 + h + |σ|) ^ 2 * ‖b‖ ^ 2 := by ring
      have h2 : (b.re + δ.re - 1) * ‖δ‖ / (2 * ‖b‖) ≤ (3 + h) * (h + |σ|) / (2 * b.im) := by
        rw [hδre', div_le_div_iff₀ (by positivity) (by positivity)]
        have hA : 0 ≤ b.re + h - 1 := by linarith
        have hB : b.re + h - 1 ≤ 3 + h := by linarith
        nlinarith [mul_nonneg hA (norm_nonneg δ), abs_nonneg σ, mul_le_mul hB hδn (norm_nonneg δ)
          (by linarith : (0:ℝ) ≤ 3 + h), mul_nonneg (mul_nonneg hA (norm_nonneg δ)) hypos.le]
      have h3 : |b.im| + |δ.im| = b.im + |σ| := by rw [hδim, abs_of_pos hypos]
      rw [h3]
      exact mul_le_mul h1 (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le (by positivity)
    have hone : 1 ≤ Real.exp (((h + |σ|) ^ 2 - b.im ^ 2 / 4) / (8 * c)) := by
      rw [Real.one_le_exp_iff]
      have : b.im / 2 < h + |σ| := hreg
      have h0 : 0 ≤ b.im / 2 := by positivity
      apply div_nonneg _ (by positivity)
      nlinarith
    calc ‖ρ b δ * cexp (Q b δ) - 1‖ ≤ ‖ρ b δ * cexp (Q b δ)‖ + 1 := by
          have := norm_sub_le (ρ b δ * cexp (Q b δ)) 1
          rwa [norm_one] at this
      _ ≤ Gb b.im h σ + 1 := by linarith [hK.trans hG]
      _ ≤ Real.exp (((h + |σ|) ^ 2 - b.im ^ 2 / 4) / (8 * c)) * (1 + Gb b.im h σ) := by
          nlinarith
      _ ≤ _ := le_add_of_nonneg_left hNb

/-! ### The integrated estimate -/

/-- The far-field linear coefficient `a = (3+h)/(2y) + π`. -/
noncomputable def aFar (y h : ℝ) : ℝ := (3 + h) / (2 * y) + π

/-- Near-field amplitude `A₁ = 48 (h²+h+1)/y · e^{(4h²+2h+2)/y}`. -/
noncomputable def A₁ (y h : ℝ) : ℝ := 48 * (h ^ 2 + h + 1) / y * Real.exp ((4 * h ^ 2 + 2 * h + 2) / y)

/-- Far-field amplitude `A₂ = e^{-y²/(32c)} e^{h²/(4c)} · 3 (2+h)² e^{(3+h)h/(2y) + πy + 1}`. -/
noncomputable def A₂ (c y h : ℝ) : ℝ :=
  Real.exp (-y ^ 2 / (32 * c)) * Real.exp (h ^ 2 / (4 * c)) *
    (3 * (2 + h) ^ 2 * Real.exp ((3 + h) * h / (2 * y) + π * y + 1))

lemma A₁_nonneg {y : ℝ} (hy : 0 < y) {h : ℝ} (hh0 : 0 ≤ h) : 0 ≤ A₁ y h := by
  unfold A₁; positivity

lemma A₂_nonneg (c y : ℝ) {h : ℝ} (hh0 : 0 ≤ h) : 0 ≤ A₂ c y h := by
  unfold A₂; positivity

/-- The near-field majorant in Gaussian-polynomial form. -/
lemma near_majorant {c : ℝ} (hc : 0 < c) {y : ℝ} (hy8 : 8 * c ≤ y) {h : ℝ} (hh0 : 0 ≤ h) (σ : ℝ) :
    Real.exp (-σ ^ 2 / c) * Nb y h σ ≤
      A₁ y h * ((1 + |σ|) ^ 2 * Real.exp (-(1 / (2 * c)) * σ ^ 2 + (1 / (4 * c)) * |σ|)) := by
  have hy : 0 < y := by linarith
  have hσ := abs_nonneg σ
  have hsq : |σ| ^ 2 = σ ^ 2 := sq_abs σ
  have hPt : Pt h σ ≤ 6 * (h ^ 2 + h + 1) * (1 + |σ|) ^ 2 := by
    unfold Pt
    nlinarith [mul_nonneg hh0 hσ, mul_nonneg (mul_nonneg hh0 hh0) hσ, mul_nonneg hh0 (mul_nonneg hσ hσ),
      mul_nonneg (mul_nonneg hh0 hh0) (mul_nonneg hσ hσ)]
  have hexp : -σ ^ 2 / c + 2 * Pt h σ / y ≤
      (4 * h ^ 2 + 2 * h + 2) / y + (-(1 / (2 * c)) * σ ^ 2 + (1 / (4 * c)) * |σ|) := by
    have h1 : 2 * Pt h σ / y ≤ (4 * h ^ 2 + 2 * h + 2) / y + 4 * σ ^ 2 / y + 2 * |σ| / y := by
      rw [← add_div, ← add_div, div_le_div_iff_of_pos_right hy]
      unfold Pt
      nlinarith [sq_nonneg (h - |σ|)]
    have h2 : 4 * σ ^ 2 / y ≤ σ ^ 2 / (2 * c) := by
      rw [div_le_div_iff₀ hy (by positivity)]
      nlinarith [sq_nonneg σ]
    have h3 : 2 * |σ| / y ≤ |σ| / (4 * c) := by
      rw [div_le_div_iff₀ hy (by positivity)]
      nlinarith
    have h4 : -σ ^ 2 / c + σ ^ 2 / (2 * c) = -(1 / (2 * c)) * σ ^ 2 := by field_simp; ring
    have h5 : |σ| / (4 * c) = (1 / (4 * c)) * |σ| := by ring
    linarith
  have hPt0 := Pt_nonneg h σ
  calc Real.exp (-σ ^ 2 / c) * Nb y h σ
      = (8 * Pt h σ / y) * Real.exp (-σ ^ 2 / c + 2 * Pt h σ / y) := by
        rw [Nb, Real.exp_add]; ring
    _ ≤ (8 * (6 * (h ^ 2 + h + 1) * (1 + |σ|) ^ 2) / y) *
        Real.exp ((4 * h ^ 2 + 2 * h + 2) / y + (-(1 / (2 * c)) * σ ^ 2 + (1 / (4 * c)) * |σ|)) := by
        gcongr
    _ = _ := by rw [A₁, Real.exp_add]; ring

/-- The far-field majorant in Gaussian-polynomial form. -/
lemma far_majorant {c : ℝ} (hc : 0 < c) {y : ℝ} (hy : 0 < y) {h : ℝ} (hh0 : 0 ≤ h) (σ : ℝ) :
    Real.exp (-σ ^ 2 / c) * (Real.exp (((h + |σ|) ^ 2 - y ^ 2 / 4) / (8 * c)) * (1 + Gb y h σ)) ≤
      A₂ c y h * ((1 + |σ|) ^ 2 * Real.exp (-(3 / (4 * c)) * σ ^ 2 + aFar y h * |σ|)) := by
  have hσ := abs_nonneg σ
  have hexp1 : -σ ^ 2 / c + ((h + |σ|) ^ 2 - y ^ 2 / 4) / (8 * c) ≤
      -y ^ 2 / (32 * c) + h ^ 2 / (4 * c) + -(3 / (4 * c)) * σ ^ 2 := by
    have : (h + |σ|) ^ 2 ≤ 2 * h ^ 2 + 2 * σ ^ 2 := by nlinarith [sq_nonneg (h - |σ|), sq_abs σ]
    have e : -σ ^ 2 / c + ((h + |σ|) ^ 2 - y ^ 2 / 4) / (8 * c) -
        (-y ^ 2 / (32 * c) + h ^ 2 / (4 * c) + -(3 / (4 * c)) * σ ^ 2) =
        ((h + |σ|) ^ 2 - (2 * h ^ 2 + 2 * σ ^ 2)) / (8 * c) := by field_simp; ring
    have : ((h + |σ|) ^ 2 - (2 * h ^ 2 + 2 * σ ^ 2)) / (8 * c) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    linarith
  have hX : (3 + h) * (h + |σ|) / (2 * y) + π * (y + |σ|) + 1 =
      ((3 + h) * h / (2 * y) + π * y + 1) + aFar y h * |σ| := by
    unfold aFar; field_simp; ring
  have hGb : 1 + Gb y h σ ≤ 3 * (2 + h) ^ 2 * (1 + |σ|) ^ 2 *
      Real.exp (((3 + h) * h / (2 * y) + π * y + 1) + aFar y h * |σ|) := by
    rw [Gb, hX]
    have hX0 : 0 ≤ ((3 + h) * h / (2 * y) + π * y + 1) + aFar y h * |σ| := by
      unfold aFar
      have := Real.pi_pos
      positivity
    have hE1 : 1 ≤ Real.exp (((3 + h) * h / (2 * y) + π * y + 1) + aFar y h * |σ|) :=
      Real.one_le_exp_iff.mpr hX0
    have hsq : (2 + h + |σ|) ^ 2 ≤ (2 + h) ^ 2 * (1 + |σ|) ^ 2 := by
      have : 2 + h + |σ| ≤ (2 + h) * (1 + |σ|) := by nlinarith
      calc (2 + h + |σ|) ^ 2 ≤ ((2 + h) * (1 + |σ|)) ^ 2 := by gcongr
        _ = _ := by ring
    have h1 : 1 ≤ (2 + h) ^ 2 * (1 + |σ|) ^ 2 := by nlinarith
    set E := Real.exp (((3 + h) * h / (2 * y) + π * y + 1) + aFar y h * |σ|)
    nlinarith [mul_le_mul_of_nonneg_right hsq (by positivity : (0:ℝ) ≤ E)]
  have hL : Real.exp (-σ ^ 2 / c) * (Real.exp (((h + |σ|) ^ 2 - y ^ 2 / 4) / (8 * c)) * (1 + Gb y h σ)) =
      Real.exp (-σ ^ 2 / c + ((h + |σ|) ^ 2 - y ^ 2 / 4) / (8 * c)) * (1 + Gb y h σ) := by
    rw [Real.exp_add]; ring
  rw [hL]
  calc Real.exp (-σ ^ 2 / c + ((h + |σ|) ^ 2 - y ^ 2 / 4) / (8 * c)) * (1 + Gb y h σ)
      ≤ Real.exp (-y ^ 2 / (32 * c) + h ^ 2 / (4 * c) + -(3 / (4 * c)) * σ ^ 2) *
        (3 * (2 + h) ^ 2 * (1 + |σ|) ^ 2 *
          Real.exp (((3 + h) * h / (2 * y) + π * y + 1) + aFar y h * |σ|)) :=
        mul_le_mul (Real.exp_le_exp.mpr hexp1) hGb (by linarith [Gb_nonneg y h σ]) (Real.exp_pos _).le
    _ = _ := by
        rw [A₂]
        simp only [Real.exp_add]
        ring

/-- `‖gw c M₀ σ‖ = e^{-σ²/c}`. -/
lemma norm_gw (c M₀ σ : ℝ) : ‖gw c M₀ σ‖ = Real.exp (-σ ^ 2 / c) := by
  rw [gw, Complex.norm_exp]
  congr 1
  have : (-(σ : ℂ) ^ 2 / c + 2 * (M₀ : ℂ) * σ * I / c) =
      ((-σ ^ 2 / c : ℝ) : ℂ) + ((2 * M₀ * σ / c : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
    add_zero]

/-- Gaussian-polynomial integrals, named. -/
noncomputable def Ig (b a : ℝ) : ℝ := Real.exp ((a + 2) ^ 2 / (2 * b)) * Real.sqrt (π / (b / 2))

lemma integral_gauss_poly_two_le {b : ℝ} (hb : 0 < b) (a : ℝ) :
    ∫ σ : ℝ, (1 + |σ|) ^ 2 * Real.exp (-b * σ ^ 2 + a * |σ|) ≤ Ig b a := by
  have := integral_gauss_poly_le hb a 2
  rw [Ig]
  simpa using this

/-- **The integrated estimate**: for `2 ≤ Re b ≤ 4`, `y = Im s ≥ max 2 (8c)`,
`‖E_n(s)‖ ≤ e^{M₀²/c}(πc)^{-1/2} (A₁ Ig(1/(2c), 1/(4c)) + A₂ Ig(3/(4c), aFar))`. -/
theorem norm_E_le {c M₀ : ℝ} (hc : 0 < c) (n : ℕ+) {s : ℂ} (hb2 : 2 ≤ (s + M₀).re)
    (hb4 : (s + M₀).re ≤ 4) (hy2 : 2 ≤ s.im) (hy8 : 8 * c ≤ s.im) :
    ‖E c M₀ n s‖ ≤ (Real.exp (M₀ ^ 2 / c) / Real.sqrt (π * c)) *
      (A₁ s.im (hh c n) * Ig (1 / (2 * c)) (1 / (4 * c)) +
        A₂ c s.im (hh c n) * Ig (3 / (4 * c)) (aFar s.im (hh c n))) := by
  set y := s.im with hydef
  set h := hh c n with hhdef
  have hh0 : 0 ≤ h := hh_nonneg hc n
  have hy : 0 < y := by linarith
  have hbim : (s + M₀).im = y := by simp [hydef]
  -- pointwise bound on the integrand
  have hpt : ∀ σ : ℝ, ‖(K c M₀ n s σ - 1) * gw c M₀ σ‖ ≤
      A₁ y h * ((1 + |σ|) ^ 2 * Real.exp (-(1 / (2 * c)) * σ ^ 2 + (1 / (4 * c)) * |σ|)) +
      A₂ c y h * ((1 + |σ|) ^ 2 * Real.exp (-(3 / (4 * c)) * σ ^ 2 + aFar y h * |σ|)) := by
    intro σ
    rw [norm_mul, norm_gw]
    have hK := norm_K_sub_one_le_unified hc (b := s + M₀) hb2 hb4 (by rw [hbim]; exact hy2) hh0 σ
    rw [hbim] at hK
    have : K c M₀ n s σ = ρ (s + M₀) (((h : ℝ) : ℂ) + σ * I) *
        cexp (Q (s + M₀) (((h : ℝ) : ℂ) + σ * I)) := rfl
    rw [this]
    calc ‖ρ (s + M₀) (((h : ℝ) : ℂ) + σ * I) * cexp (Q (s + M₀) (((h : ℝ) : ℂ) + σ * I)) - 1‖ *
          Real.exp (-σ ^ 2 / c)
        ≤ (Nb y h σ + Real.exp (((h + |σ|) ^ 2 - y ^ 2 / 4) / (8 * c)) * (1 + Gb y h σ)) *
          Real.exp (-σ ^ 2 / c) := mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le
      _ = Real.exp (-σ ^ 2 / c) * Nb y h σ +
          Real.exp (-σ ^ 2 / c) * (Real.exp (((h + |σ|) ^ 2 - y ^ 2 / 4) / (8 * c)) * (1 + Gb y h σ)) := by
          ring
      _ ≤ _ := add_le_add (near_majorant hc hy8 hh0 σ) (far_majorant hc hy hh0 σ)
  have hint1 := integrable_gauss_poly (b := 1 / (2 * c)) (by positivity) (1 / (4 * c)) 2
  have hint2 := integrable_gauss_poly (b := 3 / (4 * c)) (by positivity) (aFar y h) 2
  have hmaj : Integrable fun σ : ℝ =>
      A₁ y h * ((1 + |σ|) ^ 2 * Real.exp (-(1 / (2 * c)) * σ ^ 2 + (1 / (4 * c)) * |σ|)) +
      A₂ c y h * ((1 + |σ|) ^ 2 * Real.exp (-(3 / (4 * c)) * σ ^ 2 + aFar y h * |σ|)) :=
    (hint1.const_mul _).add (hint2.const_mul _)
  rw [E, norm_mul, norm_mul, Complex.norm_exp, norm_div, norm_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr (by positivity))]
  simp only [Complex.ofReal_re]
  have hL : Real.exp (M₀ ^ 2 / c) * (1 / Real.sqrt (π * c)) * ‖∫ σ : ℝ, (K c M₀ n s σ - 1) * gw c M₀ σ‖ =
      Real.exp (M₀ ^ 2 / c) / Real.sqrt (π * c) * ‖∫ σ : ℝ, (K c M₀ n s σ - 1) * gw c M₀ σ‖ := by
    ring
  rw [hL]
  have hI := MeasureTheory.norm_integral_le_of_norm_le hmaj (ae_of_all _ hpt)
  rw [integral_add (hint1.const_mul _) (hint2.const_mul _), MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul] at hI
  have hA1 := A₁_nonneg hy hh0
  have hA2 := A₂_nonneg c y hh0
  have hK0 : 0 ≤ Real.exp (M₀ ^ 2 / c) / Real.sqrt (π * c) := by positivity
  have hI1 := integral_gauss_poly_two_le (b := 1 / (2 * c)) (by positivity) (1 / (4 * c))
  have hI2 := integral_gauss_poly_two_le (b := 3 / (4 * c)) (by positivity) (aFar y h)
  calc Real.exp (M₀ ^ 2 / c) / Real.sqrt (π * c) * ‖∫ σ : ℝ, (K c M₀ n s σ - 1) * gw c M₀ σ‖
      ≤ Real.exp (M₀ ^ 2 / c) / Real.sqrt (π * c) *
        (A₁ y h * (∫ σ : ℝ, (1 + |σ|) ^ 2 * Real.exp (-(1 / (2 * c)) * σ ^ 2 + (1 / (4 * c)) * |σ|)) +
         A₂ c y h * (∫ σ : ℝ, (1 + |σ|) ^ 2 * Real.exp (-(3 / (4 * c)) * σ ^ 2 + aFar y h * |σ|))) :=
        mul_le_mul_of_nonneg_left hI hK0
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hK0
        exact add_le_add (mul_le_mul_of_nonneg_left hI1 hA1) (mul_le_mul_of_nonneg_left hI2 hA2)

/-! ### Absorbing the coefficient `a_n = e^{-h²/c}` -/

/-- Near field: `a_n A₁ ≤ (48 e^{3/(8c)}/y) (h²+h+1) e^{-3h²/(8c)}` for `y ≥ 8c`. -/
lemma coef_A₁_le {c : ℝ} (hc : 0 < c) {y : ℝ} (hy8 : 8 * c ≤ y) {h : ℝ} (hh0 : 0 ≤ h) :
    Real.exp (-h ^ 2 / c) * A₁ y h ≤
      (48 * Real.exp (3 / (8 * c)) / y) * ((h ^ 2 + h + 1) * Real.exp (-(3 / (8 * c)) * h ^ 2)) := by
  have hy : 0 < y := by linarith
  have h1 : (4 * h ^ 2 + 2 * h + 2) / y ≤ (5 * h ^ 2 + 3) / (8 * c) := by
    rw [div_le_div_iff₀ hy (by positivity)]
    nlinarith [sq_nonneg (h - 1), mul_nonneg (by positivity : (0:ℝ) ≤ 4 * h ^ 2 + 2 * h + 2)
      (by linarith : (0:ℝ) ≤ y - 8 * c)]
  have hexp : Real.exp (-h ^ 2 / c) * Real.exp ((4 * h ^ 2 + 2 * h + 2) / y) ≤
      Real.exp (3 / (8 * c)) * Real.exp (-(3 / (8 * c)) * h ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : -h ^ 2 / c + (5 * h ^ 2 + 3) / (8 * c) = 3 / (8 * c) + -(3 / (8 * c)) * h ^ 2 := by
      field_simp; ring
    linarith
  calc Real.exp (-h ^ 2 / c) * A₁ y h
      = (48 * (h ^ 2 + h + 1) / y) * (Real.exp (-h ^ 2 / c) * Real.exp ((4 * h ^ 2 + 2 * h + 2) / y)) := by
        rw [A₁]; ring
    _ ≤ (48 * (h ^ 2 + h + 1) / y) * (Real.exp (3 / (8 * c)) * Real.exp (-(3 / (8 * c)) * h ^ 2)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by ring

/-- The far-field constant `D₂(c)`. -/
noncomputable def D₂ (c : ℝ) : ℝ :=
  3 * Real.exp (1 + 9 / (64 * c) + (4 * c / 3) * (π + 2) ^ 2 + 3 / (32 * c)) *
    Real.sqrt (π / ((3 / (4 * c)) / 2))

/-- Far field: `a_n A₂ Ig(3/(4c), aFar) ≤ D₂ (2+h)² e^{-59h²/(96c)} e^{-y²/(32c) + πy}` for `y ≥ 8c`. -/
lemma coef_A₂_le {c : ℝ} (hc : 0 < c) {y : ℝ} (hy8 : 8 * c ≤ y) {h : ℝ} (hh0 : 0 ≤ h) :
    Real.exp (-h ^ 2 / c) * (A₂ c y h * Ig (3 / (4 * c)) (aFar y h)) ≤
      D₂ c * ((2 + h) ^ 2 * Real.exp (-(59 / (96 * c)) * h ^ 2)) *
        Real.exp (-y ^ 2 / (32 * c) + π * y) := by
  have hy : 0 < y := by linarith
  have hpi := Real.pi_pos
  -- the two exponent estimates
  have hE1 : (3 + h) * h / (2 * y) ≤ h ^ 2 / (8 * c) + 9 / (64 * c) := by
    have : (3 + h) * h / (2 * y) ≤ (3 + h) * h / (16 * c) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    refine this.trans ?_
    rw [show h ^ 2 / (8 * c) + 9 / (64 * c) = (8 * h ^ 2 + 9) / (64 * c) by field_simp; ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (2 * h - 3), hc]
  have ha : aFar y h ≤ (3 + h) / (16 * c) + π := by
    unfold aFar
    have : (3 + h) / (2 * y) ≤ (3 + h) / (16 * c) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    linarith
  have ha0 : 0 ≤ aFar y h := by unfold aFar; positivity
  have hE2 : (aFar y h + 2) ^ 2 / (2 * (3 / (4 * c))) ≤
      (4 * c / 3) * (π + 2) ^ 2 + (h ^ 2 / (96 * c) + 3 / (32 * c)) := by
    have hsq : (aFar y h + 2) ^ 2 ≤ 2 * (π + 2) ^ 2 + 2 * ((3 + h) / (16 * c)) ^ 2 := by
      have h0 : aFar y h + 2 ≤ (π + 2) + (3 + h) / (16 * c) := by linarith
      have h00 : 0 ≤ aFar y h + 2 := by linarith
      calc (aFar y h + 2) ^ 2 ≤ ((π + 2) + (3 + h) / (16 * c)) ^ 2 := by gcongr
        _ ≤ _ := by nlinarith [sq_nonneg ((π + 2) - (3 + h) / (16 * c))]
    have h3h : (3 + h) ^ 2 ≤ 2 * h ^ 2 + 18 := by nlinarith [sq_nonneg (h - 3)]
    have hdiv : (aFar y h + 2) ^ 2 / (2 * (3 / (4 * c))) = (2 * c / 3) * (aFar y h + 2) ^ 2 := by
      field_simp; ring
    rw [hdiv]
    calc (2 * c / 3) * (aFar y h + 2) ^ 2
        ≤ (2 * c / 3) * (2 * (π + 2) ^ 2 + 2 * ((3 + h) / (16 * c)) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (4 * c / 3) * (π + 2) ^ 2 + (3 + h) ^ 2 / (192 * c) := by field_simp; ring
      _ ≤ (4 * c / 3) * (π + 2) ^ 2 + (2 * h ^ 2 + 18) / (192 * c) := by gcongr
      _ = _ := by field_simp; ring
  -- assemble
  have hLHS : Real.exp (-h ^ 2 / c) * (A₂ c y h * Ig (3 / (4 * c)) (aFar y h)) =
      (3 * (2 + h) ^ 2 * Real.sqrt (π / ((3 / (4 * c)) / 2))) *
        Real.exp (-h ^ 2 / c + -y ^ 2 / (32 * c) + h ^ 2 / (4 * c) +
          ((3 + h) * h / (2 * y) + π * y + 1) + (aFar y h + 2) ^ 2 / (2 * (3 / (4 * c)))) := by
    rw [A₂, Ig]
    simp only [Real.exp_add]
    ring
  have hRHS : D₂ c * ((2 + h) ^ 2 * Real.exp (-(59 / (96 * c)) * h ^ 2)) *
      Real.exp (-y ^ 2 / (32 * c) + π * y) =
      (3 * (2 + h) ^ 2 * Real.sqrt (π / ((3 / (4 * c)) / 2))) *
        Real.exp ((1 + 9 / (64 * c) + (4 * c / 3) * (π + 2) ^ 2 + 3 / (32 * c)) +
          -(59 / (96 * c)) * h ^ 2 + (-y ^ 2 / (32 * c) + π * y)) := by
    rw [D₂]
    simp only [Real.exp_add]
    ring
  rw [hLHS, hRHS]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have hid : -h ^ 2 / c + h ^ 2 / (4 * c) + h ^ 2 / (8 * c) + h ^ 2 / (96 * c) =
      -(59 / (96 * c)) * h ^ 2 := by field_simp; ring
  linarith

/-! ### Summability of the weights -/

/-- `(1+h)^k e^{-κ h²} n^β` is summable over `n ≥ 1`, `h = (c/2) log n`, for every `κ > 0`. -/
lemma summable_weight {c : ℝ} (hc : 0 < c) {κ : ℝ} (hκ : 0 < κ) (k : ℕ) (β : ℝ) :
    Summable fun n : ℕ+ => (1 + hh c n) ^ k * Real.exp (-κ * (hh c n) ^ 2) * (n : ℝ) ^ β := by
  set c' : ℝ := κ * c ^ 2 / 4 with hc'
  have hc'pos : 0 < c' := by positivity
  set s : ℂ := ((-(k * c / 2 + β) : ℝ) : ℂ) with hsdef
  have hsum := DBNFtZero.summable_norm_term hc'pos s
  have hsum' := (summable_pnat_iff_summable_nat
    (f := fun n : ℕ => ‖LSeries.term (DBNFtZero.gaussCoeff c') s n‖)).mpr hsum
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsum'
  · have := hh_nonneg hc n
    positivity
  · have hn0 : (n : ℕ) ≠ 0 := n.ne_zero
    have hnpos : (0 : ℝ) < n := by exact_mod_cast n.pos
    have hh0 := hh_nonneg hc n
    rw [DBNFtZero.norm_term_eq c' s hn0]
    have hre : s.re = -(k * c / 2 + β) := by rw [hsdef]; simp
    rw [hre]
    -- (1+h)^k ≤ e^{k h}
    have hpow : (1 + hh c n) ^ k ≤ Real.exp (k * hh c n) := by
      calc (1 + hh c n) ^ k ≤ (Real.exp (hh c n)) ^ k := by
            gcongr; have := Real.add_one_le_exp (hh c n); linarith
        _ = Real.exp (k * hh c n) := by rw [← Real.exp_nat_mul]
    have hnβ : (n : ℝ) ^ β = Real.exp (β * Real.log n) := by
      rw [Real.rpow_def_of_pos hnpos]; ring_nf
    have hhh : hh c n = c / 2 * Real.log n := rfl
    calc (1 + hh c n) ^ k * Real.exp (-κ * (hh c n) ^ 2) * (n : ℝ) ^ β
        ≤ Real.exp (k * hh c n) * Real.exp (-κ * (hh c n) ^ 2) * (n : ℝ) ^ β := by
          gcongr
      _ = Real.exp (-c' * (Real.log n) ^ 2 - -(k * c / 2 + β) * Real.log n) := by
          rw [hnβ, ← Real.exp_add, ← Real.exp_add, hhh, hc']
          congr 1
          ring

/-! ### The uniform estimate on the strip -/

/-- The near- and far-field weights (summable in `n`), with the strip centre `x₀` built in through
the factor `n^{1-x₀} ≥ n^{-x}` for `|x - x₀| ≤ 1`. -/
noncomputable def T₁ (c x₀ : ℝ) (n : ℕ+) : ℝ :=
  ((hh c n) ^ 2 + hh c n + 1) * Real.exp (-(3 / (8 * c)) * (hh c n) ^ 2) * (n : ℝ) ^ (1 - x₀)

noncomputable def T₂ (c x₀ : ℝ) (n : ℕ+) : ℝ :=
  (2 + hh c n) ^ 2 * Real.exp (-(59 / (96 * c)) * (hh c n) ^ 2) * (n : ℝ) ^ (1 - x₀)

lemma T₁_nonneg {c : ℝ} (hc : 0 < c) (x₀ : ℝ) (n : ℕ+) : 0 ≤ T₁ c x₀ n := by
  unfold T₁; have := hh_nonneg hc n; positivity

lemma T₂_nonneg {c : ℝ} (hc : 0 < c) (x₀ : ℝ) (n : ℕ+) : 0 ≤ T₂ c x₀ n := by
  unfold T₂; have := hh_nonneg hc n; positivity

lemma summable_T₁ {c : ℝ} (hc : 0 < c) (x₀ : ℝ) : Summable (T₁ c x₀) := by
  refine Summable.of_nonneg_of_le (T₁_nonneg hc x₀) (fun n => ?_)
    (summable_weight hc (κ := 3 / (8 * c)) (by positivity) 2 (1 - x₀))
  unfold T₁
  have hh0 := hh_nonneg hc n
  have h1 : (hh c n) ^ 2 + hh c n + 1 ≤ (1 + hh c n) ^ 2 := by nlinarith
  gcongr

lemma summable_T₂ {c : ℝ} (hc : 0 < c) (x₀ : ℝ) : Summable (T₂ c x₀) := by
  have h := (summable_weight hc (κ := 59 / (96 * c)) (by positivity) 2 (1 - x₀)).mul_left 4
  refine Summable.of_nonneg_of_le (T₂_nonneg hc x₀) (fun n => ?_) h
  unfold T₂
  have hh0 := hh_nonneg hc n
  have h1 : (2 + hh c n) ^ 2 ≤ 4 * (1 + hh c n) ^ 2 := by nlinarith
  have h2 : 0 ≤ Real.exp (-(59 / (96 * c)) * (hh c n) ^ 2) * (n : ℝ) ^ (1 - x₀) := by positivity
  calc (2 + hh c n) ^ 2 * Real.exp (-(59 / (96 * c)) * (hh c n) ^ 2) * (n : ℝ) ^ (1 - x₀)
      = (2 + hh c n) ^ 2 * (Real.exp (-(59 / (96 * c)) * (hh c n) ^ 2) * (n : ℝ) ^ (1 - x₀)) := by ring
    _ ≤ 4 * (1 + hh c n) ^ 2 * (Real.exp (-(59 / (96 * c)) * (hh c n) ^ 2) * (n : ℝ) ^ (1 - x₀)) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = _ := by ring

/-- The constant in front of the near-field weight. -/
noncomputable def C₁ (c x₀ : ℝ) : ℝ :=
  (Real.exp ((3 - x₀) ^ 2 / c) / Real.sqrt (π * c)) * (48 * Real.exp (3 / (8 * c)) *
    Ig (1 / (2 * c)) (1 / (4 * c)))

/-- The constant in front of the far-field weight. -/
noncomputable def C₂ (c x₀ : ℝ) : ℝ := (Real.exp ((3 - x₀) ^ 2 / c) / Real.sqrt (π * c)) * D₂ c

lemma C₁_nonneg {c : ℝ} (hc : 0 < c) (x₀ : ℝ) : 0 ≤ C₁ c x₀ := by unfold C₁ Ig; positivity
lemma C₂_nonneg {c : ℝ} (hc : 0 < c) (x₀ : ℝ) : 0 ≤ C₂ c x₀ := by unfold C₂ D₂; positivity

/-- **Per-term bound on the strip**: for `|Re s − x₀| ≤ 1` and `Im s ≥ max 2 (8c)`,
`‖a_n n^{-s} E_n(s)‖ ≤ C₁ T₁(n)/y + C₂ T₂(n) e^{-y²/(32c) + πy}` with `M₀ = 3 − x₀`. -/
theorem norm_term_le_weights {c : ℝ} (hc : 0 < c) (x₀ : ℝ) (n : ℕ+) {s : ℂ}
    (hx : |s.re - x₀| ≤ 1) (hy2 : 2 ≤ s.im) (hy8 : 8 * c ≤ s.im) :
    ‖(coef c n : ℂ) * (1 / (n : ℂ) ^ s) * E c (3 - x₀) n s‖ ≤
      C₁ c x₀ * T₁ c x₀ n / s.im +
        C₂ c x₀ * T₂ c x₀ n * Real.exp (-s.im ^ 2 / (32 * c) + π * s.im) := by
  have hxx := abs_le.mp hx
  have hb2 : 2 ≤ (s + ((3 - x₀ : ℝ) : ℂ)).re := by simp; linarith
  have hb4 : (s + ((3 - x₀ : ℝ) : ℂ)).re ≤ 4 := by simp; linarith
  have hy : 0 < s.im := by linarith
  have hh0 := hh_nonneg hc n
  have hE := norm_E_le hc n hb2 hb4 hy2 hy8
  set y := s.im
  set h := hh c n with hhdef
  set K₀ := Real.exp ((3 - x₀) ^ 2 / c) / Real.sqrt (π * c) with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  have hcoef : ‖(coef c n : ℂ)‖ = Real.exp (-h ^ 2 / c) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (coef_pos c n)]; rfl
  have hn : ‖(1 / (n : ℂ) ^ s)‖ ≤ (n : ℝ) ^ (1 - x₀) := by
    rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos n.pos, one_div, ← Real.rpow_neg (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast n.pos) (by linarith)
  have hn0 : 0 ≤ (n : ℝ) ^ (1 - x₀) := by positivity
  have hA1 := coef_A₁_le hc hy8 hh0
  have hA2 := coef_A₂_le hc hy8 hh0
  have hIg1 : 0 ≤ Ig (1 / (2 * c)) (1 / (4 * c)) := by unfold Ig; positivity
  have hIg2 : 0 ≤ Ig (3 / (4 * c)) (aFar y h) := by unfold Ig; positivity
  have hA1' := A₁_nonneg hy hh0
  have hA2' := A₂_nonneg c y hh0
  rw [norm_mul, norm_mul, hcoef]
  calc Real.exp (-h ^ 2 / c) * ‖(1 / (n : ℂ) ^ s)‖ * ‖E c (3 - x₀) n s‖
      ≤ Real.exp (-h ^ 2 / c) * (n : ℝ) ^ (1 - x₀) *
        (K₀ * (A₁ y h * Ig (1 / (2 * c)) (1 / (4 * c)) + A₂ c y h * Ig (3 / (4 * c)) (aFar y h))) := by
        gcongr
    _ = K₀ * (n : ℝ) ^ (1 - x₀) * (Real.exp (-h ^ 2 / c) * A₁ y h) * Ig (1 / (2 * c)) (1 / (4 * c)) +
        K₀ * (n : ℝ) ^ (1 - x₀) * (Real.exp (-h ^ 2 / c) * (A₂ c y h * Ig (3 / (4 * c)) (aFar y h))) := by
        ring
    _ ≤ K₀ * (n : ℝ) ^ (1 - x₀) *
          ((48 * Real.exp (3 / (8 * c)) / y) * ((h ^ 2 + h + 1) * Real.exp (-(3 / (8 * c)) * h ^ 2))) *
          Ig (1 / (2 * c)) (1 / (4 * c)) +
        K₀ * (n : ℝ) ^ (1 - x₀) *
          (D₂ c * ((2 + h) ^ 2 * Real.exp (-(59 / (96 * c)) * h ^ 2)) *
            Real.exp (-y ^ 2 / (32 * c) + π * y)) := by
        gcongr
    _ = _ := by
        rw [C₁, C₂, T₁, T₂, hK₀, hhdef]
        field_simp

/-- **The error series is small, uniformly on the strip.**  With `M₀ = 3 − x₀`: for every `ε > 0`
there is `Y` such that for all `s` with `|Re s − x₀| ≤ 1` and `Im s ≥ Y` the error series converges
and `‖∑_n a_n n^{-s} E_n(s)‖ ≤ ε`. -/
theorem error_sum_small {c : ℝ} (hc : 0 < c) (x₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Y : ℝ, ∀ s : ℂ, |s.re - x₀| ≤ 1 → Y ≤ s.im →
      (Summable fun n : ℕ+ => (coef c n : ℂ) * (1 / (n : ℂ) ^ s) * E c (3 - x₀) n s) ∧
      ‖∑' n : ℕ+, (coef c n : ℂ) * (1 / (n : ℂ) ^ s) * E c (3 - x₀) n s‖ ≤ ε := by
  set S₁ : ℝ := C₁ c x₀ * ∑' n : ℕ+, T₁ c x₀ n with hS₁
  set S₂ : ℝ := C₂ c x₀ * ∑' n : ℕ+, T₂ c x₀ n with hS₂
  -- the bound function tends to zero
  have hlim : Tendsto (fun y : ℝ => S₁ / y + S₂ * Real.exp (-y ^ 2 / (32 * c) + π * y)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => S₁ / y) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have h2 : Tendsto (fun y : ℝ => Real.exp (-y ^ 2 / (32 * c) + π * y)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ Real.tendsto_exp_neg_atTop_nhds_zero
      filter_upwards [eventually_ge_atTop (32 * c * (π + 1))] with y hy
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have hy0 : 0 ≤ y := le_trans (by positivity) hy
      rw [div_add' _ _ _ (by positivity : (32 * c : ℝ) ≠ 0), div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_pos]
    simpa using h1.add (h2.const_mul S₂)
  have hev : ∀ᶠ y : ℝ in atTop, S₁ / y + S₂ * Real.exp (-y ^ 2 / (32 * c) + π * y) < ε :=
    hlim.eventually (gt_mem_nhds hε)
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.mp hev
  refine ⟨max Y₁ (max 2 (8 * c)), fun s hx hY => ?_⟩
  have hy2 : 2 ≤ s.im := le_trans (le_max_of_le_right (le_max_left _ _)) hY
  have hy8 : 8 * c ≤ s.im := le_trans (le_max_of_le_right (le_max_right _ _)) hY
  have hy : 0 < s.im := by linarith
  have hpt := fun n => norm_term_le_weights hc x₀ n hx hy2 hy8
  have hbound : Summable fun n : ℕ+ => C₁ c x₀ * T₁ c x₀ n / s.im +
      C₂ c x₀ * T₂ c x₀ n * Real.exp (-s.im ^ 2 / (32 * c) + π * s.im) :=
    (((summable_T₁ hc x₀).mul_left _).div_const _).add (((summable_T₂ hc x₀).mul_left _).mul_right _)
  have hsum : Summable fun n : ℕ+ => (coef c n : ℂ) * (1 / (n : ℂ) ^ s) * E c (3 - x₀) n s :=
    Summable.of_norm_bounded hbound hpt
  refine ⟨hsum, ?_⟩
  calc ‖∑' n : ℕ+, (coef c n : ℂ) * (1 / (n : ℂ) ^ s) * E c (3 - x₀) n s‖
      ≤ ∑' n : ℕ+, ‖(coef c n : ℂ) * (1 / (n : ℂ) ^ s) * E c (3 - x₀) n s‖ :=
        norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ+, (C₁ c x₀ * T₁ c x₀ n / s.im +
          C₂ c x₀ * T₂ c x₀ n * Real.exp (-s.im ^ 2 / (32 * c) + π * s.im)) :=
        hsum.norm.tsum_le_tsum hpt hbound
    _ = S₁ / s.im + S₂ * Real.exp (-s.im ^ 2 / (32 * c) + π * s.im) := by
        rw [(((summable_T₁ hc x₀).mul_left _).div_const _).tsum_add
          (((summable_T₂ hc x₀).mul_left _).mul_right _), tsum_div_const, tsum_mul_right,
          tsum_mul_left, tsum_mul_left, hS₁, hS₂]
    _ ≤ ε := (hY₁ s.im (le_trans (le_max_left _ _) hY)).le

end DBNSaddle
