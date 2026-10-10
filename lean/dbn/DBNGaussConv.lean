/-
  DBNGaussConv -- `H_t` for `t < 0` as a Gaussian convolution of `H_0`, and its Dirichlet expansion.

  Step 4 of the Lambda >= 0 (Newman's conjecture) formalization following Dobner
  (arXiv:2005.05142, section 3, eq. (9)); see NEWMAN_LAMBDA_NONNEG_SCOPING_2026-10-10.md section 6.

  For `c > 0` the heat factor `e^{-cu²}` is the Fourier transform of a Gaussian, so (Fubini)
      H_{-c}(z) = (4πc)^{-1/2} ∫_ℝ e^{-ω²/(4c)} H_0(z + ω) dω.
  The `ω`-line may be moved vertically (Cauchy on rectangles; `H_0` is entire and bounded on
  horizontal strips) into the region `Im (z + ω + iβ) < -1`, where the island's `DBNStrip` gives
  `H_0 = ∑_n γ(s) n^{-s}` termwise with `γ(v) = (1/16) v (v-1) π^{-v/2} Γ(v/2)`, `s = 1/2 + iz/2`.
  Interchanging sum and integral (dominated by `‖Γ(v/2)‖ ≤ Γ(Re v/2)`) gives, in the variable `s`,
      ξ_c(s) := H_{-c}(-i(2s-1)) = ∑_{n ≥ 1} B_n(s),
      B_n(s) = (πc)^{-1/2} ∫_ℝ γ(a + iτ) n^{-(a+iτ)} e^{(a + iτ - s)²/c} dτ      (any a > 1),
  which is Dobner's (9) with the contour on `Re v = a`.

  Nothing here is RH.  conjecture1_proved = False.
-/
import Mathlib
import DBNDefs
import DBNStrip

open Complex Filter Topology MeasureTheory Set
open scoped Real

namespace DBNGaussConv

/-! ### `‖Γ(v)‖ ≤ Γ(Re v)` on the right half-plane -/

theorem norm_Gamma_le_Gamma_re {v : ℂ} (hv : 0 < v.re) : ‖Complex.Gamma v‖ ≤ Real.Gamma v.re := by
  rw [Complex.Gamma_eq_integral hv, Real.Gamma_eq_integral hv, Complex.GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx' : (0 : ℝ) < x := hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_cpow_eq_rpow_re_of_pos hx', Complex.sub_re, Complex.one_re]

/-! ### The two-sided fold of `H_t` for `t ≤ 0` -/

/-- The two-sided heat integrand `e^{tu²} Φ(u) e^{izu}`. -/
noncomputable def heatIntegrand (t : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  ((Real.exp (t * u ^ 2) : ℝ) : ℂ) * DBN.expIntegrand z u

lemma norm_heatIntegrand_le {t : ℝ} (ht : t ≤ 0) (z : ℂ) (u : ℝ) :
    ‖heatIntegrand t z u‖ ≤ ‖DBN.expIntegrand z u‖ := by
  rw [heatIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have : Real.exp (t * u ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg u])
  calc Real.exp (t * u ^ 2) * ‖DBN.expIntegrand z u‖ ≤ 1 * ‖DBN.expIntegrand z u‖ := by gcongr
    _ = _ := one_mul _

lemma measurable_heatIntegrand (t : ℝ) (z : ℂ) : Measurable (heatIntegrand t z) := by
  unfold heatIntegrand
  exact (Complex.continuous_ofReal.measurable.comp (by fun_prop : Measurable fun u : ℝ =>
    Real.exp (t * u ^ 2))).mul (DBN.continuous_expIntegrand z).measurable

lemma integrable_heatIntegrand {t : ℝ} (ht : t ≤ 0) (z : ℂ) : Integrable (heatIntegrand t z) :=
  (DBN.integrable_expIntegrand z).norm.mono' (measurable_heatIntegrand t z).aestronglyMeasurable
    (ae_of_all _ fun u => norm_heatIntegrand_le ht z u)

lemma heatIntegrand_neg (t : ℝ) (z : ℂ) (u : ℝ) : heatIntegrand t z (-u) = heatIntegrand t (-z) u := by
  unfold heatIntegrand
  rw [DBN.expIntegrand_neg]
  congr 2
  ring

/-- **The two-sided fold**: `H_t(z) = (1/2) ∫_ℝ e^{tu²} Φ(u) e^{izu} du` for `t ≤ 0`. -/
theorem H_eq_half_integral {t : ℝ} (ht : t ≤ 0) (z : ℂ) :
    DBN.H t z = (1 / 2 : ℂ) * ∫ u : ℝ, heatIntegrand t z u := by
  have hpt : ∀ u : ℝ, DBN.HIntegrand t z u = (heatIntegrand t z u + heatIntegrand t z (-u)) / 2 := by
    intro u
    have hcos : Complex.cos (z * u)
        = (Complex.exp (z * u * Complex.I) + Complex.exp (-(z * u) * Complex.I)) / 2 := rfl
    have harg : z * ((-u : ℝ) : ℂ) * Complex.I = -(z * u) * Complex.I := by push_cast; ring
    unfold DBN.HIntegrand heatIntegrand DBN.expIntegrand
    rw [hcos, DBN.Φ_neg, harg]
    push_cast
    ring
  have hint := integrable_heatIntegrand ht z
  have hInt1 : IntegrableOn (heatIntegrand t z) (Ioi 0) := hint.integrableOn
  have hInt2 : IntegrableOn (fun u ↦ heatIntegrand t z (-u)) (Ioi 0) := by
    simp_rw [heatIntegrand_neg]
    exact (integrable_heatIntegrand ht (-z)).integrableOn
  unfold DBN.H
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ ↦ hpt u), integral_div,
    integral_add hInt1 hInt2, integral_comp_neg_Ioi (f := heatIntegrand t z), neg_zero,
    ← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hInt1]
  ring

/-! ### The Gaussian representation -/

/-- The real Gaussian kernel `e^{-ω²/(4c)}` (as a complex number). -/
noncomputable def gaussKer (c : ℝ) (ω : ℝ) : ℂ := ((Real.exp (-ω ^ 2 / (4 * c)) : ℝ) : ℂ)

lemma gaussK_eq (c : ℝ) (ω : ℝ) : gaussKer c ω = cexp (-(1 / (4 * c) : ℂ) * (ω : ℂ) ^ 2) := by
  rw [gaussKer, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

lemma integrable_gaussK {c : ℝ} (hc : 0 < c) : Integrable (gaussKer c) := by
  have h := integrable_cexp_neg_mul_sq (b := (1 / (4 * c) : ℂ)) (by simp; positivity)
  exact h.congr (ae_of_all _ fun ω => (gaussK_eq c ω).symm)

/-- `e^{-cu²} = (4πc)^{-1/2} ∫_ℝ e^{-ω²/(4c)} e^{iωu} dω`. -/
lemma heat_eq_gauss_integral {c : ℝ} (hc : 0 < c) (u : ℝ) :
    ((Real.exp (-c * u ^ 2) : ℝ) : ℂ) =
      (1 / ((Real.sqrt (4 * π * c) : ℝ) : ℂ)) * ∫ ω : ℝ, gaussKer c ω * cexp (I * ω * u) := by
  have hb : (0 : ℝ) < (1 / (4 * c) : ℂ).re := by simp; positivity
  have h := fourierIntegral_gaussian hb (u : ℂ)
  simp_rw [gaussK_eq]
  have hfun : (fun ω : ℝ => cexp (-(1 / (4 * c) : ℂ) * (ω : ℂ) ^ 2) * cexp (I * ω * u)) =
      fun ω : ℝ => cexp (I * (u : ℂ) * ω) * cexp (-(1 / (4 * c) : ℂ) * (ω : ℂ) ^ 2) := by
    funext ω; rw [mul_comm]; congr 2; ring
  rw [hfun, h]
  have hsq : ((π : ℂ) / (1 / (4 * c))) ^ (1 / 2 : ℂ) = ((Real.sqrt (4 * π * c) : ℝ) : ℂ) := by
    rw [show (π : ℂ) / (1 / (4 * c)) = (((4 * π * c : ℝ)) : ℂ) by push_cast; field_simp,
      Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    norm_num
  rw [hsq]
  have hne : ((Real.sqrt (4 * π * c) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [← mul_assoc, one_div, inv_mul_cancel₀ hne, one_mul, Complex.ofReal_exp]
  congr 1
  push_cast
  field_simp

/-- **The Gaussian representation**: `H_{-c}(z) = (4πc)^{-1/2} ∫_ℝ e^{-ω²/(4c)} H_0(z + ω) dω`. -/
theorem H_neg_eq_gauss {c : ℝ} (hc : 0 < c) (z : ℂ) :
    DBN.H (-c) z =
      (1 / ((Real.sqrt (4 * π * c) : ℝ) : ℂ)) * ∫ ω : ℝ, gaussKer c ω * DBN.H 0 (z + ω) := by
  set S : ℂ := 1 / ((Real.sqrt (4 * π * c) : ℝ) : ℂ) with hS
  have h1 : ∀ u : ℝ, heatIntegrand (-c) z u =
      S * ∫ ω : ℝ, gaussKer c ω * cexp (I * ω * u) * DBN.expIntegrand z u := by
    intro u
    rw [heatIntegrand, heat_eq_gauss_integral hc u, mul_assoc, ← integral_mul_const]
  have hcont : Continuous fun p : ℝ × ℝ =>
      gaussKer c p.2 * cexp (I * p.2 * p.1) * DBN.expIntegrand z p.1 := by
    unfold gaussKer
    fun_prop
  have hF : Integrable (fun p : ℝ × ℝ => gaussKer c p.2 * cexp (I * p.2 * p.1) * DBN.expIntegrand z p.1)
      (volume.prod volume) := by
    have hprod := (DBN.integrable_expIntegrand z).norm.mul_prod (integrable_gaussK hc).norm
    refine hprod.mono' hcont.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    rw [norm_mul, norm_mul, Complex.norm_exp]
    have : (I * (p.2 : ℂ) * (p.1 : ℂ)).re = 0 := by simp
    rw [this, Real.exp_zero, mul_one]
    exact le_of_eq (mul_comm _ _)
  have h2 : ∀ ω : ℝ, ∫ u : ℝ, gaussKer c ω * cexp (I * ω * u) * DBN.expIntegrand z u =
      2 * (gaussKer c ω * DBN.H 0 (z + ω)) := by
    intro ω
    rw [DBN.H_zero_eq_half_integral, show (2 : ℂ) * (gaussKer c ω * ((1 / 2 : ℂ) *
      ∫ u : ℝ, DBN.expIntegrand (z + ω) u)) = gaussKer c ω * ∫ u : ℝ, DBN.expIntegrand (z + ω) u by
      ring, ← integral_const_mul]
    congr 1
    funext u
    unfold DBN.expIntegrand
    rw [show (z + ω) * u * I = z * u * I + I * ω * u by ring, Complex.exp_add]
    ring
  rw [H_eq_half_integral (by linarith) z]
  simp_rw [h1]
  rw [integral_const_mul, integral_integral_swap hF]
  simp_rw [h2]
  rw [integral_const_mul]
  ring

/-! ### `H_0` is bounded on horizontal strips -/

/-- `stripBound B = ½ ∫ |Φ u| (e^{Bu} + e^{-Bu}) du`. -/
noncomputable def stripBound (B : ℝ) : ℝ :=
  (1 / 2) * ∫ u : ℝ, (‖DBN.expIntegrand (-(B : ℂ) * I) u‖ + ‖DBN.expIntegrand ((B : ℂ) * I) u‖)

lemma norm_expIntegrand_eq (z : ℂ) (u : ℝ) :
    ‖DBN.expIntegrand z u‖ = |DBN.Φ u| * Real.exp (-z.im * u) := by
  rw [DBN.expIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re, Complex.mul_im]

lemma norm_expIntegrand_le_of_abs_im_le {B : ℝ} {w : ℂ} (hw : |w.im| ≤ B) (u : ℝ) :
    ‖DBN.expIntegrand w u‖ ≤
      ‖DBN.expIntegrand (-(B : ℂ) * I) u‖ + ‖DBN.expIntegrand ((B : ℂ) * I) u‖ := by
  rw [norm_expIntegrand_eq, norm_expIntegrand_eq, norm_expIntegrand_eq]
  have h1 : (-(B : ℂ) * I).im = -B := by simp
  have h2 : ((B : ℂ) * I).im = B := by simp
  rw [h1, h2, neg_neg, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have := abs_le.mp hw
  rcases le_total 0 u with hu | hu
  · calc Real.exp (-w.im * u) ≤ Real.exp (B * u) :=
          Real.exp_le_exp.mpr (by nlinarith)
      _ ≤ _ := le_add_of_nonneg_right (Real.exp_pos _).le
  · calc Real.exp (-w.im * u) ≤ Real.exp (-B * u) :=
          Real.exp_le_exp.mpr (by nlinarith)
      _ ≤ _ := le_add_of_nonneg_left (Real.exp_pos _).le

theorem norm_H_zero_le {B : ℝ} {w : ℂ} (hw : |w.im| ≤ B) : ‖DBN.H 0 w‖ ≤ stripBound B := by
  rw [DBN.H_zero_eq_half_integral, norm_mul, stripBound]
  have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [this]
  gcongr
  refine (norm_integral_le_integral_norm _).trans ?_
  refine integral_mono (DBN.integrable_expIntegrand w).norm
    ((DBN.integrable_expIntegrand _).norm.add (DBN.integrable_expIntegrand _).norm) ?_
  intro u
  exact norm_expIntegrand_le_of_abs_im_le hw u

/-! ### Moving the Gaussian line vertically -/

/-- The entire function `w ↦ e^{-w²/(4c)} H_0(z + w)`. -/
noncomputable def shiftIntegrand (c : ℝ) (z : ℂ) (w : ℂ) : ℂ :=
  cexp (-w ^ 2 / (4 * c)) * DBN.H 0 (z + w)

lemma differentiable_shiftIntegrand (c : ℝ) (z : ℂ) : Differentiable ℂ (shiftIntegrand c z) := by
  unfold shiftIntegrand
  exact ((differentiable_id.pow 2).neg.div_const _).cexp.mul
    ((DBN.differentiable_H 0).comp (differentiable_id.const_add z))

lemma norm_cexp_neg_sq_div (c : ℝ) (x y : ℝ) :
    ‖cexp (-((x : ℂ) + y * I) ^ 2 / (4 * c))‖ = Real.exp ((y ^ 2 - x ^ 2) / (4 * c)) := by
  rw [Complex.norm_exp]
  congr 1
  have : (-((x : ℂ) + y * I) ^ 2 / (4 * c)) = ((((y ^ 2 - x ^ 2) / (4 * c) : ℝ)) : ℂ) +
      ((-(2 * x * y) / (4 * c) : ℝ) : ℂ) * I := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [this, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
    add_zero]

lemma norm_shiftIntegrand_le {c : ℝ} (z : ℂ) {B : ℝ} (hB : |z.im| ≤ B) (x y : ℝ) (hy : |y| ≤ B) :
    ‖shiftIntegrand c z (x + y * I)‖ ≤
      Real.exp ((y ^ 2 - x ^ 2) / (4 * c)) * stripBound (2 * B) := by
  rw [shiftIntegrand, norm_mul, norm_cexp_neg_sq_div]
  gcongr
  apply norm_H_zero_le
  rw [Complex.add_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  simp only [mul_one, mul_zero, add_zero, zero_add]
  calc |z.im + y| ≤ |z.im| + |y| := abs_add_le _ _
    _ ≤ B + B := add_le_add hB hy
    _ = 2 * B := by ring

lemma integrable_shiftIntegrand_line {c : ℝ} (hc : 0 < c) (z : ℂ) (β : ℝ) :
    Integrable fun x : ℝ => shiftIntegrand c z (x + β * I) := by
  set B := |z.im| + |β| with hB
  have hcont : Continuous fun x : ℝ => shiftIntegrand c z (x + β * I) :=
    (differentiable_shiftIntegrand c z).continuous.comp (by fun_prop)
  refine ((integrable_gaussK hc).norm.const_mul (Real.exp (β ^ 2 / (4 * c)) * stripBound (2 * B))).mono'
    hcont.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have h := norm_shiftIntegrand_le (c := c) z (B := B)
    (by rw [hB]; exact le_add_of_nonneg_right (abs_nonneg _)) x β
    (by rw [hB]; exact le_add_of_nonneg_left (abs_nonneg _))
  refine h.trans (le_of_eq ?_)
  rw [gaussKer, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    show (β ^ 2 - x ^ 2) / (4 * c) = β ^ 2 / (4 * c) + -x ^ 2 / (4 * c) by ring, Real.exp_add]
  ring

/-- **Cauchy**: the Gaussian line may be moved vertically. -/
theorem shift_line {c : ℝ} (hc : 0 < c) (z : ℂ) (β : ℝ) :
    ∫ x : ℝ, shiftIntegrand c z x = ∫ x : ℝ, shiftIntegrand c z (x + β * I) := by
  set B := |z.im| + |β| with hB
  set K := stripBound (2 * B) with hK
  have hK0 : 0 ≤ K := by
    rw [hK, stripBound]
    exact mul_nonneg (by norm_num) (integral_nonneg fun u => by positivity)
  -- the rectangle identity for each T
  have hrect : ∀ T : ℝ,
      (∫ x in (-T)..T, shiftIntegrand c z x) - (∫ x in (-T)..T, shiftIntegrand c z (x + β * I)) =
        I * (∫ y in (0 : ℝ)..β, shiftIntegrand c z (-T + y * I)) -
          I * (∫ y in (0 : ℝ)..β, shiftIntegrand c z (T + y * I)) := by
    intro T
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (shiftIntegrand c z)
      ⟨-T, 0⟩ ⟨T, β⟩ (differentiable_shiftIntegrand c z).differentiableOn
    simp only [Complex.ofReal_zero, zero_mul, add_zero, smul_eq_mul, Complex.ofReal_neg] at h
    linear_combination h
  -- the vertical sides tend to zero
  have hvert : ∀ T X : ℝ, X ^ 2 = T ^ 2 →
      ‖∫ y in (0 : ℝ)..β, shiftIntegrand c z (X + y * I)‖ ≤
        Real.exp ((β ^ 2 - T ^ 2) / (4 * c)) * K * |β| := by
    intro T X hX
    refine (intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_).trans
      (le_of_eq (by rw [sub_zero]))
    have hy' : |y| ≤ |β| := by
      rw [Set.uIoc, Set.mem_Ioc] at hy
      rw [abs_le]
      constructor
      · have : -|β| ≤ min 0 β := le_min (by linarith [abs_nonneg β]) (neg_abs_le β)
        linarith [hy.1]
      · have : max 0 β ≤ |β| := max_le (abs_nonneg β) (le_abs_self β)
        linarith [hy.2]
    have hyB : |y| ≤ B := le_trans hy' (by rw [hB]; exact le_add_of_nonneg_left (abs_nonneg _))
    have h := norm_shiftIntegrand_le (c := c) z (B := B)
      (by rw [hB]; exact le_add_of_nonneg_right (abs_nonneg _)) X y hyB
    refine h.trans ?_
    rw [hX]
    refine mul_le_mul_of_nonneg_right ?_ hK0
    refine Real.exp_le_exp.mpr (div_le_div_of_nonneg_right ?_ (by positivity))
    have := sq_le_sq.mpr hy'
    linarith
  have hexp : Tendsto (fun T : ℝ => Real.exp ((β ^ 2 - T ^ 2) / (4 * c)) * K * |β|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => (T ^ 2 - β ^ 2) / (4 * c)) atTop atTop := by
      refine Tendsto.atTop_div_const (by positivity) ?_
      exact tendsto_atTop_add_const_right _ _ (tendsto_pow_atTop two_ne_zero)
    have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    have h3 : Tendsto (fun T : ℝ => Real.exp ((β ^ 2 - T ^ 2) / (4 * c))) atTop (𝓝 0) := by
      refine h2.congr fun T => ?_
      simp only [Function.comp]
      congr 1
      ring
    simpa using (h3.mul_const K).mul_const |β|
  have hL : Tendsto (fun T : ℝ => (∫ x in (-T)..T, shiftIntegrand c z x) -
      ∫ x in (-T)..T, shiftIntegrand c z (x + β * I)) atTop
      (𝓝 ((∫ x : ℝ, shiftIntegrand c z x) - ∫ x : ℝ, shiftIntegrand c z (x + β * I))) := by
    have hi0 : Integrable fun x : ℝ => shiftIntegrand c z x := by
      have := integrable_shiftIntegrand_line hc z 0
      simpa using this
    exact (intervalIntegral_tendsto_integral hi0 tendsto_neg_atTop_atBot tendsto_id).sub
      (intervalIntegral_tendsto_integral (integrable_shiftIntegrand_line hc z β)
        tendsto_neg_atTop_atBot tendsto_id)
  have hR : Tendsto (fun T : ℝ => (∫ x in (-T)..T, shiftIntegrand c z x) -
      ∫ x in (-T)..T, shiftIntegrand c z (x + β * I)) atTop (𝓝 0) := by
    simp_rw [hrect]
    rw [show (0 : ℂ) = I * 0 - I * 0 by simp]
    refine Tendsto.sub (Tendsto.const_mul I ?_) (Tendsto.const_mul I ?_)
    · refine squeeze_zero_norm (fun T => ?_) hexp
      have := hvert T (-T) (neg_sq T)
      simpa using this
    · exact squeeze_zero_norm (fun T => hvert T T rfl) hexp
  have := tendsto_nhds_unique hL hR
  exact sub_eq_zero.mp this

/-- The Gaussian representation with the line moved to height `β`. -/
theorem H_neg_eq_gauss_shift {c : ℝ} (hc : 0 < c) (z : ℂ) (β : ℝ) :
    DBN.H (-c) z = (1 / ((Real.sqrt (4 * π * c) : ℝ) : ℂ)) *
      ∫ ω : ℝ, cexp (-((ω : ℂ) + β * I) ^ 2 / (4 * c)) * DBN.H 0 (z + ω + β * I) := by
  rw [H_neg_eq_gauss hc z]
  congr 1
  have h := shift_line hc z β
  unfold shiftIntegrand at h
  have e1 : (fun ω : ℝ => gaussKer c ω * DBN.H 0 (z + ω)) =
      fun x : ℝ => cexp (-(x : ℂ) ^ 2 / (4 * c)) * DBN.H 0 (z + x) := by
    funext ω; rw [gaussK_eq]; congr 2; ring
  have e2 : (fun ω : ℝ => cexp (-((ω : ℂ) + β * I) ^ 2 / (4 * c)) * DBN.H 0 (z + ω + β * I)) =
      fun x : ℝ => cexp (-((x : ℂ) + β * I) ^ 2 / (4 * c)) * DBN.H 0 (z + (x + β * I)) := by
    funext ω; rw [add_assoc]
  rw [e1, e2]
  exact h

/-! ### The Dirichlet expansion -/

/-- The island-normalised Gamma factor `γ(v) = (1/16) v (v-1) π^{-v/2} Γ(v/2)`:
`H_0(z) = ∑_{n ≥ 1} γ(s) n^{-s}` for `s = 1/2 + iz/2`, `Re s > 1` (`DBNStrip`). -/
noncomputable def γ (v : ℂ) : ℂ :=
  (1 / 16 : ℂ) * v * (v - 1) * (π : ℂ) ^ (-v / 2) * Complex.Gamma (v / 2)

theorem H_zero_eq_tsum {z : ℂ} (hz : z.im < -1) :
    DBN.H 0 z = ∑' n : ℕ+, γ (1 / 2 + I * z / 2) * (1 / (n : ℂ) ^ (1 / 2 + I * z / 2)) := by
  rw [DBN.H_zero_eq_half_integral, ← (DBN.hasSum_integral_expTerm hz).tsum_eq, ← tsum_mul_left]
  congr 1
  funext n
  rw [DBN.integral_expTerm hz n, γ]
  ring

lemma norm_γ_le {a : ℝ} (ha : 0 < a) (τ : ℝ) :
    ‖γ ((a : ℂ) + τ * I)‖ ≤
      (1 / 16) * (a + |τ|) * (a + |τ| + 1) * π ^ (-a / 2) * Real.Gamma (a / 2) := by
  have hv : ‖(a : ℂ) + τ * I‖ ≤ a + |τ| := by
    calc ‖(a : ℂ) + τ * I‖ ≤ ‖(a : ℂ)‖ + ‖(τ : ℂ) * I‖ := norm_add_le _ _
      _ = a + |τ| := by simp [abs_of_pos ha]
  have hv1 : ‖(a : ℂ) + τ * I - 1‖ ≤ a + |τ| + 1 := by
    calc ‖(a : ℂ) + τ * I - 1‖ ≤ ‖(a : ℂ) + τ * I‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ a + |τ| + 1 := by rw [norm_one]; gcongr
  have hπ : ‖(π : ℂ) ^ (-((a : ℂ) + τ * I) / 2)‖ = π ^ (-a / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    simp
  have hΓ : ‖Complex.Gamma (((a : ℂ) + τ * I) / 2)‖ ≤ Real.Gamma (a / 2) := by
    have hre : (((a : ℂ) + τ * I) / 2).re = a / 2 := by simp
    have := norm_Gamma_le_Gamma_re (v := ((a : ℂ) + τ * I) / 2) (by rw [hre]; positivity)
    rwa [hre] at this
  rw [γ, norm_mul, norm_mul, norm_mul, norm_mul, hπ]
  have h16 : ‖(1 / 16 : ℂ)‖ = 1 / 16 := by norm_num
  rw [h16]
  gcongr

/-- Dobner's `B_n(s)`: the `n`-th term of the Gaussian-convolved Dirichlet expansion, on the line
`Re v = a`. -/
noncomputable def B (c a : ℝ) (n : ℕ+) (s : ℂ) : ℂ :=
  (1 / ((Real.sqrt (π * c) : ℝ) : ℂ)) *
    ∫ τ : ℝ, γ ((a : ℂ) + τ * I) * (1 / (n : ℂ) ^ ((a : ℂ) + τ * I)) *
      cexp ((((a : ℂ) + τ * I) - s) ^ 2 / c)

/-- The integrand of `B`. -/
noncomputable def BIntegrand (c a : ℝ) (n : ℕ+) (s : ℂ) (τ : ℝ) : ℂ :=
  γ ((a : ℂ) + τ * I) * (1 / (n : ℂ) ^ ((a : ℂ) + τ * I)) * cexp ((((a : ℂ) + τ * I) - s) ^ 2 / c)

lemma norm_BIntegrand_le (c : ℝ) {a : ℝ} (ha : 0 < a) (n : ℕ+) (s : ℂ) (τ : ℝ) :
    ‖BIntegrand c a n s τ‖ ≤
      ((1 / 16) * (a + |τ|) * (a + |τ| + 1) * π ^ (-a / 2) * Real.Gamma (a / 2)) *
        (n : ℝ) ^ (-a) * Real.exp (((a - s.re) ^ 2 - (τ - s.im) ^ 2) / c) := by
  rw [BIntegrand, norm_mul, norm_mul]
  have hn : ‖(1 / (n : ℂ) ^ ((a : ℂ) + τ * I))‖ = (n : ℝ) ^ (-a) := by
    rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos n.pos, Real.rpow_neg (by positivity),
      one_div]
    congr 2
    simp
  have he : ‖cexp ((((a : ℂ) + τ * I) - s) ^ 2 / c)‖ =
      Real.exp (((a - s.re) ^ 2 - (τ - s.im) ^ 2) / c) := by
    rw [Complex.norm_exp]
    congr 1
    have : (((a : ℂ) + τ * I) - s) ^ 2 / c =
        ((((a - s.re) ^ 2 - (τ - s.im) ^ 2) / c : ℝ) : ℂ) +
          ((2 * (a - s.re) * (τ - s.im) / c : ℝ) : ℂ) * I := by
      have hs : s = (s.re : ℂ) + s.im * I := (Complex.re_add_im s).symm
      conv_lhs => rw [hs]
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [this, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
      add_zero]
  rw [hn, he]
  gcongr
  exact norm_γ_le ha τ

lemma continuous_BIntegrand (c : ℝ) {a : ℝ} (ha : 0 < a) (n : ℕ+) (s : ℂ) :
    Continuous (BIntegrand c a n s) := by
  have hline : Continuous fun τ : ℝ => (a : ℂ) + τ * I := by fun_prop
  have hΓ : Continuous fun τ : ℝ => Complex.Gamma (((a : ℂ) + τ * I) / 2) := by
    refine continuous_iff_continuousAt.mpr fun τ => ?_
    refine (Complex.differentiableAt_Gamma _ fun m => ?_).continuousAt.comp (by fun_prop)
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hπ : Continuous fun τ : ℝ => (π : ℂ) ^ (-((a : ℂ) + τ * I) / 2) :=
    (by fun_prop : Continuous fun τ : ℝ => -((a : ℂ) + τ * I) / 2).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'))
  have hn : Continuous fun τ : ℝ => 1 / (n : ℂ) ^ ((a : ℂ) + τ * I) := by
    refine continuous_const.div (hline.const_cpow (Or.inl ?_)) fun τ => ?_
    · exact_mod_cast n.ne_zero
    · rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
      left
      exact_mod_cast n.ne_zero
  unfold BIntegrand γ
  fun_prop

/-- The majorant of `‖BIntegrand c a n s τ‖` without the `n^{-a}` factor. -/
noncomputable def majorant (c a : ℝ) (s : ℂ) (τ : ℝ) : ℝ :=
  ((1 / 16) * (a + |τ|) * (a + |τ| + 1) * π ^ (-a / 2) * Real.Gamma (a / 2)) *
    Real.exp (((a - s.re) ^ 2 - (τ - s.im) ^ 2) / c)

lemma majorant_nonneg {a : ℝ} (ha : 0 < a) (c : ℝ) (s : ℂ) (τ : ℝ) : 0 ≤ majorant c a s τ := by
  have hΓ : 0 ≤ Real.Gamma (a / 2) := Real.Gamma_nonneg_of_nonneg (by positivity)
  unfold majorant
  positivity

lemma continuous_majorant (c a : ℝ) (s : ℂ) : Continuous (majorant c a s) := by
  unfold majorant
  fun_prop

/-- The Gaussian-times-polynomial majorant is integrable. -/
lemma integrable_majorant {c : ℝ} (hc : 0 < c) {a : ℝ} (ha : 0 < a) (s : ℂ) :
    Integrable (majorant c a s) := by
  set A : ℝ := |a| + |s.im| + 1 with hA
  have hΓ : 0 ≤ Real.Gamma (a / 2) := Real.Gamma_nonneg_of_nonneg (by positivity)
  set K : ℝ := (1 / 16) * π ^ (-a / 2) * Real.Gamma (a / 2) * Real.exp ((a - s.re) ^ 2 / c) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hf : Integrable fun u : ℝ => K * ((2 * A ^ 2 + 2 * u ^ 2) * Real.exp (-(1 / c) * u ^ 2)) := by
    refine Integrable.const_mul ?_ K
    have h1 := (integrable_exp_neg_mul_sq (b := 1 / c) (by positivity)).const_mul (2 * A ^ 2)
    have h2 := (integrable_rpow_mul_exp_neg_mul_sq (b := 1 / c) (by positivity)
      (s := 2) (by norm_num)).const_mul 2
    refine (h1.add h2).congr (ae_of_all _ fun u => ?_)
    simp only [Pi.add_apply, Real.rpow_two]
    ring
  have hf' := hf.comp_sub_right s.im
  refine hf'.mono' (continuous_majorant c a s).aestronglyMeasurable (ae_of_all _ fun τ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (majorant_nonneg ha c s τ)]
  set u : ℝ := τ - s.im with hu
  have h1 : a + |τ| ≤ A + |u| := by
    have : |τ| ≤ |u| + |s.im| := by
      rw [hu]
      calc |τ| = |(τ - s.im) + s.im| := by ring_nf
        _ ≤ |τ - s.im| + |s.im| := abs_add_le _ _
    rw [hA]
    linarith [le_abs_self a]
  have h2 : a + |τ| + 1 ≤ A + |u| := by
    have : |τ| ≤ |u| + |s.im| := by
      rw [hu]
      calc |τ| = |(τ - s.im) + s.im| := by ring_nf
        _ ≤ |τ - s.im| + |s.im| := abs_add_le _ _
    rw [hA]
    linarith [le_abs_self a]
  have hpoly : (a + |τ|) * (a + |τ| + 1) ≤ 2 * A ^ 2 + 2 * u ^ 2 := by
    calc (a + |τ|) * (a + |τ| + 1) ≤ (A + |u|) * (A + |u|) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (A + |u|) ^ 2 := by ring
      _ ≤ 2 * A ^ 2 + 2 * u ^ 2 := by nlinarith [sq_nonneg (A - |u|), sq_abs u]
  have hexp : Real.exp (((a - s.re) ^ 2 - (τ - s.im) ^ 2) / c) =
      Real.exp ((a - s.re) ^ 2 / c) * Real.exp (-(1 / c) * u ^ 2) := by
    rw [← Real.exp_add, hu]
    congr 1
    field_simp
    ring
  unfold majorant
  rw [hexp, hK]
  have hπ : 0 ≤ π ^ (-a / 2) := by positivity
  have hE : 0 ≤ Real.exp (-(1 / c) * u ^ 2) := (Real.exp_pos _).le
  have hE2 : 0 ≤ Real.exp ((a - s.re) ^ 2 / c) := (Real.exp_pos _).le
  calc (1 / 16) * (a + |τ|) * (a + |τ| + 1) * π ^ (-a / 2) * Real.Gamma (a / 2) *
        (Real.exp ((a - s.re) ^ 2 / c) * Real.exp (-(1 / c) * u ^ 2))
      = ((1 / 16) * π ^ (-a / 2) * Real.Gamma (a / 2) * Real.exp ((a - s.re) ^ 2 / c) *
          Real.exp (-(1 / c) * u ^ 2)) * ((a + |τ|) * (a + |τ| + 1)) := by ring
    _ ≤ ((1 / 16) * π ^ (-a / 2) * Real.Gamma (a / 2) * Real.exp ((a - s.re) ^ 2 / c) *
          Real.exp (-(1 / c) * u ^ 2)) * (2 * A ^ 2 + 2 * u ^ 2) :=
        mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = _ := by ring

lemma integrable_BIntegrand {c : ℝ} (hc : 0 < c) {a : ℝ} (ha : 0 < a) (n : ℕ+) (s : ℂ) :
    Integrable (BIntegrand c a n s) := by
  refine ((integrable_majorant hc ha s).const_mul ((n : ℝ) ^ (-a))).mono'
    (continuous_BIntegrand c ha n s).aestronglyMeasurable (ae_of_all _ fun τ => ?_)
  have := norm_BIntegrand_le c ha n s τ
  unfold majorant
  linarith [this]

lemma summable_integral_norm_BIntegrand {c : ℝ} (hc : 0 < c) {a : ℝ} (ha : 1 < a) (s : ℂ) :
    Summable fun n : ℕ+ => ∫ τ : ℝ, ‖BIntegrand c a n s τ‖ := by
  have ha0 : 0 < a := by linarith
  have hsum : Summable (fun n : ℕ+ => (n : ℝ) ^ (-a)) :=
    (summable_pnat_iff_summable_nat (f := fun n : ℕ => (n : ℝ) ^ (-a))).mpr
      (Real.summable_nat_rpow.mpr (by linarith))
  refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun τ => norm_nonneg _) (fun n => ?_)
    (hsum.mul_right (∫ τ : ℝ, majorant c a s τ))
  rw [← MeasureTheory.integral_const_mul]
  refine integral_mono (integrable_BIntegrand hc ha0 n s).norm
    ((integrable_majorant hc ha0 s).const_mul _) fun τ => ?_
  have := norm_BIntegrand_le c ha0 n s τ
  unfold majorant
  linarith [this]

lemma integral_comp_half_add (g : ℝ → ℂ) (y : ℝ) :
    ∫ ω : ℝ, g (y + ω / 2) = 2 * ∫ τ : ℝ, g τ := by
  have h := MeasureTheory.Measure.integral_comp_mul_left (fun ω : ℝ => g (y + ω / 2)) 2
  simp only [mul_div_cancel_left₀ _ (two_ne_zero' ℝ)] at h
  rw [integral_add_left_eq_self g y, Complex.real_smul, abs_inv, abs_two] at h
  rw [h]
  push_cast
  ring

/-- **Dobner's (9) on the dbn island**: for `c > 0`, `a > 1` and every `s`,
`H_{-c}(-i(2s-1)) = ∑_{n ≥ 1} B_n(s)`. -/
theorem xi_eq_tsum_B {c : ℝ} (hc : 0 < c) {a : ℝ} (ha : 1 < a) (s : ℂ) :
    DBN.H (-c) (-I * (2 * s - 1)) = ∑' n : ℕ+, B c a n s := by
  have ha0 : 0 < a := by linarith
  set z : ℂ := -I * (2 * s - 1) with hz
  set β : ℝ := 2 * (s.re - a) with hβ
  have hzim : z.im = 1 - 2 * s.re := by
    rw [hz]
    simp [Complex.mul_im, Complex.sub_im]
    try ring
  have hsω : ∀ ω : ℝ, (1 / 2 : ℂ) + I * (z + ω + β * I) / 2 =
      (a : ℂ) + ((s.im + ω / 2 : ℝ) : ℂ) * I := by
    intro ω
    rw [hz, hβ]
    apply Complex.ext <;> simp <;> try ring
  have him : ∀ ω : ℝ, (z + ω + β * I).im < -1 := by
    intro ω
    simp [hzim, hβ]
    linarith
  have hG : ∀ ω : ℝ, cexp (-((ω : ℂ) + β * I) ^ 2 / (4 * c)) * DBN.H 0 (z + ω + β * I) =
      ∑' n : ℕ+, BIntegrand c a n s (s.im + ω / 2) := by
    intro ω
    rw [H_zero_eq_tsum (him ω), hsω ω, ← tsum_mul_left]
    congr 1
    funext n
    rw [BIntegrand]
    have : cexp (-((ω : ℂ) + β * I) ^ 2 / (4 * c)) =
        cexp (((((a : ℂ) + ((s.im + ω / 2 : ℝ) : ℂ) * I)) - s) ^ 2 / c) := by
      congr 1
      set x : ℝ := s.re with hx
      set y : ℝ := s.im with hy
      have hs : s = (x : ℂ) + y * I := by rw [hx, hy]; exact (Complex.re_add_im s).symm
      conv_rhs => rw [hs]
      rw [hβ]
      push_cast
      field_simp
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [this]
    ring
  rw [H_neg_eq_gauss_shift hc z β]
  simp_rw [hG]
  have hsub := integral_comp_half_add (fun τ => ∑' n : ℕ+, BIntegrand c a n s τ) s.im
  rw [hsub, ← (hasSum_integral_of_summable_integral_norm (integrable_BIntegrand hc ha0 · s)
    (summable_integral_norm_BIntegrand hc ha s)).tsum_eq, ← tsum_mul_left, ← tsum_mul_left]
  congr 1
  funext n
  rw [B]
  have h4 : Real.sqrt (4 * π * c) = 2 * Real.sqrt (π * c) := by
    rw [show 4 * π * c = 2 ^ 2 * (π * c) by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [h4]
  push_cast
  have : ((Real.sqrt (π * c) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp
  congr 1
  funext τ
  rw [BIntegrand]
  ring

end DBNGaussConv
