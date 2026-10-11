/-
  DBNGammaVertical -- exponential decay of the complex Gamma function on vertical strips.

  Companion to DBNStirling (Newman / Lambda >= 0 programme, NEWMAN_LAMBDA_NONNEG_SCOPING_2026-10-10.md).
  From Stirling's formula with remainder, `Gamma z = exp (L z)` with
      (L z).re = (Re z - 1/2) log ‖z‖ - Im z * arg z - Re z + (1/2) log (2 pi) + (R z).re,
  and the elementary bounds `arg z >= pi/2 - Re z / Im z` (Im z >= 1, Re z > 0), `‖z‖ <= (1 + sigma_1)(1 + Im z)`,
  `(R z).re <= 1/4`, one gets for `sigma_0 <= Re z <= sigma_1` and `Im z >= 1`
      ‖Gamma z‖ <= C_1 (1 + Im z)^sigma_1 exp (-(pi/2) Im z),
  with the explicit constant `C_1 = exp (sigma_1 log (1 + sigma_1) + sigma_1 + (1/2) log (2 pi) + 1/4)`.
  The lower half-plane follows by conjugation (`Gamma_conj`) and the band `|Im z| <= 1` by compactness.

  Statement.  For `0 < sigma_0 <= sigma_1` there is `C >= 0` with
      ‖Gamma w‖ <= C (1 + |Im w|)^sigma_1 exp (-(pi/2) |Im w|)     whenever sigma_0 <= Re w <= sigma_1.

  Nothing here is RH.  conjecture1_proved = False.
-/
import Mathlib
import DBNStirling

open Complex Set ComplexConjugate

namespace DBNStirling

/-! ### Elementary bounds on `arctan` and `arg` -/

/-- `pi/2 - 1/x <= arctan x` for `x > 0`. -/
lemma pi_div_two_sub_inv_le_arctan {x : ℝ} (hx : 0 < x) :
    Real.pi / 2 - x⁻¹ ≤ Real.arctan x := by
  have h1 : Real.arctan x⁻¹ = Real.pi / 2 - Real.arctan x := Real.arctan_inv_of_pos hx
  have h2 : Real.arctan x⁻¹ ≤ x⁻¹ := by
    have h0 : 0 ≤ Real.arctan x⁻¹ := Real.arctan_nonneg.mpr (inv_nonneg.mpr hx.le)
    calc Real.arctan x⁻¹ ≤ Real.tan (Real.arctan x⁻¹) :=
          Real.le_tan h0 (Real.arctan_lt_pi_div_two _)
      _ = x⁻¹ := Real.tan_arctan _
  linarith

/-- For `Re z > 0`, `arg z = arctan (Im z / Re z)`. -/
lemma arg_eq_arctan_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    arg z = Real.arctan (z.im / z.re) := by
  have h := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  rw [abs_lt] at h
  rw [← tan_arg, Real.arctan_tan h.1 h.2]

/-- `Im z * arg z >= (pi/2) Im z - Re z` when `Re z > 0` and `Im z >= 1`. -/
lemma im_mul_arg_ge {z : ℂ} (hz : 0 < z.re) (hi : 1 ≤ z.im) :
    Real.pi / 2 * z.im - z.re ≤ z.im * arg z := by
  rw [arg_eq_arctan_of_re_pos hz]
  have hpos : 0 < z.im := by linarith
  have hx : 0 < z.im / z.re := div_pos hpos hz
  have h := pi_div_two_sub_inv_le_arctan hx
  have h' : z.im * (Real.pi / 2 - (z.im / z.re)⁻¹) ≤ z.im * Real.arctan (z.im / z.re) :=
    mul_le_mul_of_nonneg_left h hpos.le
  have hne : z.im ≠ 0 := hpos.ne'
  have heq : z.im * (Real.pi / 2 - (z.im / z.re)⁻¹) = Real.pi / 2 * z.im - z.re := by
    rw [inv_div]; field_simp
  linarith

/-! ### The real part of `L` -/

/-- The real part of Stirling's `L`. -/
lemma re_L (z : ℂ) :
    (L z).re = (z.re - 1 / 2) * Real.log ‖z‖ - z.im * arg z - z.re
      + (1 / 2) * Real.log (2 * Real.pi) + (R z).re := by
  simp only [L, add_re, sub_re, mul_re, log_re, log_im, sub_im, ofReal_re, ofReal_im]
  norm_num

/-- The explicit constant for the decay bound on `Im z >= 1`. -/
noncomputable def gammaVertC (σ₁ : ℝ) : ℝ :=
  Real.exp (σ₁ * Real.log (1 + σ₁) + σ₁ + (1 / 2) * Real.log (2 * Real.pi) + 1 / 4)

lemma gammaVertC_pos (σ₁ : ℝ) : 0 < gammaVertC σ₁ := Real.exp_pos _

/-- Upper bound on `(L z).re` for `0 < Re z <= sigma_1` and `Im z >= 1`. -/
lemma re_L_le {σ₁ : ℝ} {z : ℂ} (hz : 0 < z.re) (h1 : z.re ≤ σ₁) (hi : 1 ≤ z.im) :
    (L z).re ≤ σ₁ * Real.log (1 + σ₁) + σ₁ + (1 / 2) * Real.log (2 * Real.pi) + 1 / 4
      + σ₁ * Real.log (1 + z.im) - Real.pi / 2 * z.im := by
  have hσ₁ : 0 < σ₁ := lt_of_lt_of_le hz h1
  have hipos : 0 < z.im := by linarith
  have hnz : 1 ≤ ‖z‖ := by
    have : 1 ≤ |z.im| := by rw [abs_of_pos hipos]; exact hi
    exact this.trans (abs_im_le_norm z)
  have hnorm_le : ‖z‖ ≤ (1 + σ₁) * (1 + z.im) := by
    have := norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hz, abs_of_pos hipos] at this
    nlinarith
  have hlogpos : 0 ≤ Real.log ‖z‖ := Real.log_nonneg hnz
  have hlog_le : Real.log ‖z‖ ≤ Real.log (1 + σ₁) + Real.log (1 + z.im) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by linarith) hnorm_le
  have hlog1 : 0 ≤ Real.log (1 + σ₁) := Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log (1 + z.im) := Real.log_nonneg (by linarith)
  have hT1 : (z.re - 1 / 2) * Real.log ‖z‖ ≤ σ₁ * (Real.log (1 + σ₁) + Real.log (1 + z.im)) := by
    rcases le_or_gt 0 (z.re - 1 / 2) with h | h
    · exact mul_le_mul (by linarith) hlog_le hlogpos hσ₁.le
    · have hA : (z.re - 1 / 2) * Real.log ‖z‖ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h.le hlogpos
      have hB : 0 ≤ σ₁ * (Real.log (1 + σ₁) + Real.log (1 + z.im)) :=
        mul_nonneg hσ₁.le (add_nonneg hlog1 hlog2)
      linarith
  have hT2 := im_mul_arg_ge hz hi
  have hT3 : (R z).re ≤ 1 / 4 := by
    calc (R z).re ≤ ‖R z‖ := re_le_norm _
      _ ≤ 1 / (4 * ‖z‖) := norm_R_le hz
      _ ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  rw [re_L]
  linarith

/-! ### The decay bound in the three regions -/

/-- Decay of `Gamma` for `0 < Re z <= sigma_1`, `Im z >= 1`, with the explicit constant. -/
lemma norm_Gamma_le_of_one_le_im {σ₁ : ℝ} {z : ℂ} (hz : 0 < z.re) (h1 : z.re ≤ σ₁)
    (hi : 1 ≤ z.im) :
    ‖Gamma z‖ ≤ gammaVertC σ₁ * (1 + z.im) ^ σ₁ * Real.exp (-(Real.pi / 2) * z.im) := by
  rw [Gamma_eq_exp_L hz, norm_exp, gammaVertC, Real.rpow_def_of_pos (by linarith),
    ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := re_L_le hz h1 hi
  linarith

/-- Decay of `Gamma` for `0 < Re z <= sigma_1`, `Im z <= -1`, by conjugation. -/
lemma norm_Gamma_le_of_im_le_neg_one {σ₁ : ℝ} {z : ℂ} (hz : 0 < z.re) (h1 : z.re ≤ σ₁)
    (hi : z.im ≤ -1) :
    ‖Gamma z‖ ≤ gammaVertC σ₁ * (1 + |z.im|) ^ σ₁ * Real.exp (-(Real.pi / 2) * |z.im|) := by
  have hc : 0 < (conj z).re := by rwa [conj_re]
  have hc1 : (conj z).re ≤ σ₁ := by rwa [conj_re]
  have hci : 1 ≤ (conj z).im := by rw [conj_im]; linarith
  have := norm_Gamma_le_of_one_le_im hc hc1 hci
  rw [Gamma_conj, norm_conj, conj_im] at this
  rwa [abs_of_neg (by linarith)]

/-- `Gamma` is bounded on the compact band `sigma_0 <= Re z <= sigma_1`, `|Im z| <= 1`. -/
lemma norm_Gamma_le_of_abs_im_le_one {σ₀ σ₁ : ℝ} (h0 : 0 < σ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, σ₀ ≤ z.re → z.re ≤ σ₁ → |z.im| ≤ 1 → ‖Gamma z‖ ≤ C := by
  have hK : IsCompact (Icc σ₀ σ₁ ×ℂ Icc (-1) 1) := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn Gamma (Icc σ₀ σ₁ ×ℂ Icc (-1) 1) := by
    intro z hz
    rw [mem_reProdIm] at hz
    apply ContinuousAt.continuousWithinAt
    apply (differentiableAt_Gamma z ?_).continuousAt
    intro m hm
    have hre : z.re = -(m : ℝ) := by rw [hm, neg_re, natCast_re]
    have hpos : 0 < z.re := lt_of_lt_of_le h0 hz.1.1
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun z hz0 hz1 hzi => ?_⟩
  refine (hC z ?_).trans (le_max_left _ _)
  rw [mem_reProdIm]
  exact ⟨⟨hz0, hz1⟩, abs_le.mp hzi⟩

/-- Exponential decay of `Γ` on vertical strips of the right half-plane. -/
theorem norm_Gamma_le_vertical {σ₀ σ₁ : ℝ} (h0 : 0 < σ₀) (h01 : σ₀ ≤ σ₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, σ₀ ≤ w.re → w.re ≤ σ₁ →
      ‖Complex.Gamma w‖ ≤ C * (1 + |w.im|) ^ σ₁ * Real.exp (-(Real.pi / 2) * |w.im|) := by
  obtain ⟨C₂, hC₂0, hC₂⟩ := norm_Gamma_le_of_abs_im_le_one (σ₁ := σ₁) h0
  have hσ₁ : 0 ≤ σ₁ := by linarith
  have hC₁ := gammaVertC_pos σ₁
  refine ⟨gammaVertC σ₁ + C₂ * Real.exp (Real.pi / 2), by positivity, fun w hw0 hw1 => ?_⟩
  have hw : 0 < w.re := lt_of_lt_of_le h0 hw0
  have hX1 : 1 ≤ (1 + |w.im|) ^ σ₁ := Real.one_le_rpow (by linarith [abs_nonneg w.im]) hσ₁
  have hXpos : 0 ≤ (1 + |w.im|) ^ σ₁ * Real.exp (-(Real.pi / 2) * |w.im|) := by positivity
  rcases le_or_gt 1 |w.im| with h | h
  · have hmain : ‖Gamma w‖ ≤
        gammaVertC σ₁ * (1 + |w.im|) ^ σ₁ * Real.exp (-(Real.pi / 2) * |w.im|) := by
      rcases le_or_gt 0 w.im with hpos | hneg
      · rw [abs_of_nonneg hpos] at h ⊢
        exact norm_Gamma_le_of_one_le_im hw hw1 h
      · exact norm_Gamma_le_of_im_le_neg_one hw hw1
          (by rw [abs_of_neg hneg] at h; linarith)
    calc ‖Gamma w‖ ≤ gammaVertC σ₁ * (1 + |w.im|) ^ σ₁ * Real.exp (-(Real.pi / 2) * |w.im|) := hmain
      _ ≤ (gammaVertC σ₁ + C₂ * Real.exp (Real.pi / 2)) * (1 + |w.im|) ^ σ₁
            * Real.exp (-(Real.pi / 2) * |w.im|) := by
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hXpos
  · have hb := hC₂ w hw0 hw1 h.le
    have hexp : 1 ≤ Real.exp (Real.pi / 2) * Real.exp (-(Real.pi / 2) * |w.im|) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith [Real.pi_pos, abs_nonneg w.im]
    calc ‖Gamma w‖ ≤ C₂ := hb
      _ = C₂ * 1 * 1 := by ring
      _ ≤ C₂ * (Real.exp (Real.pi / 2) * Real.exp (-(Real.pi / 2) * |w.im|)) * (1 + |w.im|) ^ σ₁ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hexp hC₂0) hX1 zero_le_one (by positivity)
      _ = (C₂ * Real.exp (Real.pi / 2)) * (1 + |w.im|) ^ σ₁ * Real.exp (-(Real.pi / 2) * |w.im|) := by ring
      _ ≤ (gammaVertC σ₁ + C₂ * Real.exp (Real.pi / 2)) * (1 + |w.im|) ^ σ₁
            * Real.exp (-(Real.pi / 2) * |w.im|) := by
        have h := mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left hC₁.le :
            C₂ * Real.exp (Real.pi / 2) ≤ gammaVertC σ₁ + C₂ * Real.exp (Real.pi / 2)) hXpos
        simpa only [mul_assoc] using h

end DBNStirling
