/-
  DBNSaddleBounds -- the pointwise estimates behind Dobner's Theorem 4.

  Step 5b of the Lambda >= 0 (Newman's conjecture) formalization; see
  NEWMAN_LAMBDA_NONNEG_SCOPING_2026-10-10.md section 6.  With the notation of `DBNSaddleAlg`
  (`K = ρ(δ) exp(Q(δ))`, `P(δ) = ‖δ‖² + ‖δ‖ + 1`):

  * near field (`‖δ‖ ≤ ‖b‖/2`, `Re b ≥ 1`, `‖b‖ ≥ 2`, `Im b > 0`, `Im (b+δ) > 0`, `Re δ ≥ 0`):
        ‖K − 1‖ ≤ 8 P(δ)/‖b‖ · exp(2 P(δ)/‖b‖),
    from `Log((b+δ)/2) = Log(b/2) + Log(1 + δ/b)` (no branch jump: both arguments are in the open
    upper half-plane and `|Im Log(1+u)| ≤ 3/4`), `Q = (b/2)(Log(1+u) − u) + ((δ−1)/2) Log(1+u) + ΔR`
    with `u = δ/b`, Mathlib's `Log(1+u)` bounds and `DBNStirling.norm_R_le`;
  * global (`Re b ≥ 1`, `‖b‖ ≥ 2`, `Re δ ≥ 0`):
        ‖K‖ ≤ 2 (‖b‖ + ‖δ‖ + 1)²/‖b‖² · exp((Re b + Re δ − 1) ‖δ‖/(2‖b‖) + π (|Im b| + |Im δ|) + 1).

  Nothing here is RH.  conjecture1_proved = False.
-/
import Mathlib
import DBNSaddleAlg

open Complex Filter Topology MeasureTheory Set
open scoped Real

namespace DBNSaddle

open DBNGaussConv DBNStirling

/-! ### `‖exp Q − 1‖ ≤ ‖Q‖ e^{‖Q‖}` -/

theorem norm_exp_sub_one_le_mul_exp (Q : ℂ) : ‖cexp Q - 1‖ ≤ ‖Q‖ * Real.exp ‖Q‖ := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => cexp (t * Q)) (Q * cexp (t * Q)) t := by
    intro t _
    have h := ((hasDerivAt_id (t : ℂ)).mul_const Q).cexp
    have h2 := h.comp_ofReal
    simpa [mul_comm] using h2
  have hint : IntervalIntegrable (fun t : ℝ => Q * cexp (t * Q)) volume 0 1 :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, Complex.exp_zero] at hFTC
  rw [← hFTC]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := ‖Q‖ * Real.exp ‖Q‖)
    fun t ht => ?_).trans (le_of_eq ?_)
  · rw [uIoc_of_le zero_le_one] at ht
    rw [norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    calc ((t : ℂ) * Q).re ≤ ‖(t : ℂ) * Q‖ := Complex.re_le_norm _
      _ = t * ‖Q‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
      _ ≤ 1 * ‖Q‖ := by gcongr; exact ht.2
      _ = ‖Q‖ := one_mul _
  · simp

/-! ### The branch-free logarithm split -/

theorem log_half_add_eq {b δ : ℂ} (hb : 0 < b.im) (hbδ : 0 < (b + δ).im) (hδ : ‖δ‖ ≤ ‖b‖ / 2) :
    log ((b + δ) / 2) = log (b / 2) + log (1 + δ / b) := by
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  have hu : ‖δ / b‖ ≤ 1 / 2 := by rw [norm_div, div_le_iff₀ hbpos]; linarith
  have hu1 : (1 : ℂ) + δ / b ≠ 0 := by
    intro h
    have h1 : δ / b = -1 := by linear_combination h
    have : ‖δ / b‖ = 1 := by rw [h1]; simp
    linarith
  have hbδ0 : b + δ ≠ 0 := fun h => by simp [h] at hbδ
  have hexp : cexp (log ((b + δ) / 2)) = cexp (log (b / 2) + log (1 + δ / b)) := by
    rw [Complex.exp_add, Complex.exp_log (div_ne_zero hbδ0 two_ne_zero),
      Complex.exp_log (div_ne_zero hb0 two_ne_zero), Complex.exp_log hu1]
    field_simp
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have hbδ' : 0 < b.im + δ.im := by simpa using hbδ
  have him : arg ((b + δ) / 2) = arg (b / 2) + arg (1 + δ / b) + n * (2 * π) := by
    have := congrArg Complex.im hn
    simp only [Complex.add_im, Complex.log_im, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im] at this
    rw [this]
    ring
  have h1 : 0 ≤ arg ((b + δ) / 2) := Complex.arg_nonneg_iff.mpr (by simp; linarith)
  have h2 : arg ((b + δ) / 2) < π := Complex.arg_lt_pi_iff.mpr (Or.inr (by simp; linarith))
  have h3 : 0 ≤ arg (b / 2) := Complex.arg_nonneg_iff.mpr (by simp; linarith)
  have h4 : arg (b / 2) < π := Complex.arg_lt_pi_iff.mpr (Or.inr (by simp; linarith))
  have h5 : |arg (1 + δ / b)| ≤ 3 / 4 := by
    rw [← Complex.log_im]
    calc |(log (1 + δ / b)).im| ≤ ‖log (1 + δ / b)‖ := Complex.abs_im_le_norm _
      _ ≤ 3 / 2 * ‖δ / b‖ := Complex.norm_log_one_add_half_le_self hu
      _ ≤ 3 / 4 := by linarith
  have hn0 : n = 0 := by
    have hpi := Real.pi_gt_three
    have h6 := abs_le.mp h5
    have key : (n : ℝ) * (2 * π) = arg ((b + δ) / 2) - arg (b / 2) - arg (1 + δ / b) := by
      linarith [him]
    have h7 : |(n : ℝ) * (2 * π)| < 2 * π := by
      rw [key, abs_lt]
      constructor <;> linarith
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at h7
    have h8 : |(n : ℝ)| < 1 := (mul_lt_iff_lt_one_left (by positivity)).mp h7
    exact_mod_cast Int.abs_lt_one_iff.mp (by exact_mod_cast h8)
  rw [hn0] at hn
  simpa using hn

/-! ### The near-field estimate -/

/-- `P(δ) = ‖δ‖² + ‖δ‖ + 1`. -/
noncomputable def P (δ : ℂ) : ℝ := ‖δ‖ ^ 2 + ‖δ‖ + 1

lemma P_pos (δ : ℂ) : 0 < P δ := by unfold P; positivity

lemma norm_le_P (δ : ℂ) : ‖δ‖ ≤ P δ := by unfold P; nlinarith [norm_nonneg δ]

lemma sq_norm_le_P (δ : ℂ) : ‖δ‖ ^ 2 ≤ P δ := by unfold P; nlinarith [norm_nonneg δ]

theorem Q_eq_near {b δ : ℂ} (hb : 0 < b.im) (hbδ : 0 < (b + δ).im) (hδ : ‖δ‖ ≤ ‖b‖ / 2) :
    Q b δ = (b / 2) * (log (1 + δ / b) - δ / b) + ((δ - 1) / 2) * log (1 + δ / b) +
      (R ((b + δ) / 2) - R (b / 2)) := by
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  rw [Q, L, L, log_half_add_eq hb hbδ hδ]
  field_simp
  ring

theorem norm_Q_le_near {b δ : ℂ} (hb1 : 1 ≤ b.re) (hbn : 2 ≤ ‖b‖) (hb : 0 < b.im) (hδre : 0 ≤ δ.re)
    (hbδ : 0 < (b + δ).im) (hδ : ‖δ‖ ≤ ‖b‖ / 2) :
    ‖Q b δ‖ ≤ 2 * P δ / ‖b‖ := by
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have hbpos : 0 < ‖b‖ := by linarith
  have hu : ‖δ / b‖ ≤ 1 / 2 := by rw [norm_div, div_le_iff₀ hbpos]; linarith
  have hu' : ‖δ / b‖ = ‖δ‖ / ‖b‖ := norm_div _ _
  have hre1 : 0 < (b / 2).re := by simp; linarith
  have hre2 : 0 < ((b + δ) / 2).re := by simp; linarith
  have hbδn : ‖b‖ / 2 ≤ ‖b + δ‖ := by
    have := norm_sub_norm_le b (-δ)
    simp at this
    linarith
  rw [Q_eq_near hb hbδ hδ]
  -- the three pieces
  have hA : ‖(b / 2) * (log (1 + δ / b) - δ / b)‖ ≤ ‖δ‖ ^ 2 / (2 * ‖b‖) := by
    rw [norm_mul, norm_div, Complex.norm_ofNat]
    have := Complex.norm_log_one_add_sub_self_le (z := δ / b) (by linarith)
    have hinv : (1 - ‖δ / b‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    calc ‖b‖ / 2 * ‖log (1 + δ / b) - δ / b‖ ≤ ‖b‖ / 2 * (‖δ / b‖ ^ 2 * (1 - ‖δ / b‖)⁻¹ / 2) := by
          gcongr
      _ ≤ ‖b‖ / 2 * (‖δ / b‖ ^ 2 * 2 / 2) := by gcongr
      _ = ‖δ‖ ^ 2 / (2 * ‖b‖) := by rw [hu']; field_simp
  have hB : ‖((δ - 1) / 2) * log (1 + δ / b)‖ ≤ (3 / 4) * (‖δ‖ + 1) * ‖δ‖ / ‖b‖ := by
    rw [norm_mul, norm_div, Complex.norm_ofNat]
    have h1 : ‖δ - 1‖ ≤ ‖δ‖ + 1 := by
      calc ‖δ - 1‖ ≤ ‖δ‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = ‖δ‖ + 1 := by rw [norm_one]
    have h2 := Complex.norm_log_one_add_half_le_self hu
    calc ‖δ - 1‖ / 2 * ‖log (1 + δ / b)‖ ≤ (‖δ‖ + 1) / 2 * (3 / 2 * ‖δ / b‖) := by gcongr
      _ = (3 / 4) * (‖δ‖ + 1) * ‖δ‖ / ‖b‖ := by rw [hu']; field_simp; ring
  have hbδpos : 0 < ‖b + δ‖ := by linarith
  have hC : ‖R ((b + δ) / 2) - R (b / 2)‖ ≤ 1 / ‖b‖ + 1 / (2 * ‖b‖) := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · refine (norm_R_le hre2).trans ?_
      rw [norm_div, Complex.norm_ofNat]
      rw [div_le_div_iff₀ (by positivity) hbpos]
      nlinarith
    · refine (norm_R_le hre1).trans (le_of_eq ?_)
      rw [norm_div, Complex.norm_ofNat]
      field_simp
      norm_num
  calc ‖(b / 2) * (log (1 + δ / b) - δ / b) + ((δ - 1) / 2) * log (1 + δ / b) +
        (R ((b + δ) / 2) - R (b / 2))‖
      ≤ ‖(b / 2) * (log (1 + δ / b) - δ / b)‖ + ‖((δ - 1) / 2) * log (1 + δ / b)‖ +
        ‖R ((b + δ) / 2) - R (b / 2)‖ := norm_add₃_le
    _ ≤ ‖δ‖ ^ 2 / (2 * ‖b‖) + (3 / 4) * (‖δ‖ + 1) * ‖δ‖ / ‖b‖ + (1 / ‖b‖ + 1 / (2 * ‖b‖)) :=
        add_le_add (add_le_add hA hB) hC
    _ = (‖δ‖ ^ 2 / 2 + (3 / 4) * (‖δ‖ + 1) * ‖δ‖ + 3 / 2) / ‖b‖ := by
        field_simp
        ring
    _ ≤ 2 * P δ / ‖b‖ := by
        unfold P
        refine div_le_div_of_nonneg_right ?_ hbpos.le
        nlinarith [norm_nonneg δ]

theorem norm_ρ_sub_one_le {b δ : ℂ} (hbn : 2 ≤ ‖b‖) (hb0 : b ≠ 0) (hb1 : b - 1 ≠ 0) :
    ‖ρ b δ - 1‖ ≤ 6 * P δ / ‖b‖ := by
  have hbpos : 0 < ‖b‖ := by linarith
  have hb1n : ‖b‖ / 2 ≤ ‖b - 1‖ := by
    have := norm_sub_norm_le b 1
    rw [norm_one] at this
    linarith
  have heq : ρ b δ - 1 = (δ * (2 * b - 1) + δ ^ 2) / (b * (b - 1)) := by
    rw [ρ]
    field_simp
    ring
  rw [heq, norm_div, norm_mul]
  have hnum : ‖δ * (2 * b - 1) + δ ^ 2‖ ≤ ‖δ‖ * (3 * ‖b‖) + ‖δ‖ ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_pow]
    gcongr
    calc ‖2 * b - 1‖ ≤ ‖2 * b‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 * ‖b‖ + 1 := by rw [norm_mul, Complex.norm_ofNat, norm_one]
      _ ≤ 3 * ‖b‖ := by linarith
  rw [div_le_div_iff₀ (by positivity) hbpos]
  have hδ0 := norm_nonneg δ
  calc ‖δ * (2 * b - 1) + δ ^ 2‖ * ‖b‖ ≤ (‖δ‖ * (3 * ‖b‖) + ‖δ‖ ^ 2) * ‖b‖ := by gcongr
    _ ≤ 3 * (‖δ‖ ^ 2 + ‖δ‖ + 1) * ‖b‖ ^ 2 := by
        nlinarith [mul_nonneg (mul_nonneg (sq_nonneg ‖δ‖) hbpos.le) (by linarith : (0:ℝ) ≤ ‖b‖ - 1),
          sq_nonneg ‖b‖]
    _ = 6 * P δ * (‖b‖ * (‖b‖ / 2)) := by unfold P; ring
    _ ≤ 6 * P δ * (‖b‖ * ‖b - 1‖) := by
        have := P_pos δ
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb1n hbpos.le) (by positivity)

/-- **Near-field estimate**: `‖K − 1‖ ≤ 8 P(δ)/‖b‖ · exp(2 P(δ)/‖b‖)`. -/
theorem norm_K_sub_one_le {b δ : ℂ} (hb1 : 1 ≤ b.re) (hbn : 2 ≤ ‖b‖) (hb : 0 < b.im)
    (hδre : 0 ≤ δ.re) (hbδ : 0 < (b + δ).im) (hδ : ‖δ‖ ≤ ‖b‖ / 2) :
    ‖ρ b δ * cexp (Q b δ) - 1‖ ≤ 8 * P δ / ‖b‖ * Real.exp (2 * P δ / ‖b‖) := by
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have hb1' : b - 1 ≠ 0 := fun h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  have hbpos : 0 < ‖b‖ := by linarith
  have hQ := norm_Q_le_near hb1 hbn hb hδre hbδ hδ
  have hρ := norm_ρ_sub_one_le (δ := δ) hbn hb0 hb1'
  have hexpQ : ‖cexp (Q b δ)‖ ≤ Real.exp (2 * P δ / ‖b‖) := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hQ)
  have hE : ‖cexp (Q b δ) - 1‖ ≤ 2 * P δ / ‖b‖ * Real.exp (2 * P δ / ‖b‖) := by
    refine (norm_exp_sub_one_le_mul_exp _).trans ?_
    exact mul_le_mul hQ (Real.exp_le_exp.mpr hQ) (Real.exp_pos _).le
      (div_nonneg (by linarith [P_pos δ]) hbpos.le)
  calc ‖ρ b δ * cexp (Q b δ) - 1‖
      = ‖(ρ b δ - 1) * cexp (Q b δ) + (cexp (Q b δ) - 1)‖ := by ring_nf
    _ ≤ ‖(ρ b δ - 1) * cexp (Q b δ)‖ + ‖cexp (Q b δ) - 1‖ := norm_add_le _ _
    _ ≤ 6 * P δ / ‖b‖ * Real.exp (2 * P δ / ‖b‖) + 2 * P δ / ‖b‖ * Real.exp (2 * P δ / ‖b‖) := by
        rw [norm_mul]
        exact add_le_add (mul_le_mul hρ hexpQ (norm_nonneg _)
          (div_nonneg (by linarith [P_pos δ]) hbpos.le)) hE
    _ = 8 * P δ / ‖b‖ * Real.exp (2 * P δ / ‖b‖) := by ring

/-! ### The global estimate -/

theorem norm_ρ_le {b δ : ℂ} (hbn : 2 ≤ ‖b‖) (hb0 : b ≠ 0) (hb1 : b - 1 ≠ 0) :
    ‖ρ b δ‖ ≤ 2 * (‖b‖ + ‖δ‖ + 1) ^ 2 / ‖b‖ ^ 2 := by
  have hbpos : 0 < ‖b‖ := by linarith
  have hb1n : ‖b‖ / 2 ≤ ‖b - 1‖ := by
    have := norm_sub_norm_le b 1
    rw [norm_one] at this
    linarith
  rw [ρ, norm_div, norm_mul, norm_mul]
  have h1 : ‖b + δ‖ ≤ ‖b‖ + ‖δ‖ := norm_add_le _ _
  have h2 : ‖b + δ - 1‖ ≤ ‖b‖ + ‖δ‖ + 1 := by
    calc ‖b + δ - 1‖ ≤ ‖b + δ‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ ‖b‖ + ‖δ‖ + 1 := by rw [norm_one]; linarith
  rw [div_le_div_iff₀ (mul_pos hbpos (norm_pos_iff.mpr hb1)) (by positivity)]
  have hδ0 := norm_nonneg δ
  calc ‖b + δ‖ * ‖b + δ - 1‖ * ‖b‖ ^ 2 ≤ (‖b‖ + ‖δ‖) * (‖b‖ + ‖δ‖ + 1) * ‖b‖ ^ 2 := by gcongr
    _ ≤ (‖b‖ + ‖δ‖ + 1) ^ 2 * ‖b‖ ^ 2 := by gcongr; linarith
    _ = 2 * (‖b‖ + ‖δ‖ + 1) ^ 2 * (‖b‖ * (‖b‖ / 2)) := by ring
    _ ≤ 2 * (‖b‖ + ‖δ‖ + 1) ^ 2 * (‖b‖ * ‖b - 1‖) := by gcongr

theorem re_Q_le {b δ : ℂ} (hb1 : 1 ≤ b.re) (hbn : 1 ≤ ‖b‖) (hδre : 0 ≤ δ.re) :
    (Q b δ).re ≤ (b.re + δ.re - 1) * ‖δ‖ / (2 * ‖b‖) + π * (|b.im| + |δ.im|) + 1 := by
  have hbpos : 0 < ‖b‖ := by linarith
  have hb0 : b ≠ 0 := norm_pos_iff.mp hbpos
  have hbδ0 : b + δ ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have hre1 : 0 < (b / 2).re := by simp; linarith
  have hre2 : 0 < ((b + δ) / 2).re := by simp; linarith
  -- Q = ((b+δ-1)/2) (Log((b+δ)/2) − Log(b/2)) − δ/2 + ΔR
  have hQ : Q b δ = ((b + δ - 1) / 2) * (log ((b + δ) / 2) - log (b / 2)) - δ / 2 +
      (R ((b + δ) / 2) - R (b / 2)) := by
    rw [Q, L, L]
    ring
  rw [hQ]
  set A : ℂ := log ((b + δ) / 2) - log (b / 2) with hA
  have hAre : A.re = Real.log ‖b + δ‖ - Real.log ‖b‖ := by
    rw [hA, Complex.sub_re, Complex.log_re, Complex.log_re, norm_div, norm_div, Complex.norm_ofNat,
      Real.log_div (by positivity) (by norm_num), Real.log_div hbpos.ne' (by norm_num)]
    ring
  have hAre_le : A.re ≤ ‖δ‖ / ‖b‖ := by
    rw [hAre, ← Real.log_div (by positivity) hbpos.ne']
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [div_sub_one hbpos.ne', div_le_div_iff_of_pos_right hbpos]
    linarith [norm_add_le b δ]
  have hAim : |A.im| ≤ 2 * π := by
    rw [hA, Complex.sub_im, Complex.log_im, Complex.log_im]
    calc |arg ((b + δ) / 2) - arg (b / 2)| ≤ |arg ((b + δ) / 2)| + |arg (b / 2)| := abs_sub _ _
      _ ≤ π + π := add_le_add (Complex.abs_arg_le_pi _) (Complex.abs_arg_le_pi _)
      _ = 2 * π := by ring
  have hprod : (((b + δ - 1) / 2) * A).re ≤ (b.re + δ.re - 1) * ‖δ‖ / (2 * ‖b‖) +
      π * (|b.im| + |δ.im|) := by
    rw [Complex.mul_re]
    have hre : ((b + δ - 1) / 2).re = (b.re + δ.re - 1) / 2 := by simp
    have him : ((b + δ - 1) / 2).im = (b.im + δ.im) / 2 := by simp
    rw [hre, him]
    have h1 : (b.re + δ.re - 1) / 2 * A.re ≤ (b.re + δ.re - 1) * ‖δ‖ / (2 * ‖b‖) := by
      have : (b.re + δ.re - 1) / 2 * A.re ≤ (b.re + δ.re - 1) / 2 * (‖δ‖ / ‖b‖) :=
        mul_le_mul_of_nonneg_left hAre_le (by linarith)
      refine this.trans (le_of_eq ?_)
      field_simp
    have h2 : -((b.im + δ.im) / 2 * A.im) ≤ π * (|b.im| + |δ.im|) := by
      have := abs_le.mp hAim
      have hb' := abs_le.mp (le_refl |b.im|)
      have hd' := abs_le.mp (le_refl |δ.im|)
      nlinarith [abs_nonneg b.im, abs_nonneg δ.im, Real.pi_pos]
    linarith
  have hR : (R ((b + δ) / 2) - R (b / 2)).re ≤ 1 := by
    have h1 : ‖R ((b + δ) / 2)‖ ≤ 1 / 2 := by
      refine (norm_R_le hre2).trans ?_
      rw [norm_div, Complex.norm_ofNat]
      have : 1 ≤ ‖b + δ‖ := le_trans (by linarith : (1:ℝ) ≤ b.re + δ.re)
        (by simpa using Complex.re_le_norm (b + δ))
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have h2 : ‖R (b / 2)‖ ≤ 1 / 2 := by
      refine (norm_R_le hre1).trans ?_
      rw [norm_div, Complex.norm_ofNat]
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    calc (R ((b + δ) / 2) - R (b / 2)).re ≤ ‖R ((b + δ) / 2) - R (b / 2)‖ := Complex.re_le_norm _
      _ ≤ ‖R ((b + δ) / 2)‖ + ‖R (b / 2)‖ := norm_sub_le _ _
      _ ≤ 1 := by linarith
  rw [Complex.add_re, Complex.sub_re]
  have hδ2 : 0 ≤ (δ / 2).re := by simp; linarith
  linarith

/-- **Global estimate**: `‖K‖ ≤ 2 (‖b‖+‖δ‖+1)²/‖b‖² · exp((Re b + Re δ − 1)‖δ‖/(2‖b‖) + π(|Im b| + |Im δ|) + 1)`. -/
theorem norm_K_le {b δ : ℂ} (hb1 : 1 ≤ b.re) (hbn : 2 ≤ ‖b‖) (hδre : 0 ≤ δ.re) (hb1' : b - 1 ≠ 0) :
    ‖ρ b δ * cexp (Q b δ)‖ ≤ 2 * (‖b‖ + ‖δ‖ + 1) ^ 2 / ‖b‖ ^ 2 *
      Real.exp ((b.re + δ.re - 1) * ‖δ‖ / (2 * ‖b‖) + π * (|b.im| + |δ.im|) + 1) := by
  have hb0 : b ≠ 0 := norm_pos_iff.mp (by linarith)
  rw [norm_mul, Complex.norm_exp]
  exact mul_le_mul (norm_ρ_le hbn hb0 hb1') (Real.exp_le_exp.mpr (re_Q_le hb1 (by linarith) hδre))
    (Real.exp_pos _).le (by positivity)

end DBNSaddle
