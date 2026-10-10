/-
  DBNStirling -- Stirling's formula for the complex Gamma function with an explicit remainder.

  Step 3 of the Lambda >= 0 (Newman's conjecture) formalization following Dobner
  (arXiv:2005.05142); see telperion/docs/NEWMAN_LAMBDA_NONNEG_SCOPING_2026-10-10.md.  Mathlib has
  Bohr-Mollerup and real Stirling only; this module supplies the complex version needed for the
  saddle-point analysis of Dobner's Theorem 4, and the digamma asymptotic that drives it.

  Statement.  For `Re z > 0`,
      Γ(z) = exp (L z),   L z = (z - 1/2) Log z - z + (1/2) log (2π) + R z,
      R z  = 1/(12 z) - (1/2) ∫_0^∞ B̃₂(x) / (z + x)^2 dx,      ‖R z‖ ≤ 1/(4‖z‖),
  with `B̃₂(x) = {x}² - {x} + 1/6` the periodised second Bernoulli polynomial, and
      ψ(z) = Log z - 1/(2z) + R' z,   ‖R' z‖ ≤ 1/(2‖z‖²).

  Method.  Euler's limit formula `GammaSeq z n = n^z n! / ∏_{k ≤ n} (z+k) → Γ(z)` (Mathlib), with
  `exp (z log n + log n! - ∑ Log(z+k)) = GammaSeq z n`; second-order Euler-Maclaurin for
  `∑_{k ≤ n} Log (z+k)` on each unit cell from the explicit antiderivative
      Φ = B₂(x-m)/(z+x) - B₂'(x-m) Log(z+x) + 2 ((z+x) Log(z+x) - (z+x))   with   Φ' = B₂(x-m) · (-(z+x)^(-2));
  real Stirling (`Stirling.tendsto_stirlingSeq_sqrt_pi`) for `log n!`; the limit `n → ∞`.
  Everything is on the open right half-plane; no branch of `log Γ` is chosen, only `exp (L z)`.

  Nothing here is RH.  conjecture1_proved = False.
-/
import Mathlib

open Complex Filter Topology MeasureTheory Set intervalIntegral

namespace DBNStirling

/-! ### The periodised Bernoulli polynomial `B̃₂` -/

/-- `B̃₂(x) = {x}² − {x} + 1/6`. -/
noncomputable def sawB2 (x : ℝ) : ℝ := Int.fract x ^ 2 - Int.fract x + 1 / 6

lemma abs_sawB2_le (x : ℝ) : |sawB2 x| ≤ 1 / 6 := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  rw [sawB2, abs_le]
  constructor <;> nlinarith

lemma sawB2_eq_of_mem_Ico {m : ℕ} {x : ℝ} (hx : x ∈ Ico (m : ℝ) (m + 1)) :
    sawB2 x = (x - m) ^ 2 - (x - m) + 1 / 6 := by
  have hfl : ⌊x⌋ = (m : ℤ) := Int.floor_eq_iff.mpr (by exact_mod_cast hx)
  have : Int.fract x = x - m := by rw [Int.fract, hfl]; push_cast; ring
  rw [sawB2, this]

lemma measurable_sawB2 : Measurable sawB2 := by
  unfold sawB2
  exact ((measurable_fract.pow_const 2).sub measurable_fract).add_const _

/-! ### Elementary facts on the right half-plane -/

lemma add_ofReal_ne_zero {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 0 ≤ x) : z + x ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

lemma add_ofReal_mem_slitPlane {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 0 ≤ x) :
    z + x ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))

lemma add_natCast_ne_zero {z : ℂ} (hz : 0 < z.re) (k : ℕ) : z + k ≠ 0 := by
  have := add_ofReal_ne_zero hz (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  simpa using this

lemma hasDerivAt_ofReal (x : ℝ) : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 x := by
  simpa using (hasDerivAt_id x).ofReal_comp

lemma hasDerivAt_add_ofReal (z : ℂ) (x : ℝ) : HasDerivAt (fun x : ℝ => z + (x : ℂ)) 1 x :=
  (hasDerivAt_ofReal x).const_add z

lemma hasDerivAt_log_add {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun x : ℝ => log (z + x)) (z + x)⁻¹ x := by
  have h := (Complex.hasDerivAt_log (add_ofReal_mem_slitPlane hz hx)).comp (x : ℂ)
    ((hasDerivAt_id (x : ℂ)).const_add z)
  simpa using h.comp_ofReal

/-! ### The Euler–Maclaurin kernel and the cell antiderivative -/

/-- The kernel `B̃₂(x) · (−1/(z+x)²)`. -/
noncomputable def kern (z : ℂ) (x : ℝ) : ℂ := (sawB2 x : ℂ) * (-(1 / (z + x) ^ 2))

/-- `F z x = (z+x) Log(z+x) − (z+x)`, an antiderivative of `Log (z + x)`. -/
noncomputable def F (z : ℂ) (x : ℝ) : ℂ := (z + x) * log (z + x) - (z + x)

/-- `B₂(x − m)` as a complex-valued function of the real variable. -/
noncomputable def P (m : ℕ) (x : ℝ) : ℂ := ((x : ℂ) - m) ^ 2 - ((x : ℂ) - m) + 1 / 6

/-- `B₂'(x − m) = 2(x − m) − 1`. -/
noncomputable def Pd (m : ℕ) (x : ℝ) : ℂ := 2 * ((x : ℂ) - m) - 1

/-- The cell antiderivative: `Φ' = P · (−1/(z+x)²)`. -/
noncomputable def Φ (z : ℂ) (m : ℕ) (x : ℝ) : ℂ :=
  P m x / (z + x) - Pd m x * log (z + x) + 2 * F z x

/-- The telescoping part of `Φ`: `G z x = (1/6)/(z+x) + 2 F z x`. -/
noncomputable def G (z : ℂ) (x : ℝ) : ℂ := (1 / 6) / (z + x) + 2 * F z x

lemma hasDerivAt_P (m : ℕ) (x : ℝ) : HasDerivAt (P m) (Pd m x) x := by
  have h := ((((hasDerivAt_ofReal x).sub_const (m : ℂ)).pow 2).sub
    ((hasDerivAt_ofReal x).sub_const (m : ℂ))).add_const (1 / 6 : ℂ)
  exact h.congr_deriv (by simp [Pd])

lemma hasDerivAt_Pd (m : ℕ) (x : ℝ) : HasDerivAt (Pd m) 2 x := by
  have h := (((hasDerivAt_ofReal x).sub_const (m : ℂ)).const_mul (2 : ℂ)).sub_const (1 : ℂ)
  exact h.congr_deriv (by simp)

lemma hasDerivAt_F {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (F z) (log (z + x)) x := by
  have hne := add_ofReal_ne_zero hz hx
  have h := ((hasDerivAt_add_ofReal z x).mul (hasDerivAt_log_add hz hx)).sub
    (hasDerivAt_add_ofReal z x)
  exact h.congr_deriv (by rw [one_mul, mul_inv_cancel₀ hne]; ring)

lemma hasDerivAt_Φ {z : ℂ} (hz : 0 < z.re) (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (Φ z m) (P m x * (-(1 / (z + x) ^ 2))) x := by
  have hne := add_ofReal_ne_zero hz hx
  have h := (((hasDerivAt_P m x).div (hasDerivAt_add_ofReal z x) hne).sub
    ((hasDerivAt_Pd m x).mul (hasDerivAt_log_add hz hx))).add
    ((hasDerivAt_F hz hx).const_mul (2 : ℂ))
  exact h.congr_deriv (by field_simp; ring)

lemma continuousOn_inv_sq {z : ℂ} (hz : 0 < z.re) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ContinuousOn (fun x : ℝ => -(1 / (z + x) ^ 2)) (uIcc a b) := by
  refine ContinuousOn.neg (ContinuousOn.div continuousOn_const (by fun_prop) ?_)
  intro x hx
  have hx0 : 0 ≤ x := le_trans (le_min ha hb) hx.1
  exact pow_ne_zero 2 (add_ofReal_ne_zero hz hx0)

lemma intervalIntegrable_kern {z : ℂ} (hz : 0 < z.re) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (kern z) volume a b := by
  have hsaw : IntervalIntegrable (fun x : ℝ => (sawB2 x : ℂ)) volume a b := by
    apply IntervalIntegrable.mono_fun' (g := fun _ => (1 / 6 : ℝ)) intervalIntegrable_const
    · exact (Complex.continuous_ofReal.measurable.comp measurable_sawB2).aestronglyMeasurable
    · exact ae_of_all _ fun x => by
        show ‖(sawB2 x : ℂ)‖ ≤ 1 / 6
        rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_sawB2_le x
  exact hsaw.mul_continuousOn (continuousOn_inv_sq hz ha hb)

/-- The cell identity: `∫_m^{m+1} B̃₂(x) (−1/(z+x)²) dx = Φ(m+1) − Φ(m)`. -/
lemma integral_kern_cell {z : ℂ} (hz : 0 < z.re) (m : ℕ) :
    ∫ x in (m : ℝ)..(m + 1), kern z x = Φ z m (m + 1) - Φ z m m := by
  have hcc : (m : ℝ) ≤ m + 1 := by linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hcongr : ∫ x in (m : ℝ)..(m + 1), kern z x =
      ∫ x in (m : ℝ)..(m + 1), P m x * (-(1 / (z + x) ^ 2)) := by
    apply intervalIntegral.integral_congr_ae
    have hnull : ∀ᵐ x, x ≠ ((m : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico (m : ℝ) (m + 1) := ⟨hxmem.1.le, lt_of_le_of_ne hxmem.2 hxne⟩
    rw [kern, sawB2_eq_of_mem_Ico hxIco, P]
    push_cast
    ring
  rw [hcongr]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hcc] at hx
    exact hasDerivAt_Φ hz m (by linarith [hx.1])
  · apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.mul ?_ (continuousOn_inv_sq hz hm0 (by linarith))
    unfold P
    fun_prop

/-- **Second-order Euler–Maclaurin for `∑_{k ≤ n} Log (z + k)`.** -/
theorem sum_log_eq {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), log (z + k) =
      F z n - F z 0 + (log z + log (z + n)) / 2 + (1 / 12) * (1 / (z + n) - 1 / z)
        - (1 / 2) * ∫ x in (0 : ℝ)..n, kern z x := by
  have hsum : ∑ m ∈ Finset.range n, ∫ x in (m : ℝ)..(m + 1), kern z x =
      ∫ x in (0 : ℝ)..n, kern z x := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ))
      (n := n) (f := kern z) (μ := volume)
      (fun k _ => intervalIntegrable_kern hz (Nat.cast_nonneg k) (by positivity))
    simpa using h
  have hcells : ∑ m ∈ Finset.range n, ∫ x in (m : ℝ)..(m + 1), kern z x =
      ∑ m ∈ Finset.range n, (Φ z m (m + 1) - Φ z m m) :=
    Finset.sum_congr rfl fun m _ => integral_kern_cell hz m
  have hΦ : ∀ m : ℕ, Φ z m (m + 1) - Φ z m m =
      (G z ((m + 1 : ℕ) : ℝ) - G z m) - (log (z + ((m + 1 : ℕ) : ℝ)) + log (z + m)) := by
    intro m
    simp only [Φ, P, Pd, G]
    push_cast
    ring
  have htel : ∑ m ∈ Finset.range n, (G z ((m + 1 : ℕ) : ℝ) - G z m) = G z n - G z ((0 : ℕ) : ℝ) :=
    Finset.sum_range_sub (fun m : ℕ => G z (m : ℝ)) n
  have hlogs : ∑ m ∈ Finset.range n, (log (z + ((m + 1 : ℕ) : ℝ)) + log (z + m)) =
      2 * ∑ k ∈ Finset.range (n + 1), log (z + k) - log z - log (z + n) := by
    have e1 : ∀ m : ℕ, log (z + (((m + 1 : ℕ) : ℝ) : ℂ)) = log (z + ((m + 1 : ℕ) : ℂ)) :=
      fun m => by rw [Complex.ofReal_natCast]
    have h1 := Finset.sum_range_succ' (fun k : ℕ => log (z + (k : ℂ))) n
    have h2 := Finset.sum_range_succ (fun k : ℕ => log (z + (k : ℂ))) n
    simp only [Nat.cast_zero, add_zero] at h1
    rw [Finset.sum_add_distrib, Finset.sum_congr rfl (fun m _ => e1 m)]
    linear_combination -h1 - h2
  have key : ∫ x in (0 : ℝ)..n, kern z x = (G z n - G z ((0 : ℕ) : ℝ)) -
      (2 * ∑ k ∈ Finset.range (n + 1), log (z + k) - log z - log (z + n)) := by
    rw [← hsum, hcells, ← htel, ← hlogs, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ => hΦ m
  simp only [G, Nat.cast_zero, Complex.ofReal_zero, add_zero, Complex.ofReal_natCast] at key
  linear_combination (1 / 2 : ℂ) * key

/-! ### Euler's product -/

/-- `Lseq z n = z log n + log n! − ∑_{k ≤ n} Log (z + k)`, so that `exp (Lseq z n) = GammaSeq z n`. -/
noncomputable def Lseq (z : ℂ) (n : ℕ) : ℂ :=
  z * Real.log n + Real.log (n.factorial) - ∑ k ∈ Finset.range (n + 1), log (z + k)

lemma exp_Lseq {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : 1 ≤ n) :
    exp (Lseq z n) = GammaSeq z n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Lseq, exp_sub, exp_add, exp_sum, GammaSeq]
  congr 1
  · congr 1
    · rw [cpow_def_of_ne_zero (by exact_mod_cast hn'.ne'), ← Complex.natCast_log, mul_comm]
    · rw [← Complex.ofReal_exp, Real.exp_log (by positivity)]
      simp
  · exact Finset.prod_congr rfl fun k _ => exp_log (add_natCast_ne_zero hz k)

/-! ### The improper integral `∫_0^∞ kern` -/

lemma norm_sq_add_ofReal (z : ℂ) (x : ℝ) : ‖z + x‖ ^ 2 = ‖z‖ ^ 2 + 2 * x * z.re + x ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.normSq_apply]
  simp
  ring

/-- `(‖z‖ + x)² ≤ 2 ‖z + x‖²` for `Re z ≥ 0`, `x ≥ 0`. -/
lemma sq_norm_add_le {z : ℂ} (hz : 0 ≤ z.re) {x : ℝ} (hx : 0 ≤ x) :
    (‖z‖ + x) ^ 2 ≤ 2 * ‖z + x‖ ^ 2 := by
  rw [norm_sq_add_ofReal]
  nlinarith [sq_nonneg (‖z‖ - x), mul_nonneg hx hz]

lemma norm_kern_le {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 0 ≤ x) :
    ‖kern z x‖ ≤ (1 / 3) / (‖z‖ + x) ^ 2 := by
  have hne := add_ofReal_ne_zero hz hx
  have hpos : 0 < (‖z‖ + x) ^ 2 := by
    have : 0 < ‖z‖ := norm_pos_iff.mpr (fun h => by simp [h] at hz)
    positivity
  have hpos2 : 0 < ‖z + x‖ ^ 2 := by positivity
  calc ‖kern z x‖ = |sawB2 x| * (1 / ‖z + x‖ ^ 2) := by
        rw [kern, norm_mul, norm_neg, norm_div, norm_one, norm_pow, Complex.norm_real,
          Real.norm_eq_abs]
    _ ≤ (1 / 6) * (1 / ‖z + x‖ ^ 2) := by gcongr; exact abs_sawB2_le x
    _ ≤ (1 / 6) * (2 / (‖z‖ + x) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rw [div_le_div_iff₀ hpos2 hpos]
        linarith [sq_norm_add_le hz.le hx]
    _ = (1 / 3) / (‖z‖ + x) ^ 2 := by ring

/-- `∫_0^∞ (a + x)^(-2) dx = 1/a` for `a > 0`, with integrability. -/
lemma hasDerivAt_neg_inv_add {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun x : ℝ => -1 / (a + x)) (1 / (a + x) ^ 2) x := by
  have hne : a + x ≠ 0 := by positivity
  have h := (((hasDerivAt_id' x).const_add a).inv hne).neg
  refine h.congr_deriv ?_ |>.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  · field_simp
  · simp [neg_div]

lemma tendsto_neg_inv_add (a : ℝ) : Tendsto (fun x : ℝ => -1 / (a + x)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ _ tendsto_id)

lemma integrableOn_inv_sq_add {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => 1 / (a + x) ^ 2) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun x hx => hasDerivAt_neg_inv_add ha hx)
    (fun x _ => by positivity) (tendsto_neg_inv_add a)

lemma integral_inv_sq_add {a : ℝ} (ha : 0 < a) :
    ∫ x in Ioi 0, 1 / (a + x) ^ 2 = 1 / a := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun x hx => hasDerivAt_neg_inv_add ha hx)
    (fun x _ => by positivity) (tendsto_neg_inv_add a)]
  simp [neg_div]

lemma hasDerivAt_neg_inv_sq_add {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun x : ℝ => -1 / (2 * (a + x) ^ 2)) (1 / (a + x) ^ 3) x := by
  have hne : a + x ≠ 0 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => (a + y) ^ 2) (2 * (a + x)) x := by
    have := ((hasDerivAt_id' x).const_add a).pow 2
    refine this.congr_deriv ?_
    simp
  have h2 : HasDerivAt (fun y : ℝ => ((a + y) ^ 2)⁻¹) (-(2 * (a + x)) / ((a + x) ^ 2) ^ 2) x :=
    h1.inv (pow_ne_zero 2 hne)
  have h3 := h2.const_mul (-(1 / 2) : ℝ)
  refine h3.congr_deriv ?_ |>.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  · field_simp
  · show -1 / (2 * (a + y) ^ 2) = -(1 / 2) * ((a + y) ^ 2)⁻¹
    rw [div_eq_mul_inv, mul_inv]
    ring

lemma tendsto_neg_inv_sq_add (a : ℝ) :
    Tendsto (fun x : ℝ => -1 / (2 * (a + x) ^ 2)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => (a + x) ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_left _ _ tendsto_id)
  have h2 : Tendsto (fun x : ℝ => 2 * (a + x) ^ 2) atTop atTop :=
    tendsto_atTop_mono (fun x => by nlinarith [sq_nonneg (a + x)]) h1
  exact tendsto_const_nhds.div_atTop h2

lemma integrableOn_inv_cube_add {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => 1 / (a + x) ^ 3) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun x hx => hasDerivAt_neg_inv_sq_add ha hx)
    (fun x hx => by have : 0 < x := hx; positivity) (tendsto_neg_inv_sq_add a)

lemma integral_inv_cube_add {a : ℝ} (ha : 0 < a) :
    ∫ x in Ioi 0, 1 / (a + x) ^ 3 = 1 / (2 * a ^ 2) := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun x hx => hasDerivAt_neg_inv_sq_add ha hx)
    (fun x hx => by have : 0 < x := hx; positivity) (tendsto_neg_inv_sq_add a)]
  simp [neg_div]

lemma measurable_kern (z : ℂ) : Measurable (kern z) := by
  unfold kern
  exact (Complex.continuous_ofReal.measurable.comp measurable_sawB2).mul
    ((measurable_const.div ((measurable_const.add Complex.measurable_ofReal).pow_const 2)).neg)

lemma norm_pos_of_re_pos {z : ℂ} (hz : 0 < z.re) : 0 < ‖z‖ :=
  norm_pos_iff.mpr fun h => by simp [h] at hz

lemma integrableOn_kern {z : ℂ} (hz : 0 < z.re) : IntegrableOn (kern z) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_inv_sq_add (norm_pos_of_re_pos hz)).const_mul (1 / 3))
    (measurable_kern z).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  exact ae_of_all _ fun x hx => by
    have := norm_kern_le hz (le_of_lt hx)
    rwa [div_eq_mul_one_div] at this

/-! ### The remainder and the main identity -/

/-- The Stirling remainder `R z = 1/(12 z) − (1/2) ∫_0^∞ B̃₂(x)/(z+x)² dx`. -/
noncomputable def R (z : ℂ) : ℂ := 1 / (12 * z) + (1 / 2) * ∫ x in Ioi 0, kern z x

/-- `L z = (z − 1/2) Log z − z + (1/2) log (2π) + R z`, so that `Γ z = exp (L z)`. -/
noncomputable def L (z : ℂ) : ℂ :=
  (z - 1 / 2) * log z - z + (1 / 2) * Real.log (2 * Real.pi) + R z

lemma tendsto_log_stirlingSeq :
    Tendsto (fun n : ℕ => ((Real.log (Stirling.stirlingSeq n) : ℝ) : ℂ)) atTop
      (𝓝 ((1 / 2 : ℂ) * Real.log Real.pi)) := by
  have h := (Real.continuousAt_log (Real.sqrt_pos.mpr Real.pi_pos).ne').tendsto.comp
    Stirling.tendsto_stirlingSeq_sqrt_pi
  rw [Real.log_sqrt Real.pi_pos.le] at h
  have h2 := (Complex.continuous_ofReal.tendsto _).comp h
  have h3 : Tendsto (fun n : ℕ => ((Real.log (Stirling.stirlingSeq n) : ℝ) : ℂ)) atTop
      (𝓝 ((Real.log Real.pi / 2 : ℝ) : ℂ)) := h2
  convert h3 using 2
  push_cast
  ring

/-- The `n`-dependent part of `Lseq` after Euler–Maclaurin:
`D z n = log (stirlingSeq n) + (1/2) log 2 + z − (z + n + 1/2) Log (1 + z/n)`. -/
noncomputable def D (z : ℂ) (n : ℕ) : ℂ :=
  Real.log (Stirling.stirlingSeq n) + (1 / 2) * Real.log 2 + z - (z + n + 1 / 2) * log (1 + z / n)

lemma log_add_natCast {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : 1 ≤ n) :
    log (z + n) = log (n : ℂ) + log (1 + z / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn'.ne'
  have hx : (1 : ℂ) + z / n ≠ 0 := by
    intro h
    have : z + n = 0 := by
      have := congrArg (fun w => (n : ℂ) * w) h
      simp only [mul_add, mul_one, mul_zero] at this
      rw [mul_div_cancel₀ _ hnc] at this
      linear_combination this
    exact add_natCast_ne_zero hz n this
  have h := Complex.log_ofReal_mul hn' hx
  rw [show ((n : ℝ) : ℂ) * (1 + z / n) = z + n by
    push_cast; rw [mul_add, mul_one, mul_div_cancel₀ _ hnc, add_comm], Complex.natCast_log] at h
  exact h

lemma log_factorial_eq (n : ℕ) (hn : 1 ≤ n) :
    ((Real.log (n.factorial) : ℝ) : ℂ) = Real.log (Stirling.stirlingSeq n) + (1 / 2) * Real.log 2
      + (1 / 2) * log (n : ℂ) + n * log (n : ℂ) - n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Stirling.log_stirlingSeq_formula n
  rw [Real.log_mul two_ne_zero hn'.ne', Real.log_div hn'.ne' (Real.exp_pos 1).ne',
    Real.log_exp] at h
  have : Real.log (n.factorial) = Real.log (Stirling.stirlingSeq n) + 1 / 2 * Real.log 2
      + 1 / 2 * Real.log n + n * Real.log n - n := by linear_combination (-1 : ℝ) * h
  rw [this]
  push_cast
  ring

/-- `Lseq` decomposed against `L`: everything but `L z` tends to zero. -/
lemma Lseq_eq {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : 1 ≤ n) :
    Lseq z n = L z + (D z n - (1 / 2) * Real.log (2 * Real.pi)) - (1 / 12) * (1 / (z + n))
      + (1 / 2) * ((∫ x in (0 : ℝ)..n, kern z x) - ∫ x in Ioi 0, kern z x) := by
  have hS := sum_log_eq hz n
  have hf := log_factorial_eq n hn
  have hl := log_add_natCast hz hn
  simp only [Lseq, L, R, D]
  rw [hS]
  simp only [F, Complex.ofReal_natCast]
  rw [hf, hl]
  push_cast
  ring_nf

lemma tendsto_log_one_add_div (z : ℂ) :
    Tendsto (fun n : ℕ => log (1 + z / n)) atTop (𝓝 0) := by
  have h2 : Tendsto (fun n : ℕ => (1 : ℂ) + z / n) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℂ))).add (tendsto_const_div_atTop_nhds_zero_nat z)
  have h := (continuousAt_clog Complex.one_mem_slitPlane).tendsto.comp h2
  rw [Complex.log_one] at h
  exact h

lemma tendsto_natCast_mul_log_one_add_div {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun n : ℕ => (n : ℂ) * log (1 + z / n)) atTop (𝓝 z) := by
  have hd := hasDerivAt_iff_tendsto_slope_zero.mp (Complex.hasDerivAt_log Complex.one_mem_slitPlane)
  have ht : Tendsto (fun n : ℕ => z / (n : ℂ)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_div_atTop_nhds_zero_nat z, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    exact div_ne_zero hz this
  have h := (hd.comp ht).const_mul z
  refine h.congr' ?_ |>.trans ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    simp only [Function.comp, smul_eq_mul, Complex.log_one, sub_zero]
    field_simp
  · simp

lemma tendsto_D {z : ℂ} (hz : 0 < z.re) :
    Tendsto (D z) atTop (𝓝 ((1 / 2 : ℂ) * Real.log (2 * Real.pi))) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hA := tendsto_log_stirlingSeq
  have hB : Tendsto (fun n : ℕ => (z + n + 1 / 2) * log (1 + z / n)) atTop (𝓝 z) := by
    have h1 := (tendsto_log_one_add_div z).const_mul (z + 1 / 2)
    have h2 := tendsto_natCast_mul_log_one_add_div hz0
    have h := h1.add h2
    simp only [mul_zero, zero_add] at h
    refine h.congr fun n => ?_
    ring
  have h := ((hA.add_const ((1 / 2 : ℂ) * Real.log 2)).add_const z).sub hB
  have hfun : D z = fun n : ℕ => ((Real.log (Stirling.stirlingSeq n) : ℝ) : ℂ)
      + (1 / 2 : ℂ) * Real.log 2 + z - (z + n + 1 / 2) * log (1 + z / n) := rfl
  rw [hfun, Real.log_mul two_ne_zero Real.pi_pos.ne']
  convert h using 2
  push_cast
  ring

lemma tendsto_inv_add_natCast {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun n : ℕ => 1 / (z + n)) atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_ tendsto_one_div_atTop_nhds_zero_nat
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [norm_div, norm_one]
  have hre : (n : ℝ) ≤ ‖z + n‖ := by
    have := Complex.re_le_norm (z + n)
    simp at this
    linarith
  exact div_le_div_of_nonneg_left zero_le_one hn' hre

theorem tendsto_Lseq {z : ℂ} (hz : 0 < z.re) : Tendsto (Lseq z) atTop (𝓝 (L z)) := by
  have hD := tendsto_D hz
  have hC := tendsto_inv_add_natCast hz
  have hI : Tendsto (fun n : ℕ => ∫ x in (0 : ℝ)..n, kern z x) atTop (𝓝 (∫ x in Ioi 0, kern z x)) :=
    intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_kern hz) tendsto_natCast_atTop_atTop
  have h := ((tendsto_const_nhds (x := L z)).add
    (hD.sub (tendsto_const_nhds (x := (1 / 2 : ℂ) * Real.log (2 * Real.pi))))).sub
    (hC.const_mul (1 / 12 : ℂ)) |>.add
    ((hI.sub (tendsto_const_nhds (x := ∫ x in Ioi 0, kern z x))).const_mul (1 / 2 : ℂ))
  simp only [sub_self, mul_zero, add_zero, sub_zero] at h
  refine Tendsto.congr' ?_ h
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (Lseq_eq hz hn).symm

/-- **Stirling's formula with remainder.**  `Γ z = exp (L z)` on the right half-plane. -/
theorem Gamma_eq_exp_L {z : ℂ} (hz : 0 < z.re) : Gamma z = exp (L z) := by
  have h1 : Tendsto (fun n => GammaSeq z n) atTop (𝓝 (Gamma z)) := GammaSeq_tendsto_Gamma z
  have h2 : Tendsto (fun n => GammaSeq z n) atTop (𝓝 (exp (L z))) := by
    refine ((Complex.continuous_exp.tendsto _).comp (tendsto_Lseq hz)).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact exp_Lseq hz hn
  exact tendsto_nhds_unique h1 h2

/-! ### Bounds on the remainder -/

theorem norm_R_le {z : ℂ} (hz : 0 < z.re) : ‖R z‖ ≤ 1 / (4 * ‖z‖) := by
  have hz' := norm_pos_of_re_pos hz
  have hint : ‖∫ x in Ioi 0, kern z x‖ ≤ (1 / 3) * (1 / ‖z‖) := by
    have hg : Integrable (fun x : ℝ => (1 / 3) * (1 / (‖z‖ + x) ^ 2)) (volume.restrict (Ioi 0)) :=
      (integrableOn_inv_sq_add hz').const_mul _
    refine (MeasureTheory.norm_integral_le_of_norm_le hg ?_).trans ?_
    · rw [ae_restrict_iff' measurableSet_Ioi]
      exact ae_of_all _ fun x hx => by
        have := norm_kern_le hz (le_of_lt hx)
        rwa [div_eq_mul_one_div] at this
    · rw [MeasureTheory.integral_const_mul, integral_inv_sq_add hz']
  calc ‖R z‖ ≤ ‖1 / (12 * z)‖ + ‖(1 / 2 : ℂ) * ∫ x in Ioi 0, kern z x‖ := norm_add_le _ _
    _ = 1 / (12 * ‖z‖) + (1 / 2) * ‖∫ x in Ioi 0, kern z x‖ := by
        rw [norm_div, norm_one, norm_mul, norm_mul]; norm_num
    _ ≤ 1 / (12 * ‖z‖) + (1 / 2) * ((1 / 3) * (1 / ‖z‖)) := by gcongr
    _ = 1 / (4 * ‖z‖) := by field_simp; ring

/-! ### The derivative of the remainder and the digamma function -/

/-- The derived kernel `B̃₂(x) / (z+x)³`. -/
noncomputable def kern' (z : ℂ) (x : ℝ) : ℂ := (sawB2 x : ℂ) * (1 / (z + x) ^ 3)

/-- `R' z = −1/(12 z²) + ∫_0^∞ B̃₂(x)/(z+x)³ dx`. -/
noncomputable def R' (z : ℂ) : ℂ := -1 / (12 * z ^ 2) + ∫ x in Ioi 0, kern' z x

lemma measurable_kern' (z : ℂ) : Measurable (kern' z) := by
  unfold kern'
  exact (Complex.continuous_ofReal.measurable.comp measurable_sawB2).mul
    (measurable_const.div ((measurable_const.add Complex.measurable_ofReal).pow_const 3))

lemma re_add_le_norm (z : ℂ) (x : ℝ) : z.re + x ≤ ‖z + x‖ := by
  have := Complex.re_le_norm (z + x)
  simpa using this

lemma norm_kern'_le_re {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 0 ≤ x) :
    ‖kern' z x‖ ≤ (1 / 6) * (1 / (z.re + x) ^ 3) := by
  have hpos : 0 < z.re + x := by linarith
  have hle := re_add_le_norm z x
  rw [kern', norm_mul, norm_div, norm_one, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  calc |sawB2 x| * (1 / ‖z + x‖ ^ 3) ≤ (1 / 6) * (1 / ‖z + x‖ ^ 3) := by
        gcongr; exact abs_sawB2_le x
    _ ≤ (1 / 6) * (1 / (z.re + x) ^ 3) := by gcongr

/-- Differentiation under the integral: `z ↦ ∫_0^∞ kern z` has derivative `2 ∫_0^∞ kern' z`. -/
lemma hasDerivAt_integral_kern {z₀ : ℂ} (hz₀ : 0 < z₀.re) :
    HasDerivAt (fun z => ∫ x in Ioi 0, kern z x) (2 * ∫ x in Ioi 0, kern' z₀ x) z₀ := by
  set r := z₀.re / 2 with hr
  have hrpos : 0 < r := by positivity
  have hball : ∀ z ∈ Metric.ball z₀ r, r < z.re := by
    intro z hz
    have h := Complex.abs_re_le_norm (z - z₀)
    rw [Complex.sub_re] at h
    have := (abs_lt.mp (lt_of_le_of_lt h (by simpa [dist_eq_norm] using hz))).1
    linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun z x => kern z x) (F' := fun z x => 2 * kern' z x) (x₀ := z₀)
    (s := Metric.ball z₀ r) (bound := fun x => (1 / 3) * (1 / (r + x) ^ 3))
    (Metric.ball_mem_nhds z₀ hrpos)
    (Eventually.of_forall fun z => (measurable_kern z).aestronglyMeasurable)
    (integrableOn_kern hz₀)
    ((measurable_kern' z₀).const_mul 2).aestronglyMeasurable ?_
    ((integrableOn_inv_cube_add hrpos).const_mul _) ?_
  · have h := key.2
    rw [MeasureTheory.integral_const_mul] at h
    exact h
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine ae_of_all _ fun x hx z hz => ?_
    have hx0 : 0 ≤ x := le_of_lt hx
    have hzre : 0 < z.re := lt_trans hrpos (hball z hz)
    rw [norm_mul, Complex.norm_ofNat]
    calc 2 * ‖kern' z x‖ ≤ 2 * ((1 / 6) * (1 / (z.re + x) ^ 3)) := by
          gcongr; exact norm_kern'_le_re hzre hx0
      _ ≤ 2 * ((1 / 6) * (1 / (r + x) ^ 3)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact one_div_le_one_div_of_le (by positivity)
            (pow_le_pow_left₀ (by positivity) (by linarith [(hball z hz).le]) 3)
      _ = (1 / 3) * (1 / (r + x) ^ 3) := by ring
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine ae_of_all _ fun x hx z hz => ?_
    have hx0 : 0 ≤ x := le_of_lt hx
    have hzre : 0 < z.re := lt_trans hrpos (hball z hz)
    have hne := add_ofReal_ne_zero hzre hx0
    -- d/dz (−1/(z+x)²) = 2/(z+x)³
    have h1 : HasDerivAt (fun w : ℂ => (w + x) ^ 2) (2 * (z + x)) z := by
      have := ((hasDerivAt_id' z).add_const (x : ℂ)).pow 2
      refine this.congr_deriv ?_
      simp
    have h2 := (h1.inv (pow_ne_zero 2 hne)).neg.const_mul ((sawB2 x : ℝ) : ℂ)
    refine h2.congr_deriv ?_ |>.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
    · simp only [kern']
      field_simp
    · simp only [kern, Pi.neg_apply, Pi.inv_apply]
      ring

theorem hasDerivAt_R {z : ℂ} (hz : 0 < z.re) : HasDerivAt R (R' z) z := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have h1 : HasDerivAt (fun w : ℂ => 1 / (12 * w)) (-1 / (12 * z ^ 2)) z := by
    have := ((hasDerivAt_id' z).const_mul (12 : ℂ)).inv (mul_ne_zero (by norm_num) hz0)
    refine this.congr_deriv ?_ |>.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
    · field_simp
    · simp
  have h2 := (hasDerivAt_integral_kern hz).const_mul (1 / 2 : ℂ)
  have h := h1.add h2
  refine h.congr_deriv ?_
  simp only [R']
  ring

theorem norm_R'_le {z : ℂ} (hz : 0 < z.re) : ‖R' z‖ ≤ 1 / (2 * ‖z‖ ^ 2) := by
  have hz' := norm_pos_of_re_pos hz
  -- ‖kern' z x‖ ≤ (1/6) / ‖z+x‖³ ≤ (1/6) · 4 / (‖z‖+x)³
  have hpt : ∀ x : ℝ, 0 ≤ x → ‖kern' z x‖ ≤ (2 / 3) * (1 / (‖z‖ + x) ^ 3) := by
    intro x hx
    have hA : 0 ≤ ‖z‖ + x := by positivity
    have hB : 0 ≤ ‖z + x‖ := norm_nonneg _
    have hne := add_ofReal_ne_zero hz hx
    have hBpos : 0 < ‖z + x‖ := norm_pos_iff.mpr hne
    have hsq := sq_norm_add_le hz.le hx
    have hAB : ‖z‖ + x ≤ (3 / 2) * ‖z + x‖ := by nlinarith
    have hcube : (‖z‖ + x) ^ 3 ≤ 4 * ‖z + x‖ ^ 3 := by
      calc (‖z‖ + x) ^ 3 ≤ ((3 / 2) * ‖z + x‖) ^ 3 := by gcongr
        _ = (27 / 8) * ‖z + x‖ ^ 3 := by ring
        _ ≤ 4 * ‖z + x‖ ^ 3 := by nlinarith [pow_nonneg hB 3]
    rw [kern', norm_mul, norm_div, norm_one, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    calc |sawB2 x| * (1 / ‖z + x‖ ^ 3) ≤ (1 / 6) * (1 / ‖z + x‖ ^ 3) := by
          gcongr; exact abs_sawB2_le x
      _ ≤ (1 / 6) * (4 / (‖z‖ + x) ^ 3) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          linarith
      _ = (2 / 3) * (1 / (‖z‖ + x) ^ 3) := by ring
  have hint : ‖∫ x in Ioi 0, kern' z x‖ ≤ (2 / 3) * (1 / (2 * ‖z‖ ^ 2)) := by
    have hg : Integrable (fun x : ℝ => (2 / 3) * (1 / (‖z‖ + x) ^ 3)) (volume.restrict (Ioi 0)) :=
      (integrableOn_inv_cube_add hz').const_mul _
    refine (MeasureTheory.norm_integral_le_of_norm_le hg ?_).trans ?_
    · rw [ae_restrict_iff' measurableSet_Ioi]
      exact ae_of_all _ fun x hx => hpt x (le_of_lt hx)
    · rw [MeasureTheory.integral_const_mul, integral_inv_cube_add hz']
  calc ‖R' z‖ ≤ ‖-1 / (12 * z ^ 2)‖ + ‖∫ x in Ioi 0, kern' z x‖ := norm_add_le _ _
    _ = 1 / (12 * ‖z‖ ^ 2) + ‖∫ x in Ioi 0, kern' z x‖ := by
        rw [norm_div, norm_neg, norm_one, norm_mul, norm_pow]; norm_num
    _ ≤ 1 / (12 * ‖z‖ ^ 2) + (2 / 3) * (1 / (2 * ‖z‖ ^ 2)) := by gcongr
    _ ≤ 1 / (2 * ‖z‖ ^ 2) := by
        rw [show (1 : ℝ) / (12 * ‖z‖ ^ 2) + (2 / 3) * (1 / (2 * ‖z‖ ^ 2)) =
          (5 / 12) * (1 / ‖z‖ ^ 2) by field_simp; ring,
          show (1 : ℝ) / (2 * ‖z‖ ^ 2) = (1 / 2) * (1 / ‖z‖ ^ 2) by field_simp]
        exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

/-- `L` is differentiable on the right half-plane, with `L' z = Log z − 1/(2z) + R' z`. -/
theorem hasDerivAt_L {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt L (log z - 1 / (2 * z) + R' z) z := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hslit : z ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl hz)
  have h := ((((hasDerivAt_id' z).sub_const (1 / 2 : ℂ)).mul (Complex.hasDerivAt_log hslit)).sub
    (hasDerivAt_id' z)).add_const ((1 / 2 : ℂ) * Real.log (2 * Real.pi)) |>.add (hasDerivAt_R hz)
  refine h.congr_deriv ?_
  field_simp
  ring

/-- **Digamma asymptotic.**  `ψ(z) = Log z − 1/(2z) + R' z` on the right half-plane. -/
theorem digamma_eq {z : ℂ} (hz : 0 < z.re) : digamma z = log z - 1 / (2 * z) + R' z := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hG : HasDerivAt Gamma (exp (L z) * (log z - 1 / (2 * z) + R' z)) z := by
    have h := (hasDerivAt_L hz).cexp
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact Gamma_eq_exp_L hw
  rw [digamma_def, logDeriv_apply, hG.deriv, Gamma_eq_exp_L hz]
  field_simp [Complex.exp_ne_zero]

theorem norm_digamma_sub_log_le {z : ℂ} (hz : 0 < z.re) :
    ‖digamma z - log z‖ ≤ 1 / (2 * ‖z‖) + 1 / (2 * ‖z‖ ^ 2) := by
  have hz' := norm_pos_of_re_pos hz
  rw [digamma_eq hz, show log z - 1 / (2 * z) + R' z - log z = -(1 / (2 * z)) + R' z by ring]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg, norm_div, norm_one, norm_mul, Complex.norm_ofNat]
  exact add_le_add le_rfl (norm_R'_le hz)

end DBNStirling
