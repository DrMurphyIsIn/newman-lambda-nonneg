/-
  DBNFtZero -- the Gaussian-weighted Dirichlet series F has a zero.

  Step 2 of the Lambda >= 0 (Newman's conjecture) formalization following Dobner
  (arXiv:2005.05142, Lemma 3).  See telperion/docs/NEWMAN_LAMBDA_NONNEG_SCOPING_2026-10-10.md.

  For `c > 0` let `a n = exp (-c (log n)^2)` and `F c s = ∑ a n / n^s` (Dobner's `F_t` is
  `c = |t|/4`).  The series converges absolutely for every `s`, so `F c` is entire, of finite
  order (`‖F c s‖ < exp (‖s‖^3)` for `‖s‖` large).  Statement: `F c` has a zero.

  Proof.  If `F c` had no zero, the Hadamard theorem for zero-free entire functions of finite
  order (`Hadamard.entire_no_zeros_is_exp_polynomial`, LiCriterion package, already a dependency
  of this island) gives `F c = exp ∘ g` with `g` a polynomial, hence `F' = F * g'`.  On the real
  axis `F c σ ≥ 1` (positive terms, leading term `1`) while `F' σ = -∑ log n * a n / n^σ` is
  `O(2^(-σ))`; so the polynomial `g'` tends to `0` along the real axis, so it is the zero
  polynomial, so `F'` vanishes identically.  But `F' 0 = -∑ log n * a n < 0`.

  Nothing here is RH.  conjecture1_proved = False.
-/
import Mathlib
import Hadamard.Basic

open Complex Filter Topology LSeries

namespace DBNFtZero

/-- The Gaussian Dirichlet coefficients `a n = exp (-c (log n)^2)`. -/
noncomputable def gaussCoeff (c : ℝ) (n : ℕ) : ℂ := ((Real.exp (-c * (Real.log n) ^ 2) : ℝ) : ℂ)

/-- `F c s = ∑' n, a n / n^s`; Dobner's `F_t` is `F (|t|/4)`. -/
noncomputable def F (c : ℝ) (s : ℂ) : ℂ := LSeries (gaussCoeff c) s

/-! ### Terms -/

lemma norm_term_eq (c : ℝ) (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    ‖term (gaussCoeff c) s n‖ = Real.exp (-c * (Real.log n) ^ 2 - s.re * Real.log n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [LSeries.norm_term_eq, ite_eq_right hn, gaussCoeff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Real.rpow_def_of_pos hn', ← Real.exp_sub]
  congr 1
  ring

/-- On the real axis every term is a nonnegative real number: it equals its own norm. -/
lemma term_real (c : ℝ) (σ : ℝ) (n : ℕ) :
    term (gaussCoeff c) (σ : ℂ) n = ((‖term (gaussCoeff c) (σ : ℂ) n‖ : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [term_zero]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [LSeries.norm_term_eq, ite_eq_right hn, term_of_ne_zero hn, gaussCoeff, Complex.ofReal_re,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Complex.ofReal_div,
      Complex.ofReal_cpow hn'.le]
    simp

/-! ### Absolute convergence everywhere -/

/-- `∑ a n / n^s` converges absolutely for every `s` (compare with `n^(-2)` eventually). -/
lemma lseriesSummable {c : ℝ} (hc : 0 < c) (s : ℂ) : LSeriesSummable (gaussCoeff c) s := by
  refine Summable.of_norm_bounded_eventually_nat (Real.summable_nat_pow_inv.mpr one_lt_two) ?_
  obtain ⟨N, hN⟩ := exists_nat_ge (Real.exp ((2 + |s.re|) / c))
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  rw [norm_term_eq c s hn0]
  have hL : (2 + |s.re|) / c ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hnpos]
    calc Real.exp ((2 + |s.re|) / c) ≤ N := hN
      _ ≤ n := by exact_mod_cast (show N ≤ n by omega)
  have hL0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hcL : 2 + |s.re| ≤ c * Real.log n := by
    rwa [div_le_iff₀ hc, mul_comm] at hL
  have h2 : ((n : ℝ) ^ 2)⁻¹ = Real.exp (Real.log n * (-2)) := by
    rw [← Real.rpow_def_of_pos hnpos, Real.rpow_neg hnpos.le, Real.rpow_two]
  rw [h2, Real.exp_le_exp]
  nlinarith [mul_le_mul_of_nonneg_right hcL hL0, neg_abs_le s.re]

lemma summable_norm_term {c : ℝ} (hc : 0 < c) (s : ℂ) :
    Summable fun n => ‖term (gaussCoeff c) s n‖ :=
  (lseriesSummable hc s).norm

lemma abscissa_lt {c : ℝ} (hc : 0 < c) (s : ℂ) :
    abscissaOfAbsConv (gaussCoeff c) < s.re := by
  calc abscissaOfAbsConv (gaussCoeff c) ≤ ((s - 1).re : EReal) :=
        (lseriesSummable hc (s - 1)).abscissaOfAbsConv_le
    _ < s.re := by
        rw [Complex.sub_re, Complex.one_re]
        exact EReal.coe_lt_coe_iff.mpr (by linarith)

lemma hasDerivAt_F {c : ℝ} (hc : 0 < c) (s : ℂ) :
    HasDerivAt (F c) (-LSeries (logMul (gaussCoeff c)) s) s :=
  LSeries_hasDerivAt (abscissa_lt hc s)

lemma differentiable_F {c : ℝ} (hc : 0 < c) : Differentiable ℂ (F c) :=
  fun s => (hasDerivAt_F hc s).differentiableAt

/-! ### Growth: finite order -/

/-- `‖F c s‖ ≤ exp (‖s‖^2 / (2c)) * K` with `K = ∑ exp (-(c/2) (log n)^2)`, from
`-c L^2 - σ L ≤ ‖s‖^2/(2c) - (c/2) L^2` (complete the square in `L`). -/
lemma norm_F_le {c : ℝ} (hc : 0 < c) (s : ℂ) :
    ‖F c s‖ ≤ Real.exp (‖s‖ ^ 2 / (2 * c)) * ∑' n, ‖term (gaussCoeff (c / 2)) 0 n‖ := by
  have hsum := summable_norm_term hc s
  have hsum2 := summable_norm_term (half_pos hc) 0
  refine (norm_tsum_le_tsum_norm hsum).trans ?_
  rw [← tsum_mul_left]
  refine hsum.tsum_le_tsum (fun n => ?_) (hsum2.mul_left _)
  rcases eq_or_ne n 0 with rfl | hn
  · simp [term_zero]
  · rw [norm_term_eq c s hn, norm_term_eq (c / 2) 0 hn, ← Real.exp_add, Real.exp_le_exp,
      Complex.zero_re, zero_mul, sub_zero]
    have hre : s.re ^ 2 ≤ ‖s‖ ^ 2 := by
      have h := Complex.abs_re_le_norm s
      calc s.re ^ 2 = |s.re| ^ 2 := (sq_abs _).symm
        _ ≤ ‖s‖ ^ 2 := by gcongr
    have key : 0 ≤ (c * Real.log n + s.re) ^ 2 := sq_nonneg _
    have h2c : (0 : ℝ) < 2 * c := by positivity
    have : -(c / 2) * (Real.log n) ^ 2 - s.re * Real.log n ≤ ‖s‖ ^ 2 / (2 * c) := by
      rw [le_div_iff₀ h2c]
      nlinarith [key, hre]
    linarith

lemma one_le_K {c : ℝ} (hc : 0 < c) : 1 ≤ ∑' n, ‖term (gaussCoeff (c / 2)) 0 n‖ := by
  have hs := summable_norm_term (half_pos hc) 0
  have h1 : ‖term (gaussCoeff (c / 2)) 0 1‖ = 1 := by
    rw [norm_term_eq (c / 2) 0 one_ne_zero]; simp
  calc (1 : ℝ) = ‖term (gaussCoeff (c / 2)) 0 1‖ := h1.symm
    _ ≤ _ := hs.le_tsum 1 fun _ _ => norm_nonneg _

/-- `F c` is entire of finite order: `‖F c z‖ < exp (‖z‖^3)` for `‖z‖` large. -/
theorem hasFiniteOrder_F {c : ℝ} (hc : 0 < c) : Hadamard.hasFiniteOrder (F c) := by
  set K := ∑' n, ‖term (gaussCoeff (c / 2)) 0 n‖ with hK
  have hK1 : 1 ≤ K := one_le_K hc
  have hKpos : 0 < K := by linarith
  refine ⟨differentiable_F hc, 3, max 1 (max (1 / (2 * c) + 1) (Real.log K + 1)), fun z hz => ?_⟩
  have hr1 : 1 ≤ ‖z‖ := le_trans (le_max_left _ _) hz
  have hru : 1 / (2 * c) + 1 ≤ ‖z‖ := le_trans (le_max_of_le_right (le_max_left _ _)) hz
  have hrK : Real.log K + 1 ≤ ‖z‖ := le_trans (le_max_of_le_right (le_max_right _ _)) hz
  refine (norm_F_le hc z).trans_lt ?_
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc Real.exp (‖z‖ ^ 2 / (2 * c)) * K
      = Real.exp (‖z‖ ^ 2 / (2 * c) + Real.log K) := by
        rw [Real.exp_add, Real.exp_log hKpos]
    _ < Real.exp (‖z‖ ^ 3) := by
        rw [Real.exp_lt_exp]
        set r := ‖z‖
        have hu : r ^ 2 / (2 * c) = r ^ 2 * (1 / (2 * c)) := by ring
        have h1 : r ^ 2 * 1 ≤ r ^ 2 * (r - 1 / (2 * c)) :=
          mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg r)
        have h2 : r * 1 ≤ r * r := mul_le_mul_of_nonneg_left hr1 (by linarith)
        nlinarith [h1, h2, hu, hrK]

/-! ### The series on the real axis -/

/-- `F c σ ≥ 1` for real `σ`: all terms are nonnegative and the `n = 1` term is `1`. -/
lemma one_le_norm_F {c : ℝ} (hc : 0 < c) (σ : ℝ) : 1 ≤ ‖F c σ‖ := by
  have hs := summable_norm_term hc (σ : ℂ)
  have hF : F c σ = ((∑' n, ‖term (gaussCoeff c) (σ : ℂ) n‖ : ℝ) : ℂ) := by
    unfold F LSeries
    rw [Complex.ofReal_tsum]
    exact tsum_congr (term_real c σ)
  have h1 : ‖term (gaussCoeff c) (σ : ℂ) 1‖ = 1 := by
    rw [norm_term_eq c σ one_ne_zero]; simp
  rw [hF, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]
  calc (1 : ℝ) = ‖term (gaussCoeff c) (σ : ℂ) 1‖ := h1.symm
    _ ≤ _ := hs.le_tsum 1 fun _ _ => norm_nonneg _

/-- The derivative series `∑ log n * a n / n^σ` is `O(2^(-σ))` for `σ ≥ 0`. -/
lemma norm_logSeries_le {c : ℝ} (hc : 0 < c) {σ : ℝ} (hσ : 0 ≤ σ) :
    ‖LSeries (logMul (gaussCoeff c)) σ‖ ≤
      (2 : ℝ) ^ (-σ) * ∑' n, ‖term (logMul (gaussCoeff c)) 0 n‖ := by
  have hs : Summable fun n => ‖term (logMul (gaussCoeff c)) (σ : ℂ) n‖ :=
    (LSeriesSummable_logMul_of_lt_re (abscissa_lt hc σ)).norm
  have h0 : Summable fun n => ‖term (logMul (gaussCoeff c)) 0 n‖ :=
    (LSeriesSummable_logMul_of_lt_re (abscissa_lt hc 0)).norm
  refine (norm_tsum_le_tsum_norm hs).trans ?_
  rw [← tsum_mul_left]
  refine hs.tsum_le_tsum (fun n => ?_) (h0.mul_left _)
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simp
    · simp [LSeries.logMul]
  · have hn0 : n ≠ 0 := by omega
    rw [ite_eq_right hn0, ite_eq_right hn0, Complex.ofReal_re, Complex.zero_re, Real.rpow_zero, div_one,
      Real.rpow_neg zero_le_two, ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (Real.rpow_pos_of_pos two_pos σ)
      (Real.rpow_le_rpow zero_le_two (by exact_mod_cast hn) hσ)

/-- `F' 0 = -∑ log n * a n ≠ 0`: the `n = 2` term is positive and no term is negative. -/
lemma logSeries_zero_ne_zero {c : ℝ} (hc : 0 < c) : LSeries (logMul (gaussCoeff c)) 0 ≠ 0 := by
  have hterm : ∀ n, term (logMul (gaussCoeff c)) 0 n =
      ((Real.log n * Real.exp (-c * (Real.log n) ^ 2) : ℝ) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [term_zero]
    · rw [term_of_ne_zero hn, cpow_zero, div_one, logMul, gaussCoeff, Complex.ofReal_mul,
        Complex.natCast_log]
  have hsumC : Summable (term (logMul (gaussCoeff c)) 0) :=
    LSeriesSummable_logMul_of_lt_re (abscissa_lt hc 0)
  have hsumR : Summable fun n : ℕ => Real.log n * Real.exp (-c * (Real.log n) ^ 2) :=
    Complex.summable_ofReal.mp ((summable_congr hterm).mp hsumC)
  have hpos : 0 < ∑' n : ℕ, Real.log n * Real.exp (-c * (Real.log n) ^ 2) := by
    refine hsumR.tsum_pos (fun n => ?_) 2 ?_
    · rcases eq_or_ne n 0 with rfl | hn
      · simp
      · exact mul_nonneg (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn))
          (Real.exp_pos _).le
    · exact mul_pos (Real.log_pos (by norm_num)) (Real.exp_pos _)
  unfold LSeries
  rw [tsum_congr hterm, ← Complex.ofReal_tsum]
  exact_mod_cast hpos.ne'

/-! ### The theorem -/

/-- **Dobner, Lemma 3 (qualitative).**  For every `c > 0` the entire function
`F c s = ∑ exp (-c (log n)^2) n^(-s)` has a zero. -/
theorem exists_zero {c : ℝ} (hc : 0 < c) : ∃ s : ℂ, F c s = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨g, hg, -⟩ := Hadamard.entire_no_zeros_is_exp_polynomial (F c) (Hadamard.order (F c))
    (hasFiniteOrder_F hc) rfl hne
  set p := Polynomial.derivative g with hp
  -- F' = F * g' everywhere
  have hderiv : ∀ s, -LSeries (logMul (gaussCoeff c)) s = F c s * p.eval s := by
    intro s
    have h1 : HasDerivAt (F c) (-LSeries (logMul (gaussCoeff c)) s) s := hasDerivAt_F hc s
    have h2 : HasDerivAt (fun z => Complex.exp (g.eval z))
        (Complex.exp (g.eval s) * p.eval s) s := (g.hasDerivAt s).cexp
    have hfun : (fun z => Complex.exp (g.eval z)) = F c := funext fun z => (hg z).symm
    rw [hfun, ← hg s] at h2
    exact h1.unique h2
  set K₁ := ∑' n, ‖term (logMul (gaussCoeff c)) 0 n‖ with hK₁
  -- g' is O(2^(-σ)) on the positive real axis
  have hbound : ∀ σ : ℝ, 0 ≤ σ → ‖p.eval (σ : ℂ)‖ ≤ (2 : ℝ) ^ (-σ) * K₁ := by
    intro σ hσ
    have h := hderiv σ
    have h1 := one_le_norm_F hc σ
    have h2 := norm_logSeries_le hc hσ
    rw [← norm_neg, h, norm_mul] at h2
    calc ‖p.eval (σ : ℂ)‖ = 1 * ‖p.eval (σ : ℂ)‖ := (one_mul _).symm
      _ ≤ ‖F c σ‖ * ‖p.eval (σ : ℂ)‖ := by gcongr
      _ ≤ _ := h2
  have hlim : Tendsto (fun σ : ℝ => (2 : ℝ) ^ (-σ) * K₁) atTop (𝓝 0) := by
    have h2 : Tendsto (fun σ : ℝ => (2 : ℝ) ^ (-σ)) atTop (𝓝 0) := by
      have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.atTop_mul_const (Real.log_pos one_lt_two))
      refine h.congr fun σ => ?_
      simp only [Function.comp, id]
      rw [Real.rpow_def_of_pos two_pos]
      ring_nf
    simpa using h2.mul_const K₁
  -- so g' has degree ≤ 0
  have hdeg : p.degree ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have hT : Tendsto (fun σ : ℝ => ‖p.eval (σ : ℂ)‖) atTop atTop :=
      p.tendsto_norm_atTop hpos (z := fun σ : ℝ => (σ : ℂ))
        (by simpa [Complex.norm_real] using tendsto_abs_atTop_atTop)
    have hT0 : Tendsto (fun σ : ℝ => ‖p.eval (σ : ℂ)‖) atTop (𝓝 0) :=
      squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
        (eventually_atTop.mpr ⟨0, hbound⟩) hlim
    exact hT.not_tendsto (disjoint_nhds_atTop (0 : ℝ)).symm hT0
  -- so g' is a constant, and the constant is 0
  obtain ⟨b, hb⟩ : ∃ b, p = Polynomial.C b := ⟨_, Polynomial.eq_C_of_degree_le_zero hdeg⟩
  have hb0 : b = 0 := by
    have hbnd : ∀ᶠ σ : ℝ in atTop, ‖b‖ ≤ (2 : ℝ) ^ (-σ) * K₁ :=
      eventually_atTop.mpr ⟨0, fun σ hσ => by simpa [hb] using hbound σ hσ⟩
    have : ‖b‖ ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim hbnd
    simpa using this
  -- hence F' ≡ 0, contradicting F' 0 ≠ 0
  have hp0 : p = 0 := by rw [hb, hb0, map_zero]
  have h0 := hderiv 0
  rw [hp0, Polynomial.eval_zero, mul_zero, neg_eq_zero] at h0
  exact logSeries_zero_ne_zero hc h0

end DBNFtZero
