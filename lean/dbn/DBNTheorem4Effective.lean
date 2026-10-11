/-
  DBNTheorem4Effective -- an explicit height `Yeff(c, x₀, ε)` for Dobner's Theorem 4 on the dbn island.

  Programme item 4 of the RH direction note (2026-10-10): make `DBNTheorem4.theorem4` effective.  The
  qualitative proof (`DBNSaddleSum.error_sum_small`) bounds the error series by
      S₁ / y + S₂ e^{-y²/(32c) + π y},   S₁ = C₁ ∑_n T₁(n),  S₂ = C₂ ∑_n T₂(n),
  and then extracts a non-explicit `Y` from the limit `y → ∞`.  Here the last step is replaced by the
  explicit threshold
      Yeff = max {2, 8c, 64πc, 2S₁/ε, 8 √(c · log⁺(2S₂/ε))},
  so that for `|Re s − x₀| ≤ 1` and `Im s ≥ Yeff` the error is `≤ ε`.  The two sums `∑ T₁`, `∑ T₂` are
  first kept as the explicit real constants `T₁sum`, `T₂sum` (Gaussian Dirichlet series, finite by
  `summable_T₁`/`summable_T₂`), then bounded in closed form by domination with `∑ 1/n² = π²/6`
  (`T₁sum_le`, `T₂sum_le`), and `C₁`, `C₂` are evaluated in closed form (`C₁_eq`, `C₂_eq`), giving
  the fully explicit height `Yexp(c, x₀, ε)` of `theorem4_fully_explicit`.  See the accompanying note
  EFFECTIVE_THEOREM4_2026-10-10.md.

  Nothing here is RH; this is a rate for Theorem 4 only.  conjecture1_proved = False.
-/
import Mathlib
import DBNTheorem4

open Complex Filter Topology
open scoped Real

namespace DBNSaddle

/-! ### The explicit constants -/

/-- `∑_{n ≥ 1} T₁(n)`, the near-field weight sum (finite by `summable_T₁`). -/
noncomputable def T₁sum (c x₀ : ℝ) : ℝ := ∑' n : ℕ+, T₁ c x₀ n

/-- `∑_{n ≥ 1} T₂(n)`, the far-field weight sum (finite by `summable_T₂`). -/
noncomputable def T₂sum (c x₀ : ℝ) : ℝ := ∑' n : ℕ+, T₂ c x₀ n

/-- `S₁ = C₁ ∑ T₁`: the coefficient of `1/y` in the error bound. -/
noncomputable def S₁ (c x₀ : ℝ) : ℝ := C₁ c x₀ * T₁sum c x₀

/-- `S₂ = C₂ ∑ T₂`: the coefficient of `e^{-y²/(32c) + πy}` in the error bound. -/
noncomputable def S₂ (c x₀ : ℝ) : ℝ := C₂ c x₀ * T₂sum c x₀

lemma T₁sum_nonneg {c : ℝ} (hc : 0 < c) (x₀ : ℝ) : 0 ≤ T₁sum c x₀ :=
  tsum_nonneg (T₁_nonneg hc x₀)

lemma T₂sum_nonneg {c : ℝ} (hc : 0 < c) (x₀ : ℝ) : 0 ≤ T₂sum c x₀ :=
  tsum_nonneg (T₂_nonneg hc x₀)

lemma S₁_nonneg {c : ℝ} (hc : 0 < c) (x₀ : ℝ) : 0 ≤ S₁ c x₀ :=
  mul_nonneg (C₁_nonneg hc x₀) (T₁sum_nonneg hc x₀)

lemma S₂_nonneg {c : ℝ} (hc : 0 < c) (x₀ : ℝ) : 0 ≤ S₂ c x₀ :=
  mul_nonneg (C₂_nonneg hc x₀) (T₂sum_nonneg hc x₀)

/-- The error bound as an explicit function of the height: `S₁/y + S₂ e^{-y²/(32c) + πy}`. -/
noncomputable def errBound (c x₀ y : ℝ) : ℝ :=
  S₁ c x₀ / y + S₂ c x₀ * Real.exp (-y ^ 2 / (32 * c) + π * y)

/-- **The error series is bounded by `errBound`** on the strip for `Im s ≥ max 2 (8c)`.  This is
`error_sum_small` with the limit step removed. -/
theorem error_sum_le_errBound {c : ℝ} (hc : 0 < c) (x₀ : ℝ) {s : ℂ} (hx : |s.re - x₀| ≤ 1)
    (hy2 : 2 ≤ s.im) (hy8 : 8 * c ≤ s.im) :
    (Summable fun n : ℕ+ => (coef c n : ℂ) * (1 / (n : ℂ) ^ s) * E c (3 - x₀) n s) ∧
    ‖∑' n : ℕ+, (coef c n : ℂ) * (1 / (n : ℂ) ^ s) * E c (3 - x₀) n s‖ ≤ errBound c x₀ s.im := by
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
    _ = errBound c x₀ s.im := by
        unfold errBound S₁ S₂ T₁sum T₂sum
        rw [(((summable_T₁ hc x₀).mul_left _).div_const _).tsum_add
          (((summable_T₂ hc x₀).mul_left _).mul_right _), tsum_div_const, tsum_mul_right,
          tsum_mul_left, tsum_mul_left]

/-! ### The explicit height -/

/-- The explicit height `Yeff(c, x₀, ε) = max {2, 8c, 64πc, 2S₁/ε, 8 √(c log⁺(2S₂/ε))}`. -/
noncomputable def Yeff (c x₀ ε : ℝ) : ℝ :=
  max (max 2 (8 * c)) (max (64 * π * c)
    (max (2 * S₁ c x₀ / ε) (8 * Real.sqrt (c * max 0 (Real.log (2 * S₂ c x₀ / ε))))))

lemma two_le_Yeff (c x₀ ε : ℝ) : 2 ≤ Yeff c x₀ ε :=
  le_max_of_le_left (le_max_left _ _)

lemma eight_mul_le_Yeff (c x₀ ε : ℝ) : 8 * c ≤ Yeff c x₀ ε :=
  le_max_of_le_left (le_max_right _ _)

lemma pi_term_le_Yeff (c x₀ ε : ℝ) : 64 * π * c ≤ Yeff c x₀ ε :=
  le_max_of_le_right (le_max_left _ _)

lemma S₁_term_le_Yeff (c x₀ ε : ℝ) : 2 * S₁ c x₀ / ε ≤ Yeff c x₀ ε :=
  le_max_of_le_right (le_max_of_le_right (le_max_left _ _))

lemma S₂_term_le_Yeff (c x₀ ε : ℝ) :
    8 * Real.sqrt (c * max 0 (Real.log (2 * S₂ c x₀ / ε))) ≤ Yeff c x₀ ε :=
  le_max_of_le_right (le_max_of_le_right (le_max_right _ _))

/-- For `y ≥ Yeff` the bound function is `≤ ε`: the `1/y` term is `≤ ε/2` by `y ≥ 2S₁/ε`, and the
Gaussian term is `≤ ε/2` because `y ≥ 64πc` gives `y²/(32c) − πy ≥ y²/(64c) ≥ log(2S₂/ε)`. -/
theorem errBound_le_of_Yeff_le {c : ℝ} (hc : 0 < c) (x₀ : ℝ) {ε : ℝ} (hε : 0 < ε) {y : ℝ}
    (hY : Yeff c x₀ ε ≤ y) : errBound c x₀ y ≤ ε := by
  have hS₁ := S₁_nonneg hc x₀
  have hS₂ := S₂_nonneg hc x₀
  have hy2 : 2 ≤ y := (two_le_Yeff c x₀ ε).trans hY
  have hy : 0 < y := by linarith
  have hyπ : 64 * π * c ≤ y := (pi_term_le_Yeff c x₀ ε).trans hY
  have hyS₁ : 2 * S₁ c x₀ / ε ≤ y := (S₁_term_le_Yeff c x₀ ε).trans hY
  have hyS₂ : 8 * Real.sqrt (c * max 0 (Real.log (2 * S₂ c x₀ / ε))) ≤ y :=
    (S₂_term_le_Yeff c x₀ ε).trans hY
  -- the `1/y` term
  have h1 : S₁ c x₀ / y ≤ ε / 2 := by
    rw [div_le_iff₀ hy]
    rw [div_le_iff₀ hε] at hyS₁
    linarith
  -- the Gaussian term
  have h2 : S₂ c x₀ * Real.exp (-y ^ 2 / (32 * c) + π * y) ≤ ε / 2 := by
    rcases hS₂.lt_or_eq with hpos | hzero
    · have hq : 0 < 2 * S₂ c x₀ / ε := by positivity
      have hm0 : 0 ≤ c * max 0 (Real.log (2 * S₂ c x₀ / ε)) :=
        mul_nonneg hc.le (le_max_left _ _)
      have hlog : Real.log (2 * S₂ c x₀ / ε) ≤ y ^ 2 / (64 * c) := by
        have hsq : (8 * Real.sqrt (c * max 0 (Real.log (2 * S₂ c x₀ / ε)))) ^ 2 ≤ y ^ 2 := by
          have h0 : 0 ≤ 8 * Real.sqrt (c * max 0 (Real.log (2 * S₂ c x₀ / ε))) := by positivity
          exact pow_le_pow_left₀ h0 hyS₂ 2
        rw [mul_pow, Real.sq_sqrt hm0] at hsq
        have hm : max 0 (Real.log (2 * S₂ c x₀ / ε)) ≤ y ^ 2 / (64 * c) := by
          rw [le_div_iff₀ (by positivity)]
          nlinarith
        exact (le_max_right _ _).trans hm
      have hπy : π * y ≤ y ^ 2 / (64 * c) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [Real.pi_pos]
      have hexp : -y ^ 2 / (32 * c) + π * y ≤ -Real.log (2 * S₂ c x₀ / ε) := by
        have e : -y ^ 2 / (32 * c) = -(y ^ 2 / (64 * c)) - y ^ 2 / (64 * c) := by
          field_simp
          ring
        linarith
      have hS₂ne : S₂ c x₀ ≠ 0 := hpos.ne'
      calc S₂ c x₀ * Real.exp (-y ^ 2 / (32 * c) + π * y)
          ≤ S₂ c x₀ * Real.exp (-Real.log (2 * S₂ c x₀ / ε)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hS₂
        _ = ε / 2 := by
            rw [Real.exp_neg, Real.exp_log hq]
            field_simp
    · rw [← hzero, zero_mul]
      linarith
  unfold errBound
  linarith

/-- **Theorem 4's error series with an explicit height.**  For `|Re s − x₀| ≤ 1` and
`Im s ≥ Yeff c x₀ ε` the error series converges and has norm `≤ ε`. -/
theorem error_sum_small_explicit {c : ℝ} (hc : 0 < c) (x₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ s : ℂ, |s.re - x₀| ≤ 1 → Yeff c x₀ ε ≤ s.im →
      (Summable fun n : ℕ+ => (coef c n : ℂ) * (1 / (n : ℂ) ^ s) * E c (3 - x₀) n s) ∧
      ‖∑' n : ℕ+, (coef c n : ℂ) * (1 / (n : ℂ) ^ s) * E c (3 - x₀) n s‖ ≤ ε := by
  intro s hx hY
  have hy2 : 2 ≤ s.im := (two_le_Yeff c x₀ ε).trans hY
  have hy8 : 8 * c ≤ s.im := (eight_mul_le_Yeff c x₀ ε).trans hY
  obtain ⟨hsum, hle⟩ := error_sum_le_errBound hc x₀ hx hy2 hy8
  exact ⟨hsum, hle.trans (errBound_le_of_Yeff_le hc x₀ hε hY)⟩

/-- **Dobner's Theorem 4 with an explicit height**: the statement of `theorem4` with the
existential `Y` replaced by `Yeff c x₀ ε`. -/
theorem theorem4_explicit {c : ℝ} (hc : 0 < c) (x₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ s : ℂ, |s.re - x₀| ≤ 1 → Yeff c x₀ ε ≤ s.im →
      ‖DBN.H (-c) (-I * (2 * J c (3 - x₀) s - 1)) / γt c (3 - x₀) s - DBNFtZero.F (c / 4) s‖ ≤ ε := by
  intro s hx hY
  have hy2 : 2 ≤ s.im := (two_le_Yeff c x₀ ε).trans hY
  have hy : 0 < s.im := by linarith
  have hxx := abs_le.mp hx
  have hb : 0 < (s + ((3 - x₀ : ℝ) : ℂ)).re := by simp; linarith
  have hb0 : s + ((3 - x₀ : ℝ) : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  have hb1 : s + ((3 - x₀ : ℝ) : ℂ) - 1 ≠ 0 := fun h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  obtain ⟨hsum, hsmall⟩ := error_sum_small_explicit hc x₀ hε s hx hY
  have hxi := xi_J_eq hc hb hb0 hb1 hsum
  have hγ := γt_ne_zero (c := c) hb hb0 hb1
  rw [hxi, mul_div_cancel_left₀ _ hγ, add_sub_cancel_left]
  exact hsmall

/-- The qualitative `theorem4` is recovered by taking `Y = Yeff`. -/
theorem theorem4_of_explicit {c : ℝ} (hc : 0 < c) (x₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Y : ℝ, ∀ s : ℂ, |s.re - x₀| ≤ 1 → Y ≤ s.im →
      ‖DBN.H (-c) (-I * (2 * J c (3 - x₀) s - 1)) / γt c (3 - x₀) s - DBNFtZero.F (c / 4) s‖ ≤ ε :=
  ⟨Yeff c x₀ ε, theorem4_explicit hc x₀ hε⟩


/-! ### Closed-form bounds for the two sums

`T₁(n) ≤ e^{8(3−x₀+c)²/(3c)} / n²` and `T₂(n) ≤ 4 e^{96(3−x₀+c/2)²/(59c)} / n²`, by `(h²+h+1) ≤ e^{2h}`,
`(2+h)² ≤ 4e^{h}` and completing the square in `L = log n`; then `∑ 1/n² = π²/6`. -/

/-- Completing the square: `−αL² + βL ≤ β²/(4α)` for `α > 0`. -/
lemma neg_sq_add_le_sq_div {α : ℝ} (hα : 0 < α) (β L : ℝ) :
    -α * L ^ 2 + β * L ≤ β ^ 2 / (4 * α) := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (2 * α * L - β)]

/-- `∑_{n ≥ 1} 1/n² = π²/6`, indexed by `ℕ+`. -/
lemma hasSum_pnat_inv_sq : HasSum (fun n : ℕ+ => 1 / (n : ℝ) ^ 2) (π ^ 2 / 6) := by
  refine (hasSum_pnat_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2)).mpr ?_
  simpa using hasSum_zeta_two

lemma T₁_le {c : ℝ} (hc : 0 < c) (x₀ : ℝ) (n : ℕ+) :
    T₁ c x₀ n ≤ Real.exp (8 * (3 - x₀ + c) ^ 2 / (3 * c)) * (1 / (n : ℝ) ^ 2) := by
  have hc0 : c ≠ 0 := hc.ne'
  have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hh0 : 0 ≤ hh c n := hh_nonneg hc n
  have hhL : hh c n = c / 2 * Real.log (n : ℝ) := rfl
  have hpoly : (hh c n) ^ 2 + hh c n + 1 ≤ Real.exp (2 * hh c n) := by
    have h1 : hh c n + 1 ≤ Real.exp (hh c n) := Real.add_one_le_exp _
    calc (hh c n) ^ 2 + hh c n + 1 ≤ (hh c n + 1) ^ 2 := by nlinarith
      _ ≤ (Real.exp (hh c n)) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
      _ = Real.exp (2 * hh c n) := by rw [sq, ← Real.exp_add, two_mul]
  have hn2 : (1 : ℝ) / (n : ℝ) ^ 2 = Real.exp (-(2 * Real.log (n : ℝ))) := by
    rw [Real.exp_neg, one_div, two_mul, Real.exp_add, Real.exp_log hn, sq]
  have hrpow : (n : ℝ) ^ (1 - x₀) = Real.exp (Real.log (n : ℝ) * (1 - x₀)) :=
    Real.rpow_def_of_pos hn _
  calc T₁ c x₀ n
      = ((hh c n) ^ 2 + hh c n + 1) * Real.exp (-(3 / (8 * c)) * (hh c n) ^ 2) *
          Real.exp (Real.log (n : ℝ) * (1 - x₀)) := by rw [T₁, hrpow]
    _ ≤ Real.exp (2 * hh c n) * Real.exp (-(3 / (8 * c)) * (hh c n) ^ 2) *
          Real.exp (Real.log (n : ℝ) * (1 - x₀)) := by gcongr
    _ = Real.exp (-(3 * c / 32) * (Real.log (n : ℝ)) ^ 2 + (3 - x₀ + c) * Real.log (n : ℝ) +
          -(2 * Real.log (n : ℝ))) := by
        rw [← Real.exp_add, ← Real.exp_add, hhL]
        congr 1
        field_simp
        ring
    _ ≤ Real.exp ((3 - x₀ + c) ^ 2 / (4 * (3 * c / 32)) + -(2 * Real.log (n : ℝ))) := by
        gcongr
        exact neg_sq_add_le_sq_div (by positivity) _ _
    _ = Real.exp (8 * (3 - x₀ + c) ^ 2 / (3 * c)) * (1 / (n : ℝ) ^ 2) := by
        rw [hn2, ← Real.exp_add]
        congr 1
        field_simp
        ring

lemma T₂_le {c : ℝ} (hc : 0 < c) (x₀ : ℝ) (n : ℕ+) :
    T₂ c x₀ n ≤ 4 * Real.exp (96 * (3 - x₀ + c / 2) ^ 2 / (59 * c)) * (1 / (n : ℝ) ^ 2) := by
  have hc0 : c ≠ 0 := hc.ne'
  have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hh0 : 0 ≤ hh c n := hh_nonneg hc n
  have hhL : hh c n = c / 2 * Real.log (n : ℝ) := rfl
  have hpoly : (2 + hh c n) ^ 2 ≤ 4 * Real.exp (hh c n) := by
    have h1 : hh c n / 2 + 1 ≤ Real.exp (hh c n / 2) := Real.add_one_le_exp _
    calc (2 + hh c n) ^ 2 = 4 * (hh c n / 2 + 1) ^ 2 := by ring
      _ ≤ 4 * (Real.exp (hh c n / 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) h1 2) (by norm_num)
      _ = 4 * Real.exp (hh c n) := by rw [sq, ← Real.exp_add, add_halves]
  have hn2 : (1 : ℝ) / (n : ℝ) ^ 2 = Real.exp (-(2 * Real.log (n : ℝ))) := by
    rw [Real.exp_neg, one_div, two_mul, Real.exp_add, Real.exp_log hn, sq]
  have hrpow : (n : ℝ) ^ (1 - x₀) = Real.exp (Real.log (n : ℝ) * (1 - x₀)) :=
    Real.rpow_def_of_pos hn _
  calc T₂ c x₀ n
      = (2 + hh c n) ^ 2 * Real.exp (-(59 / (96 * c)) * (hh c n) ^ 2) *
          Real.exp (Real.log (n : ℝ) * (1 - x₀)) := by rw [T₂, hrpow]
    _ ≤ 4 * Real.exp (hh c n) * Real.exp (-(59 / (96 * c)) * (hh c n) ^ 2) *
          Real.exp (Real.log (n : ℝ) * (1 - x₀)) := by gcongr
    _ = 4 * Real.exp (-(59 * c / 384) * (Real.log (n : ℝ)) ^ 2 + (3 - x₀ + c / 2) * Real.log (n : ℝ) +
          -(2 * Real.log (n : ℝ))) := by
        rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add, hhL]
        congr 2
        field_simp
        ring
    _ ≤ 4 * Real.exp ((3 - x₀ + c / 2) ^ 2 / (4 * (59 * c / 384)) + -(2 * Real.log (n : ℝ))) := by
        gcongr
        exact neg_sq_add_le_sq_div (by positivity) _ _
    _ = 4 * Real.exp (96 * (3 - x₀ + c / 2) ^ 2 / (59 * c)) * (1 / (n : ℝ) ^ 2) := by
        rw [hn2, mul_assoc, ← Real.exp_add]
        congr 2
        field_simp
        ring

theorem T₁sum_le {c : ℝ} (hc : 0 < c) (x₀ : ℝ) :
    T₁sum c x₀ ≤ Real.exp (8 * (3 - x₀ + c) ^ 2 / (3 * c)) * (π ^ 2 / 6) := by
  have hz : Summable (fun n : ℕ+ => 1 / (n : ℝ) ^ 2) := hasSum_pnat_inv_sq.summable
  calc T₁sum c x₀
      ≤ ∑' n : ℕ+, Real.exp (8 * (3 - x₀ + c) ^ 2 / (3 * c)) * (1 / (n : ℝ) ^ 2) :=
        (summable_T₁ hc x₀).tsum_le_tsum (T₁_le hc x₀) (hz.mul_left _)
    _ = _ := by rw [tsum_mul_left, hasSum_pnat_inv_sq.tsum_eq]

theorem T₂sum_le {c : ℝ} (hc : 0 < c) (x₀ : ℝ) :
    T₂sum c x₀ ≤ 4 * Real.exp (96 * (3 - x₀ + c / 2) ^ 2 / (59 * c)) * (π ^ 2 / 6) := by
  have hz : Summable (fun n : ℕ+ => 1 / (n : ℝ) ^ 2) := hasSum_pnat_inv_sq.summable
  calc T₂sum c x₀
      ≤ ∑' n : ℕ+, 4 * Real.exp (96 * (3 - x₀ + c / 2) ^ 2 / (59 * c)) * (1 / (n : ℝ) ^ 2) :=
        (summable_T₂ hc x₀).tsum_le_tsum (T₂_le hc x₀) (hz.mul_left _)
    _ = _ := by rw [tsum_mul_left, hasSum_pnat_inv_sq.tsum_eq]

/-! ### The constants `C₁`, `C₂` in closed form -/

/-- `C₁ = 96 e^{(3−x₀)²/c + 7/(16c) + 4c + 1}`. -/
theorem C₁_eq {c : ℝ} (hc : 0 < c) (x₀ : ℝ) :
    C₁ c x₀ = 96 * Real.exp ((3 - x₀) ^ 2 / c + 7 / (16 * c) + 4 * c + 1) := by
  have hc0 : c ≠ 0 := hc.ne'
  have hπc : 0 < π * c := by positivity
  have hs : Real.sqrt (π / ((1 / (2 * c)) / 2)) = 2 * Real.sqrt (π * c) := by
    rw [show π / ((1 / (2 * c)) / 2) = 2 ^ 2 * (π * c) by field_simp,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hsne : Real.sqrt (π * c) ≠ 0 := (Real.sqrt_pos.mpr hπc).ne'
  have he : (1 / (4 * c) + 2) ^ 2 / (2 * (1 / (2 * c))) = 4 * c + 1 + 1 / (16 * c) := by
    field_simp
    ring
  rw [C₁, Ig, hs, he]
  have hprod : Real.exp ((3 - x₀) ^ 2 / c) / Real.sqrt (π * c) *
      (48 * Real.exp (3 / (8 * c)) * (Real.exp (4 * c + 1 + 1 / (16 * c)) * (2 * Real.sqrt (π * c)))) =
      96 * (Real.exp ((3 - x₀) ^ 2 / c) * Real.exp (3 / (8 * c)) *
        Real.exp (4 * c + 1 + 1 / (16 * c))) := by
    field_simp
    ring
  have hsum : (3 - x₀) ^ 2 / c + 3 / (8 * c) + (4 * c + 1 + 1 / (16 * c)) =
      (3 - x₀) ^ 2 / c + 7 / (16 * c) + 4 * c + 1 := by
    field_simp
    ring
  rw [hprod, ← Real.exp_add, ← Real.exp_add, hsum]

/-- `C₂ = 3 √(8/3) e^{(3−x₀)²/c + 1 + 15/(64c) + (4c/3)(π+2)²}`. -/
theorem C₂_eq {c : ℝ} (hc : 0 < c) (x₀ : ℝ) :
    C₂ c x₀ = 3 * Real.sqrt (8 / 3) *
      Real.exp ((3 - x₀) ^ 2 / c + 1 + 15 / (64 * c) + (4 * c / 3) * (π + 2) ^ 2) := by
  have hc0 : c ≠ 0 := hc.ne'
  have hπc : 0 < π * c := by positivity
  have hs : Real.sqrt (π / ((3 / (4 * c)) / 2)) = Real.sqrt (8 / 3) * Real.sqrt (π * c) := by
    rw [← Real.sqrt_mul (by norm_num)]
    congr 1
    field_simp
    norm_num
  have hsne : Real.sqrt (π * c) ≠ 0 := (Real.sqrt_pos.mpr hπc).ne'
  rw [C₂, D₂, hs]
  have hprod : Real.exp ((3 - x₀) ^ 2 / c) / Real.sqrt (π * c) *
      (3 * Real.exp (1 + 9 / (64 * c) + (4 * c / 3) * (π + 2) ^ 2 + 3 / (32 * c)) *
        (Real.sqrt (8 / 3) * Real.sqrt (π * c))) =
      3 * Real.sqrt (8 / 3) * (Real.exp ((3 - x₀) ^ 2 / c) *
        Real.exp (1 + 9 / (64 * c) + (4 * c / 3) * (π + 2) ^ 2 + 3 / (32 * c))) := by
    field_simp
  have hsum : (3 - x₀) ^ 2 / c + (1 + 9 / (64 * c) + (4 * c / 3) * (π + 2) ^ 2 + 3 / (32 * c)) =
      (3 - x₀) ^ 2 / c + 1 + 15 / (64 * c) + (4 * c / 3) * (π + 2) ^ 2 := by
    field_simp
    ring
  rw [hprod, ← Real.exp_add, hsum]

/-! ### The fully explicit height -/

/-- Closed-form majorant of `S₁ = C₁ ∑ T₁`. -/
noncomputable def S₁b (c x₀ : ℝ) : ℝ :=
  96 * Real.exp ((3 - x₀) ^ 2 / c + 7 / (16 * c) + 4 * c + 1) *
    (Real.exp (8 * (3 - x₀ + c) ^ 2 / (3 * c)) * (π ^ 2 / 6))

/-- Closed-form majorant of `S₂ = C₂ ∑ T₂`. -/
noncomputable def S₂b (c x₀ : ℝ) : ℝ :=
  3 * Real.sqrt (8 / 3) * Real.exp ((3 - x₀) ^ 2 / c + 1 + 15 / (64 * c) + (4 * c / 3) * (π + 2) ^ 2) *
    (4 * Real.exp (96 * (3 - x₀ + c / 2) ^ 2 / (59 * c)) * (π ^ 2 / 6))

theorem S₁_le_S₁b {c : ℝ} (hc : 0 < c) (x₀ : ℝ) : S₁ c x₀ ≤ S₁b c x₀ := by
  unfold S₁ S₁b
  rw [C₁_eq hc]
  exact mul_le_mul_of_nonneg_left (T₁sum_le hc x₀) (by positivity)

theorem S₂_le_S₂b {c : ℝ} (hc : 0 < c) (x₀ : ℝ) : S₂ c x₀ ≤ S₂b c x₀ := by
  unfold S₂ S₂b
  rw [C₂_eq hc]
  exact mul_le_mul_of_nonneg_left (T₂sum_le hc x₀) (by positivity)

/-- The fully explicit height: `Yeff` with `S₁`, `S₂` replaced by their closed-form majorants. -/
noncomputable def Yexp (c x₀ ε : ℝ) : ℝ :=
  max (max 2 (8 * c)) (max (64 * π * c)
    (max (2 * S₁b c x₀ / ε) (8 * Real.sqrt (c * max 0 (Real.log (2 * S₂b c x₀ / ε))))))

lemma Yeff_le_Yexp {c : ℝ} (hc : 0 < c) (x₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Yeff c x₀ ε ≤ Yexp c x₀ ε := by
  have h1 : 2 * S₁ c x₀ / ε ≤ 2 * S₁b c x₀ / ε :=
    div_le_div_of_nonneg_right (by linarith [S₁_le_S₁b hc x₀]) hε.le
  have hlog : max 0 (Real.log (2 * S₂ c x₀ / ε)) ≤ max 0 (Real.log (2 * S₂b c x₀ / ε)) := by
    rcases (S₂_nonneg hc x₀).lt_or_eq with hpos | hzero
    · refine max_le_max le_rfl (Real.log_le_log (by positivity) ?_)
      exact div_le_div_of_nonneg_right (by linarith [S₂_le_S₂b hc x₀]) hε.le
    · simp [← hzero]
  have h2 : 8 * Real.sqrt (c * max 0 (Real.log (2 * S₂ c x₀ / ε))) ≤
      8 * Real.sqrt (c * max 0 (Real.log (2 * S₂b c x₀ / ε))) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hlog hc.le)) (by norm_num)
  unfold Yeff Yexp
  exact max_le_max le_rfl (max_le_max le_rfl (max_le_max h1 h2))

/-- **Dobner's Theorem 4 with a fully explicit height** `Yexp(c, x₀, ε)`. -/
theorem theorem4_fully_explicit {c : ℝ} (hc : 0 < c) (x₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ s : ℂ, |s.re - x₀| ≤ 1 → Yexp c x₀ ε ≤ s.im →
      ‖DBN.H (-c) (-I * (2 * J c (3 - x₀) s - 1)) / γt c (3 - x₀) s - DBNFtZero.F (c / 4) s‖ ≤ ε :=
  fun s hx hY => theorem4_explicit hc x₀ hε s hx ((Yeff_le_Yexp hc x₀ hε).trans hY)

end DBNSaddle

