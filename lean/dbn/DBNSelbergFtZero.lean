/-
  DBNSelbergFtZero -- the Gaussian-weighted Dirichlet series of an extended-Selberg element has
  zeros at every height.

  Generalises DBNFtZero and DBNFtZeroHigh (the case `a n = 1` of ζ) to the coefficients
  `a : ℕ → ℂ` of an abstract `F : ExtSelbergData` (DBNSelbergData).  For `c > 0`
  `F_t(s) = ∑ a(n) e^{-c log² n} n^{-s}` (`ExtSelbergData.Ft c`).  See
  telperion/docs/SELBERG_NEWMAN_DESIGN_2026-10-10.md, row "DBNFtZero, DBNFtZeroHigh".

  * `lseriesSummable_Ft`: the series converges absolutely everywhere, by comparison with
    `∑ ‖a(n)‖ n^{-2}` (field `summable` at `s = 2`), since
    `e^{-c log² n} n^{2 - Re s} ≤ exp ((2 - Re s)² / (4c))`.
  * `hasFiniteOrder_Ft`: `‖F_t(z)‖ ≤ (∑ ‖a(n)‖ n^{-2}) exp ((2 + ‖z‖)² / (4c)) < exp (‖z‖³)`.
  * `exists_zero_Ft`: if `F_t` had no zero, Hadamard (`entire_no_zeros_is_exp_polynomial`) gives
    `F_t = exp ∘ g` with `g` a polynomial, so `F_t' = F_t g'`.  Along the real axis `F_t(σ) → 1`
    (as `a 1 = 1`) and `F_t'(σ) → 0`, so the polynomial `g'` tends to `0`, so `g' = 0`, so
    `F_t' ≡ 0`.  But for the least `n₀ ≥ 2` with `a(n₀) ≠ 0`,
    `n₀^σ F_t'(σ) → -a(n₀) log n₀ e^{-c log² n₀} ≠ 0` (dominated convergence of the tail).
    No uniqueness theorem for Dirichlet coefficients is used.
  * `exists_zero_im_ge_Ft`: zeros of arbitrarily large imaginary part, from Bohr's shifts
    (DBNBohr, already general) and the zero-free form of Hurwitz (DBNHurwitz), exactly as in
    DBNFtZeroHigh.

  Nothing here is RH.  conjecture1_proved = False.
-/
import Mathlib
import DBNSelbergData
import DBNFtZero
import DBNFtZeroHigh
import DBNBohr
import DBNHurwitz
import Hadamard.Basic

open Complex Filter Topology LSeries

namespace DBNSelberg

/-! ### A general limit along the real axis

For an everywhere (here: at `s = 2`) absolutely convergent Dirichlet series whose coefficients
vanish below `m`, `m^σ ∑ b(n) n^{-σ} → b(m)` as `σ → +∞`.  Used with `m = 1` for `F_t → 1`,
`F_t' → 0`, and with `m = n₀` for the final contradiction. -/

lemma norm_rpow_mul_term (b : ℕ → ℂ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (σ : ℝ) :
    ‖(((m : ℝ) ^ σ : ℝ) : ℂ) * term b (σ : ℂ) n‖ = ‖b n‖ * ((m : ℝ) / n) ^ σ := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hmpos σ),
    LSeries.norm_term_eq, ite_eq_right hn.ne', Complex.ofReal_re, Real.div_rpow hmpos.le hnpos.le]
  ring

lemma tendsto_rpow_mul_LSeries (b : ℕ → ℂ) (hb : LSeriesSummable b 2) {m : ℕ} (hm : 0 < m)
    (hlt : ∀ n, 0 < n → n < m → b n = 0) :
    Tendsto (fun σ : ℝ => (((m : ℝ) ^ σ : ℝ) : ℂ) * LSeries b σ) atTop (𝓝 (b m)) := by
  classical
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have h2re : (2 : ℂ).re = 2 := by simp
  have hsum_g : ∑' n : ℕ, (if n = m then b m else 0) = b m := tsum_ite_eq m (fun _ => b m)
  have hsum_term : ∀ σ : ℝ, ∑' n, (((m : ℝ) ^ σ : ℝ) : ℂ) * term b (σ : ℂ) n =
      (((m : ℝ) ^ σ : ℝ) : ℂ) * LSeries b σ := fun σ => tsum_mul_left
  rw [← hsum_g]
  refine (tendsto_tsum_of_dominated_convergence
    (bound := fun n => (m : ℝ) ^ (2 : ℝ) * ‖term b 2 n‖) (hb.norm.mul_left _) ?_ ?_).congr hsum_term
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0m : (0 : ℕ) ≠ m := hm.ne
      simp [term_zero, h0m]
    rcases lt_trichotomy n m with hnm | rfl | hnm
    · have hb0 : b n = 0 := hlt n hn hnm
      simp [term_of_ne_zero hn.ne', hb0, hnm.ne]
    · simp only [ite_true]
      refine tendsto_const_nhds.congr fun σ => ?_
      rw [term_of_ne_zero hn.ne', Complex.ofReal_cpow hmpos.le, Complex.ofReal_natCast]
      have hne : ((n : ℂ)) ^ (σ : ℂ) ≠ 0 := by
        intro h
        rw [Complex.cpow_eq_zero_iff] at h
        exact (Nat.cast_ne_zero.mpr hn.ne') h.1
      field_simp
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      simp only [hnm.ne', ite_false]
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hfun : (fun σ : ℝ => ‖(((m : ℝ) ^ σ : ℝ) : ℂ) * term b (σ : ℂ) n‖) =
          fun σ : ℝ => ‖b n‖ * ((m : ℝ) / n) ^ σ := funext fun σ => norm_rpow_mul_term b hm hn σ
      rw [hfun]
      have hlt1 : (m : ℝ) / n < 1 := (div_lt_one hnpos).mpr (by exact_mod_cast hnm)
      have hgt : -1 < (m : ℝ) / n := by
        have : 0 < (m : ℝ) / n := by positivity
        linarith
      simpa using (tendsto_rpow_atTop_of_base_lt_one _ hgt hlt1).const_mul ‖b n‖
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with σ hσ n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [term_zero]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [norm_rpow_mul_term b hm hn σ, LSeries.norm_term_eq, ite_eq_right hn.ne', h2re,
      show (m : ℝ) ^ (2 : ℝ) * (‖b n‖ / (n : ℝ) ^ (2 : ℝ)) = ‖b n‖ * ((m : ℝ) / n) ^ (2 : ℝ) by
        rw [Real.div_rpow hmpos.le hnpos.le]; ring]
    rcases lt_or_ge n m with hnm | hnm
    · rw [hlt n hn hnm, norm_zero, zero_mul, zero_mul]
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine Real.rpow_le_rpow_of_exponent_ge (by positivity) ?_ hσ
      rw [div_le_one hnpos]
      exact_mod_cast hnm

/-- `∑ b(n) n^{-σ} → b(1)` as `σ → +∞` along the reals. -/
lemma tendsto_LSeries_atTop (b : ℕ → ℂ) (hb : LSeriesSummable b 2) :
    Tendsto (fun σ : ℝ => LSeries b σ) atTop (𝓝 (b 1)) := by
  have := tendsto_rpow_mul_LSeries b hb one_pos (fun n hn hn1 => by omega)
  simpa using this

namespace ExtSelbergData

variable (F : ExtSelbergData)

/-- The coefficients of `F_t`: `a(n) e^{-c log² n}`. -/
noncomputable def ftCoeff (c : ℝ) (n : ℕ) : ℂ := F.a n * DBNFtZero.gaussCoeff c n

lemma Ft_eq (c : ℝ) : F.Ft c = LSeries (F.ftCoeff c) := rfl

lemma ftCoeff_one (c : ℝ) : F.ftCoeff c 1 = 1 := by
  simp [ftCoeff, DBNFtZero.gaussCoeff, F.a_one]

lemma norm_ftCoeff (c : ℝ) (n : ℕ) :
    ‖F.ftCoeff c n‖ = ‖F.a n‖ * Real.exp (-c * (Real.log n) ^ 2) := by
  rw [ftCoeff, DBNFtZero.gaussCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

/-! ### Terms and absolute convergence everywhere -/

lemma norm_term_eq (c : ℝ) (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    ‖term (F.ftCoeff c) s n‖ =
      ‖F.a n‖ * Real.exp (-c * (Real.log n) ^ 2 - s.re * Real.log n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [LSeries.norm_term_eq, ite_eq_right hn, norm_ftCoeff, Real.rpow_def_of_pos hn', mul_div_assoc,
    ← Real.exp_sub]
  congr 2
  ring

lemma summable_norm_term_two : Summable fun n => ‖term F.a 2 n‖ :=
  (F.summable 2 (by norm_num)).norm

/-- The comparison `‖a(n) e^{-c log² n} n^{-s}‖ ≤ ‖a(n)‖ n^{-2} · exp ((2 - Re s)² / (4c))`:
complete the square `-c L² + (2 - Re s) L ≤ (2 - Re s)² / (4c)`. -/
lemma norm_term_le {c : ℝ} (hc : 0 < c) (s : ℂ) (n : ℕ) :
    ‖term (F.ftCoeff c) s n‖ ≤ ‖term F.a 2 n‖ * Real.exp ((2 - s.re) ^ 2 / (4 * c)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [term_zero]
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have h2re : (2 : ℂ).re = 2 := by simp
  rw [F.norm_term_eq c s hn, LSeries.norm_term_eq, ite_eq_right hn, h2re, Real.rpow_def_of_pos hn',
    div_mul_eq_mul_div, mul_div_assoc, ← Real.exp_sub]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [Real.exp_le_exp]
  set L := Real.log n
  have h4c : (0 : ℝ) < 4 * c := by positivity
  have key : -c * L ^ 2 - s.re * L + L * 2 ≤ (2 - s.re) ^ 2 / (4 * c) := by
    rw [le_div_iff₀ h4c]
    nlinarith [sq_nonneg (2 - s.re - 2 * c * L)]
  linarith

/-- `F_t` converges absolutely for every `s`. -/
lemma lseriesSummable_Ft {c : ℝ} (hc : 0 < c) (s : ℂ) :
    LSeriesSummable (fun n => F.a n * DBNFtZero.gaussCoeff c n) s :=
  Summable.of_norm_bounded (F.summable_norm_term_two.mul_right _) (F.norm_term_le hc s)

lemma lseriesSummable_ftCoeff {c : ℝ} (hc : 0 < c) (s : ℂ) : LSeriesSummable (F.ftCoeff c) s :=
  F.lseriesSummable_Ft hc s

lemma abscissa_lt {c : ℝ} (hc : 0 < c) (s : ℂ) :
    abscissaOfAbsConv (F.ftCoeff c) < s.re := by
  calc abscissaOfAbsConv (F.ftCoeff c) ≤ ((s - 1).re : EReal) :=
        (F.lseriesSummable_ftCoeff hc (s - 1)).abscissaOfAbsConv_le
    _ < s.re := by
        rw [Complex.sub_re, Complex.one_re]
        exact EReal.coe_lt_coe_iff.mpr (by linarith)

/-! ### Differentiability -/

lemma hasDerivAt_Ft {c : ℝ} (hc : 0 < c) (s : ℂ) :
    HasDerivAt (F.Ft c) (-LSeries (logMul (F.ftCoeff c)) s) s :=
  LSeries_hasDerivAt (F.abscissa_lt hc s)

lemma differentiable_Ft {c : ℝ} (hc : 0 < c) : Differentiable ℂ (F.Ft c) :=
  fun s => (F.hasDerivAt_Ft hc s).differentiableAt

/-! ### Growth: finite order -/

/-- `‖F_t(z)‖ ≤ (∑ ‖a(n)‖ n^{-2}) · exp ((2 - Re z)² / (4c))`. -/
lemma norm_Ft_le {c : ℝ} (hc : 0 < c) (z : ℂ) :
    ‖F.Ft c z‖ ≤ (∑' n, ‖term F.a 2 n‖) * Real.exp ((2 - z.re) ^ 2 / (4 * c)) := by
  have hsum := (F.lseriesSummable_ftCoeff hc z).norm
  rw [Ft_eq]
  refine (norm_tsum_le_tsum_norm hsum).trans ?_
  rw [← tsum_mul_right]
  exact hsum.tsum_le_tsum (fun n => F.norm_term_le hc z n) (F.summable_norm_term_two.mul_right _)

lemma one_le_K : 1 ≤ ∑' n, ‖term F.a 2 n‖ := by
  have hs := F.summable_norm_term_two
  have h1 : ‖term F.a 2 1‖ = 1 := by
    rw [LSeries.norm_term_eq, ite_eq_right one_ne_zero, F.a_one]; simp
  calc (1 : ℝ) = ‖term F.a 2 1‖ := h1.symm
    _ ≤ _ := hs.le_tsum 1 fun _ _ => norm_nonneg _

/-- `F_t` is entire of finite order: `‖F_t(z)‖ < exp (‖z‖³)` for `‖z‖` large. -/
theorem hasFiniteOrder_Ft {c : ℝ} (hc : 0 < c) : Hadamard.hasFiniteOrder (F.Ft c) := by
  set K := ∑' n, ‖term F.a 2 n‖ with hK
  have hK1 : 1 ≤ K := F.one_le_K
  have hKpos : 0 < K := by linarith
  refine ⟨F.differentiable_Ft hc, 3, max 1 (max (9 / (4 * c) + 1) (Real.log K + 1)),
    fun z hz => ?_⟩
  have hr1 : 1 ≤ ‖z‖ := le_trans (le_max_left _ _) hz
  have hru : 9 / (4 * c) + 1 ≤ ‖z‖ := le_trans (le_max_of_le_right (le_max_left _ _)) hz
  have hrK : Real.log K + 1 ≤ ‖z‖ := le_trans (le_max_of_le_right (le_max_right _ _)) hz
  refine (F.norm_Ft_le hc z).trans_lt ?_
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h4c : (0 : ℝ) < 4 * c := by positivity
  have hre : (2 - z.re) ^ 2 ≤ (2 + ‖z‖) ^ 2 := by
    have h := Complex.abs_re_le_norm z
    have h' := abs_le.mp h
    have hle : |2 - z.re| ≤ 2 + ‖z‖ := abs_le.mpr ⟨by linarith [h'.1, h'.2], by linarith [h'.1, h'.2]⟩
    calc (2 - z.re) ^ 2 = |2 - z.re| ^ 2 := (sq_abs _).symm
      _ ≤ (2 + ‖z‖) ^ 2 := by gcongr
  calc K * Real.exp ((2 - z.re) ^ 2 / (4 * c))
      = Real.exp (Real.log K + (2 - z.re) ^ 2 / (4 * c)) := by
        rw [Real.exp_add, Real.exp_log hKpos]
    _ < Real.exp (‖z‖ ^ 3) := by
        rw [Real.exp_lt_exp]
        set r := ‖z‖
        have hA : (2 - z.re) ^ 2 / (4 * c) ≤ 9 * r ^ 2 / (4 * c) := by
          apply div_le_div_of_nonneg_right _ h4c.le
          nlinarith [hre, hr1]
        have hB : 9 * r ^ 2 / (4 * c) = r ^ 2 * (9 / (4 * c)) := by ring
        have hC : r ^ 2 * (9 / (4 * c) + 1) ≤ r ^ 2 * r :=
          mul_le_mul_of_nonneg_left hru (sq_nonneg r)
        have hD : r ≤ r ^ 2 := by nlinarith
        nlinarith [hA, hB, hC, hD, hrK]

/-! ### The series on the real axis -/

/-- `F_t(σ) → 1` as `σ → +∞` along the reals, since `a 1 = 1`. -/
lemma tendsto_Ft_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun σ : ℝ => F.Ft c σ) atTop (𝓝 1) := by
  have := tendsto_LSeries_atTop (F.ftCoeff c) (F.lseriesSummable_ftCoeff hc 2)
  rw [F.ftCoeff_one] at this
  rw [Ft_eq]
  exact this

lemma lseriesSummable_logMul {c : ℝ} (hc : 0 < c) (s : ℂ) :
    LSeriesSummable (logMul (F.ftCoeff c)) s :=
  LSeriesSummable_logMul_of_lt_re (F.abscissa_lt hc s)

/-- `F_t'(σ) → 0` as `σ → +∞` along the reals (the `n = 1` coefficient of `F_t'` is
`log 1 · a 1 = 0`). -/
lemma tendsto_logSeries_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun σ : ℝ => LSeries (logMul (F.ftCoeff c)) σ) atTop (𝓝 0) := by
  have := tendsto_LSeries_atTop _ (F.lseriesSummable_logMul hc 2)
  simpa [logMul] using this

lemma exists_Ft_ne_zero {c : ℝ} (hc : 0 < c) : ∃ z, F.Ft c z ≠ 0 := by
  by_contra hall
  push Not at hall
  have h2 : Tendsto (fun σ : ℝ => F.Ft c σ) atTop (𝓝 0) := by
    simp only [hall]; exact tendsto_const_nhds
  exact one_ne_zero (tendsto_nhds_unique (F.tendsto_Ft_atTop hc) h2)

/-! ### The theorem -/

/-- **Dobner, Lemma 3 (qualitative), for the extended Selberg class.**  For every `c > 0` the
entire function `F_t(s) = ∑ a(n) e^{-c log² n} n^{-s}` has a zero. -/
theorem exists_zero_Ft {c : ℝ} (hc : 0 < c) : ∃ s : ℂ, F.Ft c s = 0 := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨g, hg, -⟩ := Hadamard.entire_no_zeros_is_exp_polynomial (F.Ft c)
    (Hadamard.order (F.Ft c)) (F.hasFiniteOrder_Ft hc) rfl hne
  set p := Polynomial.derivative g with hp
  -- F_t' = F_t * g' everywhere
  have hderiv : ∀ s, -LSeries (logMul (F.ftCoeff c)) s = F.Ft c s * p.eval s := by
    intro s
    have h1 : HasDerivAt (F.Ft c) (-LSeries (logMul (F.ftCoeff c)) s) s := F.hasDerivAt_Ft hc s
    have h2 : HasDerivAt (fun z => Complex.exp (g.eval z))
        (Complex.exp (g.eval s) * p.eval s) s := (g.hasDerivAt s).cexp
    have hfun : (fun z => Complex.exp (g.eval z)) = F.Ft c := funext fun z => (hg z).symm
    rw [hfun, ← hg s] at h2
    exact h1.unique h2
  -- g'(σ) = F_t'(σ) / F_t(σ) → 0 / 1 = 0 along the real axis
  have hp_lim : Tendsto (fun σ : ℝ => p.eval (σ : ℂ)) atTop (𝓝 0) := by
    have h : ∀ σ : ℝ, p.eval (σ : ℂ) = -LSeries (logMul (F.ftCoeff c)) σ / F.Ft c σ := by
      intro σ
      rw [hderiv σ]
      field_simp [hne σ]
    simp_rw [h]
    have := (F.tendsto_logSeries_atTop hc).neg.div (F.tendsto_Ft_atTop hc) one_ne_zero
    rw [neg_zero, zero_div] at this
    exact this
  -- so g' has degree ≤ 0
  have hdeg : p.degree ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have hT : Tendsto (fun σ : ℝ => ‖p.eval (σ : ℂ)‖) atTop atTop :=
      p.tendsto_norm_atTop hpos (z := fun σ : ℝ => (σ : ℂ))
        (by simpa [Complex.norm_real] using tendsto_abs_atTop_atTop)
    have hT0 : Tendsto (fun σ : ℝ => ‖p.eval (σ : ℂ)‖) atTop (𝓝 0) := by
      simpa using hp_lim.norm
    exact hT.not_tendsto (disjoint_nhds_atTop (0 : ℝ)).symm hT0
  -- so g' is a constant, and the constant is 0
  obtain ⟨b, hb⟩ : ∃ b, p = Polynomial.C b := ⟨_, Polynomial.eq_C_of_degree_le_zero hdeg⟩
  have hb0 : b = 0 := by
    have h1 : Tendsto (fun σ : ℝ => p.eval (σ : ℂ)) atTop (𝓝 b) := by
      simp only [hb, Polynomial.eval_C]; exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 hp_lim
  have hp0 : p = 0 := by rw [hb, hb0, map_zero]
  -- hence F_t' ≡ 0 on the real axis
  have hzero : ∀ σ : ℝ, LSeries (logMul (F.ftCoeff c)) σ = 0 := by
    intro σ
    have h := hderiv σ
    rw [hp0, Polynomial.eval_zero, mul_zero, neg_eq_zero] at h
    exact h
  -- the least n₀ ≥ 2 with a(n₀) ≠ 0 gives n₀^σ F_t'(σ) → log n₀ · a(n₀) e^{-c log² n₀} ≠ 0
  set n₀ := Nat.find F.nonconst with hn₀
  have hspec : 2 ≤ n₀ ∧ F.a n₀ ≠ 0 := Nat.find_spec F.nonconst
  have hmin : ∀ n, n < n₀ → ¬ (2 ≤ n ∧ F.a n ≠ 0) := fun n hn => Nat.find_min F.nonconst hn
  have hlt : ∀ n, 0 < n → n < n₀ → logMul (F.ftCoeff c) n = 0 := by
    intro n hn hnlt
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have : n = 1 := by omega
      subst this
      simp [logMul]
    · have ha : F.a n = 0 := by
        by_contra ha
        exact hmin n hnlt ⟨h2, ha⟩
      simp [logMul, ftCoeff, ha]
  have hlim := tendsto_rpow_mul_LSeries (logMul (F.ftCoeff c)) (F.lseriesSummable_logMul hc 2)
    (show 0 < n₀ by omega) hlt
  have h0 : Tendsto (fun σ : ℝ => (((n₀ : ℝ) ^ σ : ℝ) : ℂ) * LSeries (logMul (F.ftCoeff c)) σ)
      atTop (𝓝 0) := by
    simp only [hzero, mul_zero]; exact tendsto_const_nhds
  have heq : logMul (F.ftCoeff c) n₀ = 0 := tendsto_nhds_unique hlim h0
  -- but every factor of logMul (ftCoeff c) n₀ = log n₀ * (a n₀ * e^{-c log² n₀}) is nonzero
  have hlog : Complex.log (n₀ : ℂ) ≠ 0 := by
    rw [← Complex.natCast_log, Complex.ofReal_ne_zero]
    exact (Real.log_pos (by exact_mod_cast (show 1 < n₀ by omega))).ne'
  have hgauss : DBNFtZero.gaussCoeff c n₀ ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  exact mul_ne_zero hlog (mul_ne_zero hspec.2 hgauss) heq

/-- `F_t` has zeros of arbitrarily large imaginary part (Bohr shifts + zero-free Hurwitz). -/
theorem exists_zero_im_ge_Ft {c : ℝ} (hc : 0 < c) (Y : ℝ) : ∃ s : ℂ, F.Ft c s = 0 ∧ Y ≤ s.im := by
  obtain ⟨s₀, hs₀⟩ := F.exists_zero_Ft hc
  obtain ⟨τ, hτ, hconv⟩ :=
    DBNBohr.exists_shifts_tendstoLocallyUniformly (F.ftCoeff c) (F.lseriesSummable_ftCoeff hc)
  by_contra h
  push Not at h
  -- every zero of F_t has imaginary part < Y
  have hτ_top : Tendsto (fun j => (τ j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hτ.tendsto_atTop
  have hF : ∀ᶠ j in atTop, DifferentiableOn ℂ (fun s => F.Ft c (s + (τ j : ℂ) * I))
      (Metric.ball s₀ 1) ∧ ∀ z ∈ Metric.ball s₀ 1, F.Ft c (z + (τ j : ℂ) * I) ≠ 0 := by
    filter_upwards [hτ_top.eventually_ge_atTop (Y - s₀.im + 1)] with j hj
    refine ⟨((F.differentiable_Ft hc).comp (differentiable_id.add_const _)).differentiableOn, ?_⟩
    intro z hz hzero
    have h1 := h _ hzero
    have h2 : |z.im - s₀.im| < 1 := by
      have := Complex.abs_im_le_norm (z - s₀)
      rw [Complex.sub_im] at this
      exact lt_of_le_of_lt this (by simpa [dist_eq_norm] using hz)
    rw [Complex.add_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, Complex.I_re,
      Complex.I_im] at h1
    have := abs_lt.mp h2
    linarith [this.1, this.2]
  have hne : ∃ z, F.Ft c z ≠ 0 := F.exists_Ft_ne_zero hc
  rw [← Ft_eq] at hconv
  exact DBN.hurwitz_ne_zero Metric.isOpen_ball hF (F.differentiable_Ft hc)
    hconv.tendstoLocallyUniformlyOn hne (Metric.mem_ball_self one_pos) hs₀

end ExtSelbergData

end DBNSelberg
