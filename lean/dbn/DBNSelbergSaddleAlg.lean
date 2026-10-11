/-
  DBNSelbergSaddleAlg -- the exact saddle-point bookkeeping for Dobner's Theorem 4, for an
  abstract element `F` of the extended Selberg class (`DBNSelberg.ExtSelbergData`).

  This is `DBNSaddleAlg` with `ζ` replaced by `F`: `γ` becomes `γ_F = P Q^v ∏ Γ(λ_j v + μ_j)`,
  `ℓ(b) = ½ Log(b/2π)` becomes `ℓ_F(b) = log Q + ∑ λ_j Log(λ_j b + μ_j)`, the ratio `ρ(δ)` becomes
  `ρ_F(δ) = P(b+δ)/P(b)` and `Q(δ)` becomes `Q_F(δ)`; all of these enter only through the exact
  decomposition `gammaF_add_eq` (DBNSelbergData), so the algebra is literally the ζ algebra.
  `h_n = (c/2) log n` and `a_n = e^{-h_n²/c}` do not depend on `F` and are reused from `DBNSaddle`.

  With `b = s + M₀` (`Re b > 0`, `P(b) ≠ 0`), `J_F(s) = s + (c/2) ℓ_F(b)`,
  `γ_t(s) = γ_F(b) exp(-M₀ ℓ_F(b) + (c/4) ℓ_F(b)²)`, on the contour `Re v = Re b + h_n`:
      B_n(J_F(s)) = γ_t(s) · a(n) a_n n^{-s} · (1 + E_n(s)),
  and, summing over `n` (the error series being assumed summable),
      ∑_n B_n(J_F(s)) = γ_t(s) (F_{c/4}(s) + ∑_n a(n) a_n n^{-s} E_n(s)).
  The contour may be moved (`Bn_shift`) because `γ_F` is bounded on compact `a`-ranges by a
  polynomial in `|τ|` while the Gaussian `e^{(v-s)²/c}` decays along horizontal segments.

  Nothing here is about zeros.  conjecture1_proved = False.
-/
import Mathlib
import DBNSelbergData
import DBNSaddleAlg

open Complex Filter Topology MeasureTheory Set
open scoped Real

namespace DBNSelberg

namespace ExtSelbergData

open DBNGaussConv DBNStirling DBNSaddle

variable (F : ExtSelbergData)

/-! ### Elementary bounds on `P` and `γ_F` -/

/-- `C_P = ∑_k ‖p_k‖ k!`, so that `‖P(v)‖ ≤ C_P e^{‖v‖}`. -/
noncomputable def Cp : ℝ :=
  ∑ k ∈ Finset.range (F.P.natDegree + 1), ‖F.P.coeff k‖ * (k.factorial : ℝ)

lemma Cp_nonneg : 0 ≤ F.Cp :=
  Finset.sum_nonneg fun k _ => by positivity

/-- The polynomial majorant of `norm_gammaF_le` is at most `C_P e^{x}`. -/
lemma polySum_le_exp {x : ℝ} (hx : 0 ≤ x) :
    ∑ k ∈ Finset.range (F.P.natDegree + 1), ‖F.P.coeff k‖ * x ^ k ≤ F.Cp * Real.exp x := by
  rw [Cp, Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have h := Real.pow_div_factorial_le_exp x hx k
  rw [div_le_iff₀ hk] at h
  calc ‖F.P.coeff k‖ * x ^ k ≤ ‖F.P.coeff k‖ * (Real.exp x * k.factorial) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = ‖F.P.coeff k‖ * k.factorial * Real.exp x := by ring

/-- The `F`-dependent factor of `norm_gammaF_le`: `Q^x ∏_j Γ(λ_j x + Re μ_j)`. -/
noncomputable def gConst (x : ℝ) : ℝ := F.Q ^ x * ∏ j, Real.Gamma (F.lam j * x + (F.mu j).re)

lemma gConst_pos {x : ℝ} (hx : 0 < x) : 0 < F.gConst x := by
  unfold gConst
  refine mul_pos (Real.rpow_pos_of_pos F.Q_pos x) (Finset.prod_pos fun j _ => ?_)
  refine Real.Gamma_pos_of_pos ?_
  have := F.lam_pos j
  have := F.mu_re_nonneg j
  positivity

/-- `gConst` is bounded on `[a, a']`, `0 < a`. -/
lemma exists_gConst_bound {a a' : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, ∀ x ∈ Icc a a', F.gConst x ≤ C := by
  have hcont : ContinuousOn F.gConst (Icc a a') := by
    unfold gConst
    refine ContinuousOn.mul ?_ ?_
    · intro x hx
      exact (Real.continuousAt_const_rpow F.Q_pos.ne').continuousWithinAt
    · refine continuousOn_finsetProd _ fun j _ => ?_
      intro x hx
      refine ContinuousAt.continuousWithinAt ?_
      refine (Real.differentiableAt_Gamma fun m => ?_).continuousAt.comp (by fun_prop)
      intro h
      have h1 := F.lam_pos j
      have h2 := F.mu_re_nonneg j
      have h3 : 0 < F.lam j * x + (F.mu j).re := by
        have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
        positivity
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn hcont).bddAbove
  exact ⟨C, fun x hx => hC ⟨x, hx, rfl⟩⟩

/-- `‖γ_F(x + iy)‖ ≤ C_P e^{a' + |y|} C_γ` for `x ∈ [a, a']`, `0 < a`, whenever `gConst ≤ C_γ`
on `[a, a']`. -/
lemma norm_gammaF_le_of_mem {a a' : ℝ} (ha : 0 < a) {Cγ : ℝ}
    (hCγ : ∀ x ∈ Icc a a', F.gConst x ≤ Cγ) {x : ℝ} (hx : x ∈ Icc a a') (y : ℝ) :
    ‖F.gammaF ((x : ℂ) + y * I)‖ ≤ F.Cp * Real.exp (a' + |y|) * Cγ := by
  have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
  have h := F.norm_gammaF_le hx0 y
  have hg : F.Q ^ x * ∏ j, Real.Gamma (F.lam j * x + (F.mu j).re) = F.gConst x := rfl
  rw [mul_assoc, hg] at h
  refine h.trans ?_
  have h1 := F.polySum_le_exp (x := x + |y|) (by linarith [abs_nonneg y])
  have h2 : Real.exp (x + |y|) ≤ Real.exp (a' + |y|) :=
    Real.exp_le_exp.mpr (by linarith [hx.2])
  have hC0 : 0 ≤ Cγ := le_trans (F.gConst_pos hx0).le (hCγ x hx)
  calc (∑ k ∈ Finset.range (F.P.natDegree + 1), ‖F.P.coeff k‖ * (x + |y|) ^ k) * F.gConst x
      ≤ (F.Cp * Real.exp (a' + |y|)) * Cγ := by
        refine mul_le_mul (h1.trans ?_) (hCγ x hx) (F.gConst_pos hx0).le
          (mul_nonneg F.Cp_nonneg (Real.exp_pos _).le)
        exact mul_le_mul_of_nonneg_left h2 F.Cp_nonneg

/-! ### The norm of the `B`-integrand -/

/-- `‖BInt c a n s τ‖` exactly. -/
lemma norm_BInt_eq (c a : ℝ) (n : ℕ+) (s : ℂ) (τ : ℝ) :
    ‖F.BInt c a n s τ‖ = ‖F.a n‖ * ‖F.gammaF ((a : ℂ) + τ * I)‖ * (n : ℝ) ^ (-a) *
      Real.exp (((a - s.re) ^ 2 - (τ - s.im) ^ 2) / c) := by
  rw [BInt, norm_mul, norm_mul, norm_mul]
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

lemma continuous_BInt (c : ℝ) {a : ℝ} (ha : 0 < a) (n : ℕ+) (s : ℂ) :
    Continuous (F.BInt c a n s) := by
  have hline : Continuous fun τ : ℝ => (a : ℂ) + τ * I := by fun_prop
  have hγ : Continuous fun τ : ℝ => F.gammaF ((a : ℂ) + τ * I) := by
    refine continuous_iff_continuousAt.mpr fun τ => ?_
    refine (F.differentiableAt_gammaF ?_).continuousAt.comp hline.continuousAt
    simpa using ha
  have hn : Continuous fun τ : ℝ => 1 / (n : ℂ) ^ ((a : ℂ) + τ * I) := by
    refine continuous_const.div (hline.const_cpow (Or.inl ?_)) fun τ => ?_
    · exact_mod_cast n.ne_zero
    · rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
      left
      exact_mod_cast n.ne_zero
  unfold BInt
  fun_prop

/-- `BInt` is integrable on every vertical line `Re v = a > 0`: a Gaussian majorant. -/
lemma integrable_BInt {c : ℝ} (hc : 0 < c) {a : ℝ} (ha : 0 < a) (n : ℕ+) (s : ℂ) :
    Integrable (F.BInt c a n s) := by
  -- `exp (a + |τ|) ≤ exp (a + |Im s|) exp |u|` and `exp (|u| - u²/c) ≤ exp (c/2) exp (-u²/(2c))`.
  set K : ℝ := ‖F.a n‖ * (F.Cp * Real.exp (a + |s.im|) * F.gConst a) * (n : ℝ) ^ (-a) *
    Real.exp ((a - s.re) ^ 2 / c) * Real.exp (c / 2) with hK
  have hg : Integrable fun u : ℝ => K * Real.exp (-(1 / (2 * c)) * u ^ 2) :=
    (integrable_exp_neg_mul_sq (by positivity)).const_mul K
  have hg' := hg.comp_sub_right s.im
  refine hg'.mono' (F.continuous_BInt c ha n s).aestronglyMeasurable (ae_of_all _ fun τ => ?_)
  rw [F.norm_BInt_eq c a n s τ]
  have hγ : ‖F.gammaF ((a : ℂ) + τ * I)‖ ≤ F.Cp * Real.exp (a + |τ|) * F.gConst a :=
    F.norm_gammaF_le_of_mem ha (a' := a) (fun x hx => by
      rw [show x = a from le_antisymm hx.2 hx.1]) ⟨le_rfl, le_rfl⟩ τ
  set u : ℝ := τ - s.im with hu
  have hτ : |τ| ≤ |u| + |s.im| := by
    rw [hu]
    calc |τ| = |(τ - s.im) + s.im| := by ring_nf
      _ ≤ |τ - s.im| + |s.im| := abs_add_le _ _
  have hAM : |u| - u ^ 2 / c ≤ c / 2 - u ^ 2 / (2 * c) := by
    have : |u| ≤ u ^ 2 / (2 * c) + c / 2 := by
      rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (|u| - c), sq_abs u]
    have h2 : u ^ 2 / (2 * c) = u ^ 2 / c / 2 := by field_simp
    linarith
  have hexp : Real.exp (a + |τ|) * Real.exp (((a - s.re) ^ 2 - u ^ 2) / c) ≤
      Real.exp (a + |s.im|) * Real.exp ((a - s.re) ^ 2 / c) * Real.exp (c / 2) *
        Real.exp (-(1 / (2 * c)) * u ^ 2) := by
    simp only [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : ((a - s.re) ^ 2 - u ^ 2) / c = (a - s.re) ^ 2 / c - u ^ 2 / c := by ring
    rw [this]
    have h3 : -(1 / (2 * c)) * u ^ 2 = -(u ^ 2 / (2 * c)) := by ring
    rw [h3]
    linarith
  have hn0 : 0 ≤ (n : ℝ) ^ (-a) := by positivity
  have hG0 : 0 ≤ F.gConst a := (F.gConst_pos ha).le
  rw [hK]
  calc ‖F.a n‖ * ‖F.gammaF ((a : ℂ) + τ * I)‖ * (n : ℝ) ^ (-a) *
        Real.exp (((a - s.re) ^ 2 - u ^ 2) / c)
      ≤ ‖F.a n‖ * (F.Cp * Real.exp (a + |τ|) * F.gConst a) * (n : ℝ) ^ (-a) *
        Real.exp (((a - s.re) ^ 2 - u ^ 2) / c) := by gcongr
    _ = ‖F.a n‖ * F.Cp * F.gConst a * (n : ℝ) ^ (-a) *
        (Real.exp (a + |τ|) * Real.exp (((a - s.re) ^ 2 - u ^ 2) / c)) := by ring
    _ ≤ ‖F.a n‖ * F.Cp * F.gConst a * (n : ℝ) ^ (-a) *
        (Real.exp (a + |s.im|) * Real.exp ((a - s.re) ^ 2 / c) * Real.exp (c / 2) *
          Real.exp (-(1 / (2 * c)) * u ^ 2)) := by
        refine mul_le_mul_of_nonneg_left hexp ?_
        have := F.Cp_nonneg
        positivity
    _ = _ := by ring

/-! ### The per-`σ` identity -/

/-- **The exact per-`σ` identity.**  On the contour `Re v = Re s + M₀ + h_n`, parametrised by
`τ = Im s + σ`, the `B`-integrand at `J_F(s)` is
`γ_t(s) · a(n) a_n n^{-s} · e^{M₀²/c} · K_n(σ) gw(σ)`. -/
theorem BInt_J_eq {c M₀ : ℝ} (hc : 0 < c) (n : ℕ+) {s : ℂ} (hb : 0 < (s + M₀).re)
    (hP : F.P.eval (s + M₀) ≠ 0) (σ : ℝ) :
    F.BInt c (s.re + M₀ + hh c n) n (F.JF c M₀ s) (s.im + σ) =
      F.γtF c M₀ s * (F.a n * (coef c n : ℂ) * (1 / (n : ℂ) ^ s)) *
        (cexp ((M₀ ^ 2 / c : ℝ)) * (F.KF c M₀ n s σ * gw c M₀ σ)) := by
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
  have hL : F.BInt c (s.re + M₀ + hh c n) n (F.JF c M₀ s) (s.im + σ) =
      F.a n * (F.gammaF b * F.ρF b (δ c n σ)) * cexp ((F.QF b (δ c n σ) + δ c n σ * F.ellF b) +
        (-(Real.log n : ℂ) * (b + δ c n σ)) + (b + δ c n σ - F.JF c M₀ s) ^ 2 / c) := by
    rw [BInt, hv, F.gammaF_add_eq hb hbδ hP, one_div_cpow_eq]
    simp only [Complex.exp_add]
    ring
  have hR : F.γtF c M₀ s * (F.a n * (coef c n : ℂ) * (1 / (n : ℂ) ^ s)) *
      (cexp ((M₀ ^ 2 / c : ℝ)) * (F.KF c M₀ n s σ * gw c M₀ σ)) =
      F.a n * (F.gammaF b * F.ρF b (δ c n σ)) *
        cexp ((-(M₀ : ℂ) * F.ellF b + (c / 4 : ℂ) * F.ellF b ^ 2) +
        ((-(hh c n) ^ 2 / c : ℝ) : ℂ) + (-(Real.log n : ℂ) * s) + ((M₀ ^ 2 / c : ℝ) : ℂ) +
        F.QF b (δ c n σ) + (-(σ : ℂ) ^ 2 / c + 2 * (M₀ : ℂ) * σ * I / c)) := by
    rw [γtF, coef, KF, gw, one_div_cpow_eq, Complex.ofReal_exp]
    simp only [Complex.exp_add]
    rw [← hbdef]
    ring
  rw [hL, hR]
  congr 2
  rw [JF, ← hbdef, log_eq_hh hc.ne']
  simp only [δ]
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

/-! ### The integrated identity -/

lemma γtF_ne_zero {c M₀ : ℝ} {s : ℂ} (hb : 0 < (s + M₀).re) (hP : F.P.eval (s + M₀) ≠ 0) :
    F.γtF c M₀ s ≠ 0 :=
  mul_ne_zero (F.gammaF_ne_zero hb hP) (Complex.exp_ne_zero _)

/-- **The integrated identity**: `B_n(J_F(s)) = γ_t(s) a(n) a_n n^{-s} (1 + E_n(s))` on the contour
`Re v = Re s + M₀ + h_n`. -/
theorem Bn_J_eq {c M₀ : ℝ} (hc : 0 < c) (n : ℕ+) {s : ℂ} (hb : 0 < (s + M₀).re)
    (hP : F.P.eval (s + M₀) ≠ 0) :
    F.Bn c (s.re + M₀ + hh c n) n (F.JF c M₀ s) =
      F.γtF c M₀ s * (F.a n * (coef c n : ℂ) * (1 / (n : ℂ) ^ s)) * (1 + F.EF c M₀ n s) := by
  rcases eq_or_ne (F.a n) 0 with ha0 | ha0
  · simp [Bn, BInt, ha0]
  have hb' : 0 < s.re + M₀ := by simpa using hb
  set C : ℂ := F.γtF c M₀ s * (F.a n * (coef c n : ℂ) * (1 / (n : ℂ) ^ s)) *
    cexp ((M₀ ^ 2 / c : ℝ)) with hC
  have hC0 : C ≠ 0 := by
    rw [hC]
    refine mul_ne_zero (mul_ne_zero (F.γtF_ne_zero hb hP) (mul_ne_zero (mul_ne_zero ha0 ?_) ?_))
      (Complex.exp_ne_zero _)
    · exact_mod_cast (coef_pos c n).ne'
    · rw [one_div]
      refine inv_ne_zero ?_
      rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
      left
      exact_mod_cast n.ne_zero
  have hpt : ∀ σ : ℝ, F.BInt c (s.re + M₀ + hh c n) n (F.JF c M₀ s) (s.im + σ) =
      C * (F.KF c M₀ n s σ * gw c M₀ σ) := by
    intro σ
    rw [F.BInt_J_eq hc n hb hP σ, hC]
    ring
  have hint : Integrable fun σ : ℝ => F.KF c M₀ n s σ * gw c M₀ σ := by
    have h1 : Integrable fun σ : ℝ =>
        F.BInt c (s.re + M₀ + hh c n) n (F.JF c M₀ s) (s.im + σ) :=
      (F.integrable_BInt hc (by linarith [hh_nonneg hc n]) n (F.JF c M₀ s)).comp_add_left s.im
    simp_rw [hpt] at h1
    exact (integrable_const_mul_iff (IsUnit.mk0 _ hC0) _).mp h1
  have hB : F.Bn c (s.re + M₀ + hh c n) n (F.JF c M₀ s) =
      (1 / ((Real.sqrt (π * c) : ℝ) : ℂ)) * ∫ σ : ℝ, C * (F.KF c M₀ n s σ * gw c M₀ σ) := by
    rw [Bn]
    congr 1
    rw [← integral_add_left_eq_self _ s.im]
    exact integral_congr_ae (ae_of_all _ fun σ => hpt σ)
  rw [hB, integral_const_mul, EF]
  have hsplit : ∫ σ : ℝ, (F.KF c M₀ n s σ - 1) * gw c M₀ σ =
      (∫ σ : ℝ, F.KF c M₀ n s σ * gw c M₀ σ) - ∫ σ : ℝ, gw c M₀ σ := by
    rw [← integral_sub hint (integrable_gw hc M₀)]
    congr 1
    funext σ
    ring
  rw [hsplit, hC]
  have hg := integral_gw hc M₀
  have this : cexp ((M₀ ^ 2 / c : ℝ)) * cexp (-(M₀ ^ 2 / c : ℝ)) = 1 := by
    rw [← Complex.exp_add]; simp
  linear_combination (F.γtF c M₀ s * (F.a n * (coef c n : ℂ) * (1 / (n : ℂ) ^ s)) *
      cexp ((M₀ ^ 2 / c : ℝ))) * hg
    + (F.γtF c M₀ s * (F.a n * (coef c n : ℂ) * (1 / (n : ℂ) ^ s))) * this

/-! ### Moving the contour of `B_n` -/

/-- The integrand of `B_n` as a function of the complex variable `v`. -/
noncomputable def Fv (c : ℝ) (n : ℕ+) (s : ℂ) (v : ℂ) : ℂ :=
  F.a n * F.gammaF v * (1 / (n : ℂ) ^ v) * cexp ((v - s) ^ 2 / c)

lemma BInt_eq_Fv (c a : ℝ) (n : ℕ+) (s : ℂ) (τ : ℝ) :
    F.BInt c a n s τ = F.Fv c n s ((a : ℂ) + τ * I) := rfl

lemma differentiableAt_Fv (c : ℝ) (n : ℕ+) (s : ℂ) {v : ℂ} (hv : 0 < v.re) :
    DifferentiableAt ℂ (F.Fv c n s) v := by
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  have h1 : DifferentiableAt ℂ (fun w : ℂ => 1 / (n : ℂ) ^ w) v := by
    refine (differentiableAt_const _).div (differentiableAt_id.const_cpow (Or.inl hn)) ?_
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl hn
  unfold Fv
  exact (((differentiableAt_const _).mul (F.differentiableAt_gammaF hv)).mul h1).mul
    ((((differentiableAt_id.sub_const s).pow 2).div_const _).cexp)

/-- The horizontal bound for `Fv` on the rectangle: `x ∈ [a, a']`, `|y| ≥ |Im s|`. -/
lemma norm_Fv_le {c : ℝ} (hc : 0 < c) {a a' : ℝ} (ha : 0 < a) (n : ℕ+) (s : ℂ) {Cγ : ℝ}
    (hCγ : ∀ x ∈ Icc a a', F.gConst x ≤ Cγ) {x : ℝ} (hx : x ∈ Icc a a')
    {y : ℝ} (hy : |s.im| ≤ |y|) :
    ‖F.Fv c n s ((x : ℂ) + y * I)‖ ≤
      ‖F.a n‖ * (F.Cp * Real.exp (a' + |y|) * Cγ) *
        Real.exp (((a' + |s.re|) ^ 2 - (|y| - |s.im|) ^ 2) / c) := by
  have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
  have ha' : 0 < a' := lt_of_lt_of_le hx0 hx.2
  have hCγ0 : 0 ≤ Cγ := le_trans (F.gConst_pos ha).le (hCγ a ⟨le_rfl, le_trans hx.1 hx.2⟩)
  rw [← BInt_eq_Fv, F.norm_BInt_eq c x n s y]
  have hγ := F.norm_gammaF_le_of_mem ha hCγ hx y
  have hn : (n : ℝ) ^ (-x) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast n.pos) (by linarith)
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
  have hB0 : 0 ≤ F.Cp * Real.exp (a' + |y|) * Cγ := by
    have := F.Cp_nonneg; positivity
  calc ‖F.a n‖ * ‖F.gammaF ((x : ℂ) + y * I)‖ * (n : ℝ) ^ (-x) *
        Real.exp (((x - s.re) ^ 2 - (y - s.im) ^ 2) / c)
      ≤ ‖F.a n‖ * (F.Cp * Real.exp (a' + |y|) * Cγ) * 1 *
        Real.exp (((a' + |s.re|) ^ 2 - (|y| - |s.im|) ^ 2) / c) := by
        gcongr
    _ = _ := by ring

/-- **The contour of `B_n` may be moved**: `B_n c a n s = B_n c a' n s` for `0 < a ≤ a'`. -/
theorem Bn_shift {c : ℝ} (hc : 0 < c) {a a' : ℝ} (ha : 0 < a) (haa : a ≤ a') (n : ℕ+) (s : ℂ) :
    F.Bn c a n s = F.Bn c a' n s := by
  unfold Bn
  congr 1
  show (∫ τ : ℝ, F.Fv c n s ((a : ℂ) + τ * I)) = ∫ τ : ℝ, F.Fv c n s ((a' : ℂ) + τ * I)
  have ha' : 0 < a' := lt_of_lt_of_le ha haa
  obtain ⟨Cγ, hCγ⟩ := F.exists_gConst_bound (a' := a') ha
  -- the rectangle identity
  have hrect : ∀ T : ℝ,
      (∫ x in a..a', F.Fv c n s (x + -(T : ℂ) * I)) - (∫ x in a..a', F.Fv c n s (x + T * I)) =
        I * (∫ y in (-T)..T, F.Fv c n s (a + y * I)) -
          I * (∫ y in (-T)..T, F.Fv c n s (a' + y * I)) := by
    intro T
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (F.Fv c n s) ⟨a, -T⟩
      ⟨a', T⟩ (fun v hv => by
        refine (F.differentiableAt_Fv c n s ?_).differentiableWithinAt
        have := (Complex.mem_reProdIm.mp hv).1
        change v.re ∈ uIcc a a' at this
        rw [uIcc_of_le haa] at this
        linarith [this.1])
    simp only [smul_eq_mul, Complex.ofReal_neg] at h
    linear_combination h
  -- the horizontal sides tend to zero
  have hCγ0 : 0 ≤ Cγ := le_trans (F.gConst_pos ha).le (hCγ a ⟨le_rfl, haa⟩)
  have hCp := F.Cp_nonneg
  have hhoriz : ∀ T : ℝ, |s.im| ≤ T → ∀ y : ℝ, |y| = T →
      ‖∫ x in a..a', F.Fv c n s (x + y * I)‖ ≤
        (‖F.a n‖ * (F.Cp * Real.exp (a' + T) * Cγ) *
          Real.exp (((a' + |s.re|) ^ 2 - (T - |s.im|) ^ 2) / c)) * |a' - a| := by
    intro T hT y hy
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [uIoc_of_le haa] at hx
    have hx' : x ∈ Icc a a' := ⟨hx.1.le, hx.2⟩
    have := F.norm_Fv_le hc ha n s hCγ hx' (y := y) (by rw [hy]; exact hT)
    rwa [hy] at this
  -- the bound decays like e^{-T}
  set D : ℝ := (a' + |s.re|) ^ 2 with hDdef
  set K : ℝ := ‖F.a n‖ * F.Cp * Cγ * Real.exp (a' + D / c + 2 * |s.im|) with hKdef
  have hdecay : ∀ T : ℝ, |s.im| + 2 * c ≤ T →
      ‖F.a n‖ * (F.Cp * Real.exp (a' + T) * Cγ) * Real.exp ((D - (T - |s.im|) ^ 2) / c) ≤
        K * Real.exp (-T) := by
    intro T hT
    have hsq : 2 * (T - |s.im|) ≤ (T - |s.im|) ^ 2 / c := by
      rw [le_div_iff₀ hc]
      nlinarith
    have hexp : Real.exp (a' + T) * Real.exp ((D - (T - |s.im|) ^ 2) / c) ≤
        Real.exp (a' + D / c + 2 * |s.im|) * Real.exp (-T) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [sub_div]
      linarith
    calc ‖F.a n‖ * (F.Cp * Real.exp (a' + T) * Cγ) * Real.exp ((D - (T - |s.im|) ^ 2) / c)
        = ‖F.a n‖ * F.Cp * Cγ * (Real.exp (a' + T) * Real.exp ((D - (T - |s.im|) ^ 2) / c)) := by
          ring
      _ ≤ ‖F.a n‖ * F.Cp * Cγ * (Real.exp (a' + D / c + 2 * |s.im|) * Real.exp (-T)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = K * Real.exp (-T) := by rw [hKdef]; ring
  have hzero : Tendsto (fun T : ℝ => (K * Real.exp (-T)) * |a' - a|) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul K).mul_const |a' - a|
    simpa using this
  have hside_pos : Tendsto (fun T : ℝ => ∫ x in a..a', F.Fv c n s (x + T * I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hzero
    filter_upwards [eventually_ge_atTop (|s.im| + 2 * c)] with T hT
    have hT' : |s.im| ≤ T := by linarith
    have hyT : |T| = T := abs_of_nonneg (by linarith [abs_nonneg s.im])
    exact (hhoriz T hT' T hyT).trans (mul_le_mul_of_nonneg_right (hdecay T hT) (abs_nonneg _))
  have hside_neg : Tendsto (fun T : ℝ => ∫ x in a..a', F.Fv c n s (x + -(T : ℂ) * I)) atTop
      (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hzero
    filter_upwards [eventually_ge_atTop (|s.im| + 2 * c)] with T hT
    have hT' : |s.im| ≤ T := by linarith
    have hyT : |-T| = T := by rw [abs_neg]; exact abs_of_nonneg (by linarith [abs_nonneg s.im])
    have := (hhoriz T hT' (-T) hyT).trans (mul_le_mul_of_nonneg_right (hdecay T hT) (abs_nonneg _))
    simpa only [Complex.ofReal_neg] using this
  -- the vertical sides converge to the full-line integrals
  have hV : ∀ b : ℝ, 0 < b → Tendsto (fun T : ℝ => ∫ y in (-T)..T, F.Fv c n s (b + y * I)) atTop
      (𝓝 (∫ y : ℝ, F.Fv c n s (b + y * I))) := fun b hb =>
    intervalIntegral_tendsto_integral (F.integrable_BInt hc hb n s) tendsto_neg_atTop_atBot
      tendsto_id
  have hL : Tendsto (fun T : ℝ => I * (∫ y in (-T)..T, F.Fv c n s (a + y * I)) -
      I * (∫ y in (-T)..T, F.Fv c n s (a' + y * I))) atTop
      (𝓝 (I * (∫ y : ℝ, F.Fv c n s (a + y * I)) - I * (∫ y : ℝ, F.Fv c n s (a' + y * I)))) :=
    ((hV a ha).const_mul I).sub ((hV a' ha').const_mul I)
  have hR : Tendsto (fun T : ℝ => I * (∫ y in (-T)..T, F.Fv c n s (a + y * I)) -
      I * (∫ y in (-T)..T, F.Fv c n s (a' + y * I))) atTop (𝓝 0) := by
    simp_rw [← hrect]
    simpa using hside_neg.sub hside_pos
  have := tendsto_nhds_unique hL hR
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h' : (∫ y : ℝ, F.Fv c n s (a + y * I)) - ∫ y : ℝ, F.Fv c n s (a' + y * I) = 0 := by
    have : I * ((∫ y : ℝ, F.Fv c n s (a + y * I)) - ∫ y : ℝ, F.Fv c n s (a' + y * I)) = 0 := by
      rw [mul_sub]; exact this
    exact (mul_eq_zero.mp this).resolve_left hI
  exact sub_eq_zero.mp h'

/-! ### Summation over `n` -/

/-- The Gaussian-weighted Dirichlet series of `F` converges absolutely at every `s`: the weight
`e^{-c log² n} n^{2 - Re s}` is bounded and `∑ a(n) n^{-2}` converges absolutely. -/
lemma lseriesSummable_gauss {c : ℝ} (hc : 0 < c) (s : ℂ) :
    LSeriesSummable (fun n => F.a n * DBNFtZero.gaussCoeff c n) s := by
  have h2 : LSeriesSummable F.a 2 := F.summable 2 (by norm_num)
  set Cst : ℝ := Real.exp ((2 - s.re) ^ 2 / (4 * c)) with hCst
  refine Summable.of_norm_bounded (g := fun n => Cst * ‖LSeries.term F.a 2 n‖)
    (h2.norm.mul_left Cst) fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq, ite_eq_right hn, ite_eq_right hn, norm_mul,
    DBNFtZero.gaussCoeff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h2re : ((2 : ℂ)).re = 2 := by norm_num
  rw [h2re]
  set L : ℝ := Real.log n with hL
  have hns : (n : ℝ) ^ s.re = Real.exp (L * s.re) := Real.rpow_def_of_pos hnpos s.re
  have hn2 : (n : ℝ) ^ (2 : ℝ) = Real.exp (L * 2) := Real.rpow_def_of_pos hnpos 2
  rw [hns, hn2, hCst]
  have hkey : Real.exp (-c * L ^ 2) / Real.exp (L * s.re) ≤
      Real.exp ((2 - s.re) ^ 2 / (4 * c)) / Real.exp (L * 2) := by
    rw [← Real.exp_sub, ← Real.exp_sub, Real.exp_le_exp]
    have : (2 - s.re) * L - c * L ^ 2 ≤ (2 - s.re) ^ 2 / (4 * c) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (2 * c * L - (2 - s.re))]
    linarith
  calc ‖F.a n‖ * Real.exp (-c * L ^ 2) / Real.exp (L * s.re)
      = ‖F.a n‖ * (Real.exp (-c * L ^ 2) / Real.exp (L * s.re)) := by ring
    _ ≤ ‖F.a n‖ * (Real.exp ((2 - s.re) ^ 2 / (4 * c)) / Real.exp (L * 2)) :=
        mul_le_mul_of_nonneg_left hkey (norm_nonneg _)
    _ = Real.exp ((2 - s.re) ^ 2 / (4 * c)) * (‖F.a n‖ / Real.exp (L * 2)) := by ring

lemma summable_coef_term {c : ℝ} (hc : 0 < c) (s : ℂ) :
    Summable fun n : ℕ+ => F.a n * (coef c n : ℂ) * (1 / (n : ℂ) ^ s) := by
  have h := F.lseriesSummable_gauss (by positivity : (0 : ℝ) < c / 4) s
  have h2 := (summable_pnat_iff_summable_nat
    (f := fun n : ℕ => LSeries.term (fun n => F.a n * DBNFtZero.gaussCoeff (c / 4) n) s n)).mpr h
  refine h2.congr fun n => ?_
  rw [LSeries.term_of_ne_zero n.ne_zero, coef_eq_gaussCoeff hc]
  ring

/-- `∑_{n ≥ 1} a(n) a_n n^{-s} = F_{c/4}(s)` (Dobner's `F_t` with `|t| = c`). -/
theorem tsum_coef_eq_Ft {c : ℝ} (hc : 0 < c) (s : ℂ) :
    ∑' n : ℕ+, F.a n * (coef c n : ℂ) * (1 / (n : ℂ) ^ s) = F.Ft (c / 4) s := by
  rw [Ft, LSeries, (F.lseriesSummable_gauss (by positivity) s).tsum_eq_zero_add,
    LSeries.term_zero, zero_add,
    ← tsum_pnat_eq_tsum_succ
      (f := fun n : ℕ => LSeries.term (fun n => F.a n * DBNFtZero.gaussCoeff (c / 4) n) s n)]
  congr 1
  funext n
  rw [LSeries.term_of_ne_zero n.ne_zero, coef_eq_gaussCoeff hc]
  ring

/-- **Theorem 4, exact form, for `F`**:
`∑_n B_n(J_F(s)) = γ_t(s) (F_{c/4}(s) + ∑_n a(n) a_n n^{-s} E_n(s))` on any line `Re v = a₀ > 0`,
given that the error series converges. -/
theorem tsum_Bn_J_eq {c M₀ : ℝ} (hc : 0 < c) {s : ℂ} (hb : 0 < (s + M₀).re)
    (hP : F.P.eval (s + M₀) ≠ 0)
    (hsum : Summable fun n : ℕ+ =>
      F.a n * (coef c n : ℂ) * (1 / (n : ℂ) ^ s) * F.EF c M₀ n s)
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∑' n : ℕ+, F.Bn c a₀ n (F.JF c M₀ s) =
      F.γtF c M₀ s * (F.Ft (c / 4) s +
        ∑' n : ℕ+, F.a n * (coef c n : ℂ) * (1 / (n : ℂ) ^ s) * F.EF c M₀ n s) := by
  have hb' : 0 < s.re + M₀ := by simpa using hb
  have hterm : ∀ n : ℕ+, F.Bn c a₀ n (F.JF c M₀ s) =
      F.γtF c M₀ s * (F.a n * (coef c n : ℂ) * (1 / (n : ℂ) ^ s)) +
        F.γtF c M₀ s * (F.a n * (coef c n : ℂ) * (1 / (n : ℂ) ^ s) * F.EF c M₀ n s) := by
    intro n
    rcases le_total a₀ (s.re + M₀ + hh c n) with h | h
    · rw [F.Bn_shift hc ha₀ h n, F.Bn_J_eq hc n hb hP]
      ring
    · rw [← F.Bn_shift hc (by linarith [hh_nonneg hc n]) h n, F.Bn_J_eq hc n hb hP]
      ring
  simp_rw [hterm]
  rw [((F.summable_coef_term hc s).mul_left _).tsum_add (hsum.mul_left _), tsum_mul_left,
    tsum_mul_left, F.tsum_coef_eq_Ft hc, mul_add]

end ExtSelbergData

end DBNSelberg
