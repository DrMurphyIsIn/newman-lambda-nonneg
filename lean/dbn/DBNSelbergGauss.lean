/-
  DBNSelbergGauss -- Dobner's (9) for an element `F` of the extended Selberg class.

  Generalizes DBNGaussConv (the ζ case) to an abstract `F : DBNSelberg.ExtSelbergData`
  (see SELBERG_NEWMAN_DESIGN_2026-10-10.md, row "DBNGaussConv -> DBNSelbergGauss").

  The backward flow `F.flow (-c) z = (4πc)^{-1/2} ∫ e^{-ω²/(4c)} Ξ_F(z + ω) dω` is already the
  definition (DBNSelbergData). Here:

  * `shift_line`: the Gaussian line may be moved vertically (Cauchy on rectangles); the only inputs
    are that `Ξ_F` is entire (`Ξ_differentiable`) and bounded on horizontal strips
    (`Ξ_strip_bounded`).
  * `flow_neg_eq_gauss_shift`: the Gaussian representation with the line at height `β`.
  * `norm_BInt_le`, `integrable_BInt`, `summable_integral_norm_BInt`: the majorant for Dobner's
    integrand `a(n) γ_F(a+iτ) n^{-(a+iτ)} e^{(a+iτ-s)²/c}`, from `norm_gammaF_le`
    (polynomial × `Q^a` × `∏ Γ(λ_j a + Re μ_j)`) and `∑ |a(n)| n^{-a} < ∞` for `a > 1`.
  * `xi_eq_tsum_Bn`: for `c > 0`, `a > 1` and every `s`,
        F.flow (-c) (-i(2s-1)) = ∑_{n ≥ 1} B_n(s),
    `B_n(s) = (πc)^{-1/2} ∫_ℝ a(n) γ_F(a + iτ) n^{-(a+iτ)} e^{(a + iτ - s)²/c} dτ`,
    which is Dobner's (9) for `F` with the contour on `Re v = a`.
  * `norm_gammaF_le_const`: `‖γ_F(x + iτ)‖ ≤ C (1 + |τ|)^{deg P}` uniformly for `x` in a compact
    interval `[a, a'] ⊂ (0, ∞)` (for the contour shift in DBNSelbergSaddleAlg).

  Nothing here is about the zeros of ζ or of any `F`; `conjecture1_proved = False`.
-/
import Mathlib
import DBNGaussConv
import DBNSelbergData

open Complex Filter Topology MeasureTheory Set
open scoped Real

namespace DBNSelberg

namespace ExtSelbergData

variable (F : ExtSelbergData)

/-! ### `Ξ_F` on horizontal strips -/

/-- A bound for `‖Ξ_F‖` on the strip `|Im w| ≤ B`, chosen from `Ξ_strip_bounded`. -/
noncomputable def stripBound (B : ℝ) : ℝ := Classical.choose (F.Ξ_strip_bounded B)

lemma norm_Ξ_le {B : ℝ} {w : ℂ} (hw : |w.im| ≤ B) : ‖F.Ξ w‖ ≤ F.stripBound B :=
  Classical.choose_spec (F.Ξ_strip_bounded B) w hw

lemma stripBound_nonneg {B : ℝ} (hB : 0 ≤ B) : 0 ≤ F.stripBound B :=
  (norm_nonneg _).trans (F.norm_Ξ_le (w := 0) (by simpa using hB))

/-! ### Moving the Gaussian line vertically -/

/-- The entire function `w ↦ e^{-w²/(4c)} Ξ_F(z + w)`. -/
noncomputable def shiftIntegrand (c : ℝ) (z : ℂ) (w : ℂ) : ℂ :=
  cexp (-w ^ 2 / (4 * c)) * F.Ξ (z + w)

lemma differentiable_shiftIntegrand (c : ℝ) (z : ℂ) : Differentiable ℂ (F.shiftIntegrand c z) := by
  unfold shiftIntegrand
  exact ((differentiable_id.pow 2).neg.div_const _).cexp.mul
    (F.Ξ_differentiable.comp (differentiable_id.const_add z))

lemma norm_shiftIntegrand_le {c : ℝ} (z : ℂ) {B : ℝ} (hB : |z.im| ≤ B) (x y : ℝ) (hy : |y| ≤ B) :
    ‖F.shiftIntegrand c z (x + y * I)‖ ≤
      Real.exp ((y ^ 2 - x ^ 2) / (4 * c)) * F.stripBound (2 * B) := by
  rw [shiftIntegrand, norm_mul, DBNGaussConv.norm_cexp_neg_sq_div]
  gcongr
  apply F.norm_Ξ_le
  rw [Complex.add_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  simp only [mul_one, mul_zero, add_zero, zero_add]
  calc |z.im + y| ≤ |z.im| + |y| := abs_add_le _ _
    _ ≤ B + B := add_le_add hB hy
    _ = 2 * B := by ring

lemma integrable_shiftIntegrand_line {c : ℝ} (hc : 0 < c) (z : ℂ) (β : ℝ) :
    Integrable fun x : ℝ => F.shiftIntegrand c z (x + β * I) := by
  set B := |z.im| + |β| with hB
  have hcont : Continuous fun x : ℝ => F.shiftIntegrand c z (x + β * I) :=
    (F.differentiable_shiftIntegrand c z).continuous.comp (by fun_prop)
  refine ((DBNGaussConv.integrable_gaussK hc).norm.const_mul
    (Real.exp (β ^ 2 / (4 * c)) * F.stripBound (2 * B))).mono'
    hcont.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have h := F.norm_shiftIntegrand_le (c := c) z (B := B)
    (by rw [hB]; exact le_add_of_nonneg_right (abs_nonneg _)) x β
    (by rw [hB]; exact le_add_of_nonneg_left (abs_nonneg _))
  refine h.trans (le_of_eq ?_)
  rw [DBNGaussConv.gaussKer, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    show (β ^ 2 - x ^ 2) / (4 * c) = β ^ 2 / (4 * c) + -x ^ 2 / (4 * c) by ring, Real.exp_add]
  ring

/-- **Cauchy**: the Gaussian line may be moved vertically (`shiftIntegrand` form). -/
theorem shift_line_shiftIntegrand {c : ℝ} (hc : 0 < c) (z : ℂ) (β : ℝ) :
    ∫ x : ℝ, F.shiftIntegrand c z x = ∫ x : ℝ, F.shiftIntegrand c z (x + β * I) := by
  set B := |z.im| + |β| with hB
  set K := F.stripBound (2 * B) with hK
  have hK0 : 0 ≤ K := F.stripBound_nonneg (by positivity)
  -- the rectangle identity for each T
  have hrect : ∀ T : ℝ,
      (∫ x in (-T)..T, F.shiftIntegrand c z x) -
          (∫ x in (-T)..T, F.shiftIntegrand c z (x + β * I)) =
        I * (∫ y in (0 : ℝ)..β, F.shiftIntegrand c z (-T + y * I)) -
          I * (∫ y in (0 : ℝ)..β, F.shiftIntegrand c z (T + y * I)) := by
    intro T
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (F.shiftIntegrand c z)
      ⟨-T, 0⟩ ⟨T, β⟩ (F.differentiable_shiftIntegrand c z).differentiableOn
    simp only [Complex.ofReal_zero, zero_mul, add_zero, smul_eq_mul, Complex.ofReal_neg] at h
    linear_combination h
  -- the vertical sides tend to zero
  have hvert : ∀ T X : ℝ, X ^ 2 = T ^ 2 →
      ‖∫ y in (0 : ℝ)..β, F.shiftIntegrand c z (X + y * I)‖ ≤
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
    have h := F.norm_shiftIntegrand_le (c := c) z (B := B)
      (by rw [hB]; exact le_add_of_nonneg_right (abs_nonneg _)) X y hyB
    refine h.trans ?_
    rw [hX]
    refine mul_le_mul_of_nonneg_right ?_ hK0
    refine Real.exp_le_exp.mpr (div_le_div_of_nonneg_right ?_ (by positivity))
    have := sq_le_sq.mpr hy'
    linarith
  have hexp : Tendsto (fun T : ℝ => Real.exp ((β ^ 2 - T ^ 2) / (4 * c)) * K * |β|) atTop
      (𝓝 0) := by
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
  have hL : Tendsto (fun T : ℝ => (∫ x in (-T)..T, F.shiftIntegrand c z x) -
      ∫ x in (-T)..T, F.shiftIntegrand c z (x + β * I)) atTop
      (𝓝 ((∫ x : ℝ, F.shiftIntegrand c z x) - ∫ x : ℝ, F.shiftIntegrand c z (x + β * I))) := by
    have hi0 : Integrable fun x : ℝ => F.shiftIntegrand c z x := by
      have := F.integrable_shiftIntegrand_line hc z 0
      simpa using this
    exact (intervalIntegral_tendsto_integral hi0 tendsto_neg_atTop_atBot tendsto_id).sub
      (intervalIntegral_tendsto_integral (F.integrable_shiftIntegrand_line hc z β)
        tendsto_neg_atTop_atBot tendsto_id)
  have hR : Tendsto (fun T : ℝ => (∫ x in (-T)..T, F.shiftIntegrand c z x) -
      ∫ x in (-T)..T, F.shiftIntegrand c z (x + β * I)) atTop (𝓝 0) := by
    simp_rw [hrect]
    rw [show (0 : ℂ) = I * 0 - I * 0 by simp]
    refine Tendsto.sub (Tendsto.const_mul I ?_) (Tendsto.const_mul I ?_)
    · refine squeeze_zero_norm (fun T => ?_) hexp
      have := hvert T (-T) (neg_sq T)
      simpa using this
    · exact squeeze_zero_norm (fun T => hvert T T rfl) hexp
  have := tendsto_nhds_unique hL hR
  exact sub_eq_zero.mp this

/-- **Cauchy**: the Gaussian line may be moved vertically. -/
theorem shift_line {c : ℝ} (hc : 0 < c) (z : ℂ) (β : ℝ) :
    ∫ x : ℝ, cexp (-(x : ℂ) ^ 2 / (4 * c)) * F.Ξ (z + x) =
      ∫ x : ℝ, cexp (-((x : ℂ) + β * I) ^ 2 / (4 * c)) * F.Ξ (z + (x + β * I)) := by
  have h := F.shift_line_shiftIntegrand hc z β
  unfold shiftIntegrand at h
  exact h

/-- The Gaussian representation with the line moved to height `β`. -/
theorem flow_neg_eq_gauss_shift {c : ℝ} (hc : 0 < c) (z : ℂ) (β : ℝ) :
    F.flow (-c) z = (1 / ((Real.sqrt (4 * π * c) : ℝ) : ℂ)) *
      ∫ ω : ℝ, cexp (-((ω : ℂ) + β * I) ^ 2 / (4 * c)) * F.Ξ (z + ω + β * I) := by
  simp only [flow, neg_neg]
  congr 1
  have h := F.shift_line hc z β
  have e1 : (fun ω : ℝ => DBNGaussConv.gaussKer c ω * F.Ξ (z + ω)) =
      fun x : ℝ => cexp (-(x : ℂ) ^ 2 / (4 * c)) * F.Ξ (z + x) := by
    funext ω; rw [DBNGaussConv.gaussK_eq]; congr 2; ring
  have e2 : (fun ω : ℝ => cexp (-((ω : ℂ) + β * I) ^ 2 / (4 * c)) * F.Ξ (z + ω + β * I)) =
      fun x : ℝ => cexp (-((x : ℂ) + β * I) ^ 2 / (4 * c)) * F.Ξ (z + (x + β * I)) := by
    funext ω; rw [add_assoc]
  rw [e1, e2]
  exact h

/-! ### The majorant for `BInt` -/

/-- The polynomial factor of the bound `norm_gammaF_le`. -/
noncomputable def polyBound (a τ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (F.P.natDegree + 1), ‖F.P.coeff k‖ * (a + |τ|) ^ k

/-- The `τ`-independent factor of the bound `norm_gammaF_le`: `Q^a ∏_j Γ(λ_j a + Re μ_j)`. -/
noncomputable def gammaBound (a : ℝ) : ℝ :=
  F.Q ^ a * ∏ j, Real.Gamma (F.lam j * a + (F.mu j).re)

/-- The majorant of `‖BInt c a n s τ‖` without the factors `‖a(n)‖ n^{-a}`. -/
noncomputable def majorant (c a : ℝ) (s : ℂ) (τ : ℝ) : ℝ :=
  F.polyBound a τ * F.gammaBound a * Real.exp (((a - s.re) ^ 2 - (τ - s.im) ^ 2) / c)

lemma polyBound_nonneg {a : ℝ} (ha : 0 ≤ a) (τ : ℝ) : 0 ≤ F.polyBound a τ :=
  Finset.sum_nonneg fun k _ => by positivity

lemma gammaBound_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ F.gammaBound a := by
  unfold gammaBound
  refine mul_nonneg (Real.rpow_nonneg F.Q_pos.le a) (Finset.prod_nonneg fun j _ => ?_)
  refine Real.Gamma_nonneg_of_nonneg ?_
  have := F.lam_pos j
  have := F.mu_re_nonneg j
  positivity

lemma majorant_nonneg {a : ℝ} (ha : 0 ≤ a) (c : ℝ) (s : ℂ) (τ : ℝ) : 0 ≤ F.majorant c a s τ := by
  unfold majorant
  have := F.polyBound_nonneg ha τ
  have := F.gammaBound_nonneg ha
  positivity

lemma continuous_polyBound (a : ℝ) : Continuous (F.polyBound a) := by
  unfold polyBound
  fun_prop

lemma continuous_majorant (c a : ℝ) (s : ℂ) : Continuous (F.majorant c a s) := by
  unfold majorant
  have := F.continuous_polyBound a
  fun_prop

lemma norm_BInt_le (c : ℝ) {a : ℝ} (ha : 0 < a) (n : ℕ+) (s : ℂ) (τ : ℝ) :
    ‖F.BInt c a n s τ‖ ≤
      ‖F.a n‖ * ((∑ k ∈ Finset.range (F.P.natDegree + 1), ‖F.P.coeff k‖ * (a + |τ|) ^ k) *
        F.Q ^ a * ∏ j, Real.Gamma (F.lam j * a + (F.mu j).re)) *
        (n : ℝ) ^ (-a) * Real.exp (((a - s.re) ^ 2 - (τ - s.im) ^ 2) / c) := by
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
  gcongr
  exact F.norm_gammaF_le ha τ

lemma norm_BInt_le_majorant (c : ℝ) {a : ℝ} (ha : 0 < a) (n : ℕ+) (s : ℂ) (τ : ℝ) :
    ‖F.BInt c a n s τ‖ ≤ ‖F.a n‖ * (n : ℝ) ^ (-a) * F.majorant c a s τ := by
  have := F.norm_BInt_le c ha n s τ
  unfold majorant polyBound gammaBound
  linarith [this]

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

/-! ### Integrability of the majorant -/

/-- `(x + y)^k ≤ 2^k (x^k + y^k)` for `x, y ≥ 0`. -/
lemma add_pow_le_two_pow_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (k : ℕ) :
    (x + y) ^ k ≤ 2 ^ k * (x ^ k + y ^ k) := by
  have h1 : x + y ≤ 2 * max x y := by
    have := le_max_left x y
    have := le_max_right x y
    linarith
  calc (x + y) ^ k ≤ (2 * max x y) ^ k := pow_le_pow_left₀ (by positivity) h1 k
    _ = 2 ^ k * (max x y) ^ k := mul_pow _ _ _
    _ ≤ 2 ^ k * (x ^ k + y ^ k) := by
      gcongr
      rcases le_total x y with h | h
      · rw [max_eq_right h]
        exact le_add_of_nonneg_left (by positivity)
      · rw [max_eq_left h]
        exact le_add_of_nonneg_right (by positivity)

/-- `|u|^k e^{-b u²}` is integrable for `b > 0`. -/
lemma integrable_abs_pow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) (k : ℕ) :
    Integrable fun u : ℝ => |u| ^ k * Real.exp (-b * u ^ 2) := by
  have hs : (-1 : ℝ) < (k : ℝ) := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have h := (integrable_rpow_mul_exp_neg_mul_sq hb hs).norm
  refine h.congr (ae_of_all _ fun u => ?_)
  simp only [Real.rpow_natCast, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]

/-- `(a + |τ|)^k e^{-(τ - y)²/c}` is integrable for `c > 0`, `a ≥ 0`. -/
lemma integrable_pow_mul_gauss {c : ℝ} (hc : 0 < c) {a : ℝ} (ha : 0 ≤ a) (k : ℕ) (y : ℝ) :
    Integrable fun τ : ℝ => (a + |τ|) ^ k * Real.exp (-(τ - y) ^ 2 / c) := by
  set A : ℝ := a + |y| with hA
  have hA0 : 0 ≤ A := by positivity
  have hb : (0 : ℝ) < 1 / c := by positivity
  have hg : Integrable fun u : ℝ => 2 ^ k * (A ^ k + |u| ^ k) * Real.exp (-(1 / c) * u ^ 2) := by
    have h1 := (integrable_exp_neg_mul_sq hb).const_mul (2 ^ k * A ^ k)
    have h2 := (integrable_abs_pow_mul_exp_neg_mul_sq hb k).const_mul (2 ^ k)
    refine (h1.add h2).congr (ae_of_all _ fun u => ?_)
    simp only [Pi.add_apply]
    ring
  have hg' := hg.comp_sub_right y
  have hcont : Continuous fun τ : ℝ => (a + |τ|) ^ k * Real.exp (-(τ - y) ^ 2 / c) := by
    fun_prop
  refine hg'.mono' hcont.aestronglyMeasurable (ae_of_all _ fun τ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  set u : ℝ := τ - y with hu
  have h1 : a + |τ| ≤ A + |u| := by
    have : |τ| ≤ |u| + |y| := by
      rw [hu]
      calc |τ| = |(τ - y) + y| := by ring_nf
        _ ≤ |τ - y| + |y| := abs_add_le _ _
    rw [hA]
    linarith
  have hpow : (a + |τ|) ^ k ≤ 2 ^ k * (A ^ k + |u| ^ k) :=
    (pow_le_pow_left₀ (by positivity) h1 k).trans (add_pow_le_two_pow_mul hA0 (abs_nonneg u) k)
  have hexp : Real.exp (-(τ - y) ^ 2 / c) = Real.exp (-(1 / c) * u ^ 2) := by
    rw [hu]
    congr 1
    field_simp
  rw [hexp]
  exact mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le

/-- The polynomial-times-Gaussian majorant is integrable. -/
lemma integrable_majorant {c : ℝ} (hc : 0 < c) {a : ℝ} (ha : 0 < a) (s : ℂ) :
    Integrable (F.majorant c a s) := by
  have hsplit : ∀ τ : ℝ, F.majorant c a s τ =
      ∑ k ∈ Finset.range (F.P.natDegree + 1),
        (‖F.P.coeff k‖ * F.gammaBound a * Real.exp ((a - s.re) ^ 2 / c)) *
          ((a + |τ|) ^ k * Real.exp (-(τ - s.im) ^ 2 / c)) := by
    intro τ
    unfold majorant polyBound
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show ((a - s.re) ^ 2 - (τ - s.im) ^ 2) / c = (a - s.re) ^ 2 / c + -(τ - s.im) ^ 2 / c by
      ring, Real.exp_add]
    ring
  have : F.majorant c a s = fun τ => ∑ k ∈ Finset.range (F.P.natDegree + 1),
      (‖F.P.coeff k‖ * F.gammaBound a * Real.exp ((a - s.re) ^ 2 / c)) *
        ((a + |τ|) ^ k * Real.exp (-(τ - s.im) ^ 2 / c)) := funext hsplit
  rw [this]
  refine integrable_finsetSum _ fun k _ => ?_
  exact (integrable_pow_mul_gauss hc ha.le k s.im).const_mul _

lemma integrable_BInt {c : ℝ} (hc : 0 < c) {a : ℝ} (ha : 0 < a) (n : ℕ+) (s : ℂ) :
    Integrable (F.BInt c a n s) := by
  refine ((F.integrable_majorant hc ha s).const_mul (‖F.a n‖ * (n : ℝ) ^ (-a))).mono'
    (F.continuous_BInt c ha n s).aestronglyMeasurable (ae_of_all _ fun τ => ?_)
  exact F.norm_BInt_le_majorant c ha n s τ

/-- `∑_{n ≥ 1} ‖a(n)‖ n^{-a} < ∞` for `a > 1`, from the `summable` field at the real point `a`. -/
lemma summable_norm_a_mul_rpow {a : ℝ} (ha : 1 < a) :
    Summable fun n : ℕ+ => ‖F.a n‖ * (n : ℝ) ^ (-a) := by
  have h := (F.summable (a : ℂ) (by simpa using ha)).norm
  have h2 := (summable_pnat_iff_summable_nat
    (f := fun n : ℕ => ‖LSeries.term F.a (a : ℂ) n‖)).mpr h
  refine h2.congr fun n => ?_
  rw [LSeries.norm_term_eq, ite_eq_right n.ne_zero, Complex.ofReal_re, Real.rpow_neg (by positivity),
    div_eq_mul_inv]

lemma summable_integral_norm_BInt {c : ℝ} (hc : 0 < c) {a : ℝ} (ha : 1 < a) (s : ℂ) :
    Summable fun n : ℕ+ => ∫ τ : ℝ, ‖F.BInt c a n s τ‖ := by
  have ha0 : 0 < a := by linarith
  refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun τ => norm_nonneg _) (fun n => ?_)
    ((F.summable_norm_a_mul_rpow ha).mul_right (∫ τ : ℝ, F.majorant c a s τ))
  rw [← MeasureTheory.integral_const_mul]
  refine integral_mono (F.integrable_BInt hc ha0 n s).norm
    ((F.integrable_majorant hc ha0 s).const_mul _) fun τ => ?_
  exact F.norm_BInt_le_majorant c ha0 n s τ

/-! ### Dobner's (9) for `F` -/

lemma Bn_eq_integral_BInt (c a : ℝ) (n : ℕ+) (s : ℂ) :
    F.Bn c a n s = (1 / ((Real.sqrt (π * c) : ℝ) : ℂ)) * ∫ τ : ℝ, F.BInt c a n s τ := rfl

/-- **Dobner's (9) for `F`**: for `c > 0`, `a > 1` and every `s`,
`F.flow (-c) (-i(2s-1)) = ∑_{n ≥ 1} B_n(s)`. -/
theorem xi_eq_tsum_Bn {c : ℝ} (hc : 0 < c) {a : ℝ} (ha : 1 < a) (s : ℂ) :
    F.flow (-c) (-I * (2 * s - 1)) = ∑' n : ℕ+, F.Bn c a n s := by
  have ha0 : 0 < a := by linarith
  set z : ℂ := -I * (2 * s - 1) with hz
  set β : ℝ := 2 * (s.re - a) with hβ
  -- the shifted point in the `s`-variable
  have hpt : ∀ ω : ℝ, z + ω + β * I =
      -I * (2 * ((a : ℂ) + ((s.im + ω / 2 : ℝ) : ℂ) * I) - 1) := by
    intro ω
    rw [hz, hβ]
    apply Complex.ext <;> simp <;> ring
  have hre : ∀ ω : ℝ, 1 < ((a : ℂ) + ((s.im + ω / 2 : ℝ) : ℂ) * I).re := by
    intro ω
    simpa using ha
  have hG : ∀ ω : ℝ, cexp (-((ω : ℂ) + β * I) ^ 2 / (4 * c)) * F.Ξ (z + ω + β * I) =
      ∑' n : ℕ+, F.BInt c a n s (s.im + ω / 2) := by
    intro ω
    rw [hpt ω, F.Ξ_eq_tsum_gammaF (hre ω), ← tsum_mul_left]
    congr 1
    funext n
    rw [BInt]
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
  rw [F.flow_neg_eq_gauss_shift hc z β]
  simp_rw [hG]
  have hsub := DBNGaussConv.integral_comp_half_add (fun τ => ∑' n : ℕ+, F.BInt c a n s τ) s.im
  rw [hsub, ← (hasSum_integral_of_summable_integral_norm (F.integrable_BInt hc ha0 · s)
    (F.summable_integral_norm_BInt hc ha s)).tsum_eq, ← tsum_mul_left, ← tsum_mul_left]
  congr 1
  funext n
  rw [Bn]
  have h4 : Real.sqrt (4 * π * c) = 2 * Real.sqrt (π * c) := by
    rw [show 4 * π * c = 2 ^ 2 * (π * c) by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [h4]
  push_cast
  have : ((Real.sqrt (π * c) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp

/-! ### `γ_F` on a compact range of abscissas -/

/-- `‖γ_F(x + iτ)‖ ≤ C (1 + |τ|)^{deg P}` uniformly for `x ∈ [a, a']`, `0 < a ≤ a'`. -/
lemma norm_gammaF_le_const {a a' : ℝ} (ha : 0 < a) (_haa : a ≤ a') :
    ∃ C : ℝ, ∀ x ∈ Set.Icc a a', ∀ τ : ℝ,
      ‖F.gammaF ((x : ℂ) + τ * I)‖ ≤ C * (1 + |τ|) ^ F.P.natDegree := by
  set d := F.P.natDegree with hd
  set S : ℝ := ∑ k ∈ Finset.range (d + 1), ‖F.P.coeff k‖ with hS
  set M : ℝ := max a' 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  have ha'M : a' ≤ M := le_max_left _ _
  -- the `τ`-independent factor is continuous on the compact interval
  have hcont : ContinuousOn F.gammaBound (Set.Icc a a') := by
    unfold gammaBound
    refine ContinuousOn.mul ?_ ?_
    · exact continuousOn_of_forall_continuousAt fun x _ =>
        Real.continuousAt_const_rpow F.Q_pos.ne'
    · refine continuousOn_finsetProd _ fun j _ => ?_
      refine continuousOn_of_forall_continuousAt fun x hx => ?_
      have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
      refine (Real.differentiableAt_Gamma fun m => ?_).continuousAt.comp (by fun_prop)
      have := F.lam_pos j
      have := F.mu_re_nonneg j
      have hpos : 0 < F.lam j * x + (F.mu j).re := by positivity
      intro h
      rw [h] at hpos
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  obtain ⟨Cg, hCg⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨S * M ^ d * Cg, fun x hx τ => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
  have hbound := F.norm_gammaF_le hx0 τ
  have hgB : F.gammaBound x ≤ Cg := (le_abs_self _).trans (hCg x hx)
  have hgB0 : 0 ≤ F.gammaBound x := F.gammaBound_nonneg hx0.le
  -- the polynomial factor
  have hxτ : x + |τ| ≤ M * (1 + |τ|) := by
    have hx' : x ≤ M := hx.2.trans ha'M
    nlinarith [abs_nonneg τ]
  have hM1' : 1 ≤ M * (1 + |τ|) :=
    one_le_mul_of_one_le_of_one_le hM1 (by linarith [abs_nonneg τ])
  have hpoly : ∑ k ∈ Finset.range (d + 1), ‖F.P.coeff k‖ * (x + |τ|) ^ k ≤
      S * (M ^ d * (1 + |τ|) ^ d) := by
    rw [hS, Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    have hkd : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc (x + |τ|) ^ k ≤ (M * (1 + |τ|)) ^ k := pow_le_pow_left₀ (by positivity) hxτ k
      _ ≤ (M * (1 + |τ|)) ^ d := pow_le_pow_right₀ hM1' hkd
      _ = M ^ d * (1 + |τ|) ^ d := mul_pow _ _ _
  have hS0 : 0 ≤ S * (M ^ d * (1 + |τ|) ^ d) := by
    have : 0 ≤ S := Finset.sum_nonneg fun k _ => norm_nonneg _
    positivity
  calc ‖F.gammaF ((x : ℂ) + τ * I)‖
      ≤ (∑ k ∈ Finset.range (d + 1), ‖F.P.coeff k‖ * (x + |τ|) ^ k) *
        F.Q ^ x * ∏ j, Real.Gamma (F.lam j * x + (F.mu j).re) := hbound
    _ = (∑ k ∈ Finset.range (d + 1), ‖F.P.coeff k‖ * (x + |τ|) ^ k) * F.gammaBound x := by
        rw [gammaBound, mul_assoc]
    _ ≤ (S * (M ^ d * (1 + |τ|) ^ d)) * Cg := mul_le_mul hpoly hgB hgB0 hS0
    _ = S * M ^ d * Cg * (1 + |τ|) ^ d := by ring

end ExtSelbergData

end DBNSelberg
