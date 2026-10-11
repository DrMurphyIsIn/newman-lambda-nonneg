/-
# The completed function of an element of `S^#` is bounded on every vertical strip

`DBNSelbergSharpXi` makes `xi_F` an entire function of finite order with the functional equation
`xi(s) = ω conj(xi(1 - conj s))`. This module proves the last analytic input Dobner's argument
needs, boundedness on vertical strips, and assembles the conversion `SelbergSharp → ExtSelbergData`:

* on `2 ≤ Re s ≤ σ₁` (`exists_bound_xi_right`) the Dirichlet series is bounded by its absolute
  value at `s = 2`, `‖Q^s‖ = Q^{Re s}` is bounded, `(s(s-1))^m` is a polynomial in `|Im s|`, and
  each Gamma factor decays like `(1+|Im s|)^{N_j} e^{-(π/2) λ_j |Im s|}` (`DBNGammaVertical`); the
  product decays like `e^{-(π/2)(∑ λ_j)|Im s|}` with `∑ λ_j > 0`, beating the polynomial
  (`pow_mul_exp_neg_le`: `(1+y)^N e^{-cy} ≤ N! e^c / c^N`);
* on `σ₀ ≤ Re s ≤ -1` (`exists_bound_xi_left`) by the functional equation;
* on `-1 ≤ Re s ≤ 2` (`exists_bound_xi_strip`) by Phragmén–Lindelöf
  (`PhragmenLindelof.vertical_strip`), the growth hypothesis `exp(B exp(|Im s|))` coming from
  finite order (`‖s‖^ρ ≤ (2+|Im s|)^N ≤ N! e^2 e^{|Im s|}` on the strip);
* every vertical strip (`exists_bound_xi_vertical`) by combining the three.

Then `toExtSelbergData` with `Ξ z := xi(1/2 + iz/2)` and the root-level `selberg_newman_sharp`:
Newman's conjecture for `S^#` as `DBNSelbergNewman.selberg_newman` states it. Nothing here is about
`Λ_F = 0`; `conjecture1_proved = False`.
-/
import Mathlib
import DBNSelbergSharp
import DBNSelbergSharpXi
import DBNGammaVertical
import DBNSelbergData
import DBNSelbergNewman
import Hadamard.Basic

open Complex Filter Topology Set
open scoped Real ComplexConjugate

namespace DBNSelberg

namespace SelbergSharp

variable (S : SelbergSharp)

/-! ### A polynomial times a decaying exponential is bounded -/

/-- `(1+y)^N e^{-cy} ≤ N! e^c / c^N` for `y ≥ 0`, `c > 0`: from `x^N / N! ≤ e^x` at `x = c(1+y)`. -/
lemma pow_mul_exp_neg_le {c : ℝ} (hc : 0 < c) (N : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    (1 + y) ^ N * Real.exp (-(c * y)) ≤ (N.factorial : ℝ) * Real.exp c / c ^ N := by
  have h1 := Real.pow_div_factorial_le_exp (x := c * (1 + y)) (by positivity) N
  have hfac : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  have hcN : 0 < c ^ N := pow_pos hc N
  rw [div_le_iff₀ hfac, mul_pow] at h1
  have h2 : Real.exp (c * (1 + y)) = Real.exp c * Real.exp (c * y) := by
    rw [← Real.exp_add]; ring_nf
  rw [h2] at h1
  rw [le_div_iff₀ hcN]
  have h3 : (1 + y) ^ N * Real.exp (-(c * y)) * c ^ N =
      (c ^ N * (1 + y) ^ N) * Real.exp (-(c * y)) := by ring
  rw [h3]
  calc (c ^ N * (1 + y) ^ N) * Real.exp (-(c * y))
      ≤ (Real.exp c * Real.exp (c * y) * N.factorial) * Real.exp (-(c * y)) := by
        gcongr
    _ = N.factorial * Real.exp c * (Real.exp (c * y) * Real.exp (-(c * y))) := by ring
    _ = N.factorial * Real.exp c := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-! ### The Dirichlet series on `Re s ≥ 2` -/

/-- `‖L(a, s)‖ ≤ ∑ ‖a(n)‖ n^{-2}` for `Re s ≥ 2`. -/
lemma norm_LSeries_le_of_two_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖LSeries S.a s‖ ≤ ∑' n, ‖LSeries.term S.a 2 n‖ := by
  have h2 : LSeriesSummable S.a 2 := S.summable 2 (by norm_num)
  have hsum : LSeriesSummable S.a s := S.summable s (by linarith)
  have hle : ∀ n, ‖LSeries.term S.a s n‖ ≤ ‖LSeries.term S.a 2 n‖ := fun n =>
    LSeries.norm_term_le_of_re_le_re S.a (by simpa using hs) n
  calc ‖LSeries S.a s‖ = ‖∑' n, LSeries.term S.a s n‖ := rfl
    _ ≤ ∑' n, ‖LSeries.term S.a s n‖ := norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n, ‖LSeries.term S.a 2 n‖ := hsum.norm.tsum_le_tsum hle h2.norm

/-! ### The elementary factors on `2 ≤ Re s ≤ σ₁` -/

/-- `‖Q^s‖ = Q^{Re s} ≤ exp(σ₁ |log Q|)` for `0 ≤ Re s ≤ σ₁`. -/
lemma norm_Q_cpow_le {σ₁ : ℝ} {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ σ₁) :
    ‖((S.Q : ℝ) : ℂ) ^ s‖ ≤ Real.exp (σ₁ * |Real.log S.Q|) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos S.Q_pos, Real.rpow_def_of_pos S.Q_pos, Real.exp_le_exp]
  calc Real.log S.Q * s.re ≤ |Real.log S.Q * s.re| := le_abs_self _
    _ = |Real.log S.Q| * s.re := by rw [abs_mul, abs_of_nonneg h0]
    _ ≤ |Real.log S.Q| * σ₁ := by gcongr
    _ = σ₁ * |Real.log S.Q| := mul_comm _ _

/-- `‖(s(s-1))^m‖ ≤ (σ₁(σ₁+1))^m (1 + |Im s|)^{2m}` for `0 ≤ Re s ≤ σ₁`, `1 ≤ σ₁`. -/
lemma norm_pole_pow_le {σ₁ : ℝ} (hσ : 1 ≤ σ₁) {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ σ₁) :
    ‖(s * (s - 1)) ^ S.m‖ ≤ (σ₁ * (σ₁ + 1)) ^ S.m * (1 + |s.im|) ^ (2 * S.m) := by
  have hτ : 0 ≤ |s.im| := abs_nonneg _
  have hs : ‖s‖ ≤ σ₁ * (1 + |s.im|) := by
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ = s.re + |s.im| := by rw [abs_of_nonneg h0]
      _ ≤ σ₁ + |s.im| := by linarith
      _ ≤ σ₁ * (1 + |s.im|) := by nlinarith
  have hs1 : ‖s - 1‖ ≤ (σ₁ + 1) * (1 + |s.im|) := by
    calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖s‖ + 1 := by rw [norm_one]
      _ ≤ σ₁ * (1 + |s.im|) + 1 := by linarith
      _ ≤ (σ₁ + 1) * (1 + |s.im|) := by nlinarith
  have hprod : ‖s * (s - 1)‖ ≤ σ₁ * (σ₁ + 1) * (1 + |s.im|) ^ 2 := by
    rw [norm_mul]
    calc ‖s‖ * ‖s - 1‖ ≤ (σ₁ * (1 + |s.im|)) * ((σ₁ + 1) * (1 + |s.im|)) := by gcongr
      _ = σ₁ * (σ₁ + 1) * (1 + |s.im|) ^ 2 := by ring
  rw [norm_pow, pow_mul, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hprod S.m

/-! ### The Gamma factors on `2 ≤ Re s ≤ σ₁` -/

/-- One Gamma factor: `‖Γ(λ_j s + μ_j)‖ ≤ A (1 + |Im s|)^N e^{-(π/2) λ_j |Im s|}` uniformly on
`2 ≤ Re s ≤ σ₁`. -/
lemma exists_bound_Gamma_factor {σ₁ : ℝ} (hσ : 2 ≤ σ₁) (j : Fin S.r) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ N : ℕ, ∀ s : ℂ, 2 ≤ s.re → s.re ≤ σ₁ →
      ‖Complex.Gamma (S.lam j * s + S.mu j)‖ ≤
        A * (1 + |s.im|) ^ N * Real.exp (-(Real.pi / 2 * S.lam j * |s.im|)) := by
  have hlam := S.lam_pos j
  have hmu := S.mu_re_nonneg j
  set a := 2 * S.lam j + (S.mu j).re with ha
  set b := σ₁ * S.lam j + (S.mu j).re with hb
  have ha0 : 0 < a := by positivity
  have hab : a ≤ b := by rw [ha, hb]; nlinarith
  have hb0 : 0 ≤ b := ha0.le.trans hab
  obtain ⟨C, hC0, hC⟩ := DBNStirling.norm_Gamma_le_vertical ha0 hab
  set N : ℕ := ⌈b⌉₊ with hN
  set D : ℝ := 1 + S.lam j + |(S.mu j).im| with hD
  have hD1 : 1 ≤ D := by rw [hD]; linarith [abs_nonneg (S.mu j).im]
  refine ⟨C * D ^ N * Real.exp (Real.pi / 2 * |(S.mu j).im|), by positivity, N, fun s hs2 hs1 => ?_⟩
  set w := S.lam j * s + S.mu j with hw
  have hwre : w.re = S.lam j * s.re + (S.mu j).re := by rw [hw]; simp
  have hwim : w.im = S.lam j * s.im + (S.mu j).im := by rw [hw]; simp
  have hw0 : a ≤ w.re := by rw [hwre, ha]; nlinarith
  have hw1 : w.re ≤ b := by rw [hwre, hb]; nlinarith
  have hGam := hC w hw0 hw1
  have hτ0 : 0 ≤ |s.im| := abs_nonneg _
  -- the polynomial factor
  have hpoly : (1 + |w.im|) ^ b ≤ D ^ N * (1 + |s.im|) ^ N := by
    have h1 : 1 + |w.im| ≤ D * (1 + |s.im|) := by
      rw [hwim, hD]
      have : |S.lam j * s.im + (S.mu j).im| ≤ S.lam j * |s.im| + |(S.mu j).im| := by
        calc |S.lam j * s.im + (S.mu j).im| ≤ |S.lam j * s.im| + |(S.mu j).im| := abs_add_le _ _
          _ = S.lam j * |s.im| + |(S.mu j).im| := by rw [abs_mul, abs_of_pos hlam]
      nlinarith [abs_nonneg (S.mu j).im]
    have h2 : (1 + |w.im|) ^ b ≤ (1 + |w.im|) ^ (N : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg w.im]) (Nat.le_ceil b)
    rw [Real.rpow_natCast, ← mul_pow] at *
    exact h2.trans (pow_le_pow_left₀ (by linarith [abs_nonneg w.im]) h1 N)
  -- the exponential factor
  have hexp : Real.exp (-(Real.pi / 2) * |w.im|) ≤
      Real.exp (Real.pi / 2 * |(S.mu j).im|) * Real.exp (-(Real.pi / 2 * S.lam j * |s.im|)) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have : S.lam j * |s.im| ≤ |w.im| + |(S.mu j).im| := by
      have h := abs_add_le w.im (-(S.mu j).im)
      rw [abs_neg] at h
      have h' : w.im + -(S.mu j).im = S.lam j * s.im := by rw [hwim]; ring
      rw [h', abs_mul, abs_of_pos hlam] at h
      exact h
    nlinarith [Real.pi_pos]
  calc ‖Complex.Gamma w‖ ≤ C * (1 + |w.im|) ^ b * Real.exp (-(Real.pi / 2) * |w.im|) := hGam
    _ ≤ C * (D ^ N * (1 + |s.im|) ^ N) *
        (Real.exp (Real.pi / 2 * |(S.mu j).im|) * Real.exp (-(Real.pi / 2 * S.lam j * |s.im|))) := by
        gcongr
    _ = C * D ^ N * Real.exp (Real.pi / 2 * |(S.mu j).im|) * (1 + |s.im|) ^ N *
        Real.exp (-(Real.pi / 2 * S.lam j * |s.im|)) := by ring

/-- The Gamma product: `‖∏ Γ(λ_j s + μ_j)‖ ≤ A (1 + |Im s|)^N e^{-(π/2)(∑ λ_j)|Im s|}` on
`2 ≤ Re s ≤ σ₁`. -/
lemma exists_bound_Gamma_prod {σ₁ : ℝ} (hσ : 2 ≤ σ₁) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ N : ℕ, ∀ s : ℂ, 2 ≤ s.re → s.re ≤ σ₁ →
      ‖∏ j, Complex.Gamma (S.lam j * s + S.mu j)‖ ≤
        A * (1 + |s.im|) ^ N * Real.exp (-(Real.pi / 2 * (∑ j, S.lam j) * |s.im|)) := by
  choose A hA0 N hAN using S.exists_bound_Gamma_factor hσ
  refine ⟨∏ j, A j, Finset.prod_nonneg fun j _ => hA0 j, ∑ j, N j, fun s hs2 hs1 => ?_⟩
  rw [norm_prod]
  calc ∏ j, ‖Complex.Gamma (S.lam j * s + S.mu j)‖
      ≤ ∏ j, (A j * (1 + |s.im|) ^ N j * Real.exp (-(Real.pi / 2 * S.lam j * |s.im|))) :=
        Finset.prod_le_prod (fun j _ => norm_nonneg _) fun j _ => hAN j s hs2 hs1
    _ = (∏ j, A j) * (∏ j, (1 + |s.im|) ^ N j) *
        ∏ j, Real.exp (-(Real.pi / 2 * S.lam j * |s.im|)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ = (∏ j, A j) * (1 + |s.im|) ^ (∑ j, N j) *
        Real.exp (-(Real.pi / 2 * (∑ j, S.lam j) * |s.im|)) := by
        rw [Finset.prod_pow_eq_pow_sum, ← Real.exp_sum]
        congr 2
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]

/-! ### Boundedness on `2 ≤ Re s ≤ σ₁` -/

/-- `xi_F` is bounded on `2 ≤ Re s ≤ σ₁`. -/
lemma exists_bound_xi_right {σ₁ : ℝ} (h : 2 ≤ σ₁) :
    ∃ C : ℝ, ∀ s : ℂ, 2 ≤ s.re → s.re ≤ σ₁ → ‖S.xi s‖ ≤ C := by
  obtain ⟨A, hA0, N, hAN⟩ := S.exists_bound_Gamma_prod h
  set c : ℝ := Real.pi / 2 * ∑ j, S.lam j with hc
  have hc0 : 0 < c := by have := S.deg_pos; positivity
  set CL : ℝ := ∑' n, ‖LSeries.term S.a 2 n‖ with hCL
  have hCL0 : 0 ≤ CL := tsum_nonneg fun n => norm_nonneg _
  set CQ : ℝ := Real.exp (σ₁ * |Real.log S.Q|) with hCQ
  set CP : ℝ := (σ₁ * (σ₁ + 1)) ^ S.m with hCP
  have hCP0 : 0 ≤ CP := by rw [hCP]; positivity
  set K : ℕ := 2 * S.m + N with hK
  refine ⟨CP * CQ * A * CL * ((K.factorial : ℝ) * Real.exp c / c ^ K), fun s hs2 hs1 => ?_⟩
  have h0 : 0 ≤ s.re := by linarith
  have hτ0 : 0 ≤ |s.im| := abs_nonneg _
  rw [S.xi_eq_tsum (by linarith)]
  have hP := S.norm_pole_pow_le (by linarith) h0 hs1
  have hQ := S.norm_Q_cpow_le h0 hs1
  have hGam := hAN s hs2 hs1
  have hL := S.norm_LSeries_le_of_two_le hs2
  have hdecay := pow_mul_exp_neg_le hc0 K hτ0
  calc ‖(s * (s - 1)) ^ S.m * ((S.Q : ℝ) : ℂ) ^ s * (∏ j, Complex.Gamma (S.lam j * s + S.mu j)) *
        LSeries S.a s‖
      = ‖(s * (s - 1)) ^ S.m‖ * ‖((S.Q : ℝ) : ℂ) ^ s‖ *
          ‖∏ j, Complex.Gamma (S.lam j * s + S.mu j)‖ * ‖LSeries S.a s‖ := by
        rw [norm_mul, norm_mul, norm_mul]
    _ ≤ (CP * (1 + |s.im|) ^ (2 * S.m)) * CQ *
          (A * (1 + |s.im|) ^ N * Real.exp (-(c * |s.im|))) * CL := by
        gcongr
    _ = CP * CQ * A * CL * ((1 + |s.im|) ^ K * Real.exp (-(c * |s.im|))) := by
        rw [hK, pow_add]; ring
    _ ≤ CP * CQ * A * CL * ((K.factorial : ℝ) * Real.exp c / c ^ K) := by
        gcongr

/-! ### Boundedness on `σ₀ ≤ Re s ≤ -1`, by the functional equation -/

/-- `xi_F` is bounded on `σ₀ ≤ Re s ≤ -1`: reflect to `2 ≤ Re(1 - conj s) ≤ 1 - σ₀`. -/
lemma exists_bound_xi_left {σ₀ : ℝ} (h : σ₀ ≤ -1) :
    ∃ C : ℝ, ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ -1 → ‖S.xi s‖ ≤ C := by
  obtain ⟨C, hC⟩ := S.exists_bound_xi_right (σ₁ := 1 - σ₀) (by linarith)
  refine ⟨C, fun s hs0 hs1 => ?_⟩
  rw [S.norm_xi_reflect]
  exact hC _ (by rw [re_one_sub_conj]; linarith) (by rw [re_one_sub_conj]; linarith)

/-! ### Phragmén–Lindelöf on `-1 ≤ Re s ≤ 2` -/

/-- The growth hypothesis for Phragmén–Lindelöf: on `-1 < Re z < 2` with `|Im z|` large,
`‖xi z‖ ≤ exp(B exp(|Im z|))`, from finite order (`‖z‖ ≤ 2 + |Im z|`,
`(2+y)^N ≤ N! e^2 e^y`). -/
lemma exists_growth_bound : ∃ B T : ℝ, ∀ z : ℂ, T ≤ |z.im| → -1 < z.re → z.re < 2 →
    ‖S.xi z‖ ≤ Real.exp (B * Real.exp (|z.im|)) := by
  obtain ⟨-, ρ₀, R₀, hR⟩ := S.hasFiniteOrder_xi
  set ρ : ℝ := max ρ₀ 0 with hρ
  have hρ0 : 0 ≤ ρ := le_max_right _ _
  set N : ℕ := ⌈ρ⌉₊ with hN
  refine ⟨(N.factorial : ℝ) * Real.exp 2, max R₀ 1, fun z hz h1 h2 => ?_⟩
  have hy0 : 0 ≤ |z.im| := abs_nonneg _
  have hzR : R₀ ≤ ‖z‖ := le_trans (le_trans (le_max_left _ _) hz) (Complex.abs_im_le_norm z)
  have hz1 : 1 ≤ ‖z‖ := le_trans (le_trans (le_max_right _ _) hz) (Complex.abs_im_le_norm z)
  have hz2 : ‖z‖ ≤ 2 + |z.im| := by
    have := Complex.norm_le_abs_re_add_abs_im z
    have : |z.re| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have key : ‖z‖ ^ ρ₀ ≤ (N.factorial : ℝ) * Real.exp 2 * Real.exp (|z.im|) := by
    calc ‖z‖ ^ ρ₀ ≤ ‖z‖ ^ ρ := Real.rpow_le_rpow_of_exponent_le hz1 (le_max_left _ _)
      _ ≤ ‖z‖ ^ (N : ℝ) := Real.rpow_le_rpow_of_exponent_le hz1 (Nat.le_ceil ρ)
      _ = ‖z‖ ^ N := Real.rpow_natCast _ _
      _ ≤ (2 + |z.im|) ^ N := pow_le_pow_left₀ (norm_nonneg _) hz2 N
      _ ≤ (N.factorial : ℝ) * Real.exp (2 + |z.im|) := by
          have h := Real.pow_div_factorial_le_exp (x := 2 + |z.im|) (by positivity) N
          have hfac : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
          rw [div_le_iff₀ hfac] at h
          linarith
      _ = (N.factorial : ℝ) * Real.exp 2 * Real.exp (|z.im|) := by rw [Real.exp_add]; ring
  exact (hR z hzR).le.trans (Real.exp_le_exp.mpr key)

/-- `xi_F` is bounded on the closed strip `-1 ≤ Re s ≤ 2` (Phragmén–Lindelöf). -/
lemma exists_bound_xi_strip : ∃ C : ℝ, ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → ‖S.xi s‖ ≤ C := by
  obtain ⟨C₁, hC₁⟩ := S.exists_bound_xi_right (σ₁ := 2) le_rfl
  obtain ⟨C₂, hC₂⟩ := S.exists_bound_xi_left (σ₀ := -1) le_rfl
  obtain ⟨B, T, hBT⟩ := S.exists_growth_bound
  refine ⟨max C₁ C₂, fun s hs0 hs1 => ?_⟩
  refine PhragmenLindelof.vertical_strip (a := -1) (b := 2) (S.differentiable_xi.diffContOnCl)
    ?_ (fun z hz => ?_) (fun z hz => ?_) hs0 hs1
  · -- the growth hypothesis
    refine ⟨1, ?_, B, ?_⟩
    · have := Real.pi_gt_three
      rw [lt_div_iff₀ (by norm_num)]
      linarith
    · refine Asymptotics.IsBigO.of_bound 1 ?_
      rw [Filter.eventually_inf_principal, Filter.eventually_comap]
      refine (Filter.eventually_ge_atTop T).mono fun y hy z hz hzs => ?_
      have hzs' : -1 < z.re ∧ z.re < 2 := hzs
      have hyz : T ≤ |z.im| := by
        have : (_root_.abs ∘ Complex.im) z = |z.im| := rfl
        rw [← this, hz]; exact hy
      have hb := hBT z hyz hzs'.1 hzs'.2
      rw [one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]
      exact hb
  · exact (hC₂ z (by rw [hz]) (by rw [hz])).trans (le_max_right _ _)
  · exact (hC₁ z (by rw [hz]) (by rw [hz])).trans (le_max_left _ _)

/-! ### Every vertical strip -/

/-- **`xi_F` is bounded on every vertical strip.** -/
theorem exists_bound_xi_vertical (σ₀ σ₁ : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → ‖S.xi s‖ ≤ C := by
  obtain ⟨C₁, hC₁⟩ := S.exists_bound_xi_right (σ₁ := max σ₁ 2) (le_max_right _ _)
  obtain ⟨C₂, hC₂⟩ := S.exists_bound_xi_left (σ₀ := min σ₀ (-1)) (min_le_right _ _)
  obtain ⟨C₃, hC₃⟩ := S.exists_bound_xi_strip
  refine ⟨max (max C₁ C₂) C₃, fun s hs0 hs1 => ?_⟩
  rcases le_or_gt 2 s.re with h2 | h2
  · exact (hC₁ s h2 (hs1.trans (le_max_left _ _))).trans
      ((le_max_left _ _).trans (le_max_left _ _))
  rcases le_or_gt s.re (-1) with h1 | h1
  · exact (hC₂ s ((min_le_left _ _).trans hs0) h1).trans
      ((le_max_right _ _).trans (le_max_left _ _))
  · exact (hC₃ s h1.le h2.le).trans (le_max_right _ _)

/-! ### The conversion to `ExtSelbergData` -/

lemma re_half_add_I_mul_div_two (z : ℂ) : ((1 : ℂ) / 2 + I * z / 2).re = 1 / 2 - z.im / 2 := by
  simp
  ring

lemma half_add_I_mul_neg_I (s : ℂ) : (1 : ℂ) / 2 + I * (-I * (2 * s - 1)) / 2 = s := by
  linear_combination (-(2 * s - 1) / 2) * Complex.I_sq

/-- Every element of `S^#` yields the data Dobner's proof consumes, with
`Ξ z := xi_F(1/2 + iz/2)` (the island's `z = -i(2s-1)` variable). -/
noncomputable def toExtSelbergData : ExtSelbergData where
  a := S.a
  a_one := S.a_one
  nonconst := S.nonconst
  summable := S.summable
  r := S.r
  Q := S.Q
  Q_pos := S.Q_pos
  lam := S.lam
  lam_pos := S.lam_pos
  deg_pos := S.deg_pos
  mu := S.mu
  mu_re_nonneg := S.mu_re_nonneg
  P := S.P
  P_ne_zero := S.P_ne_zero
  Ξ := fun z => S.xi (1 / 2 + I * z / 2)
  Ξ_differentiable :=
    S.differentiable_xi.comp (f := fun z : ℂ => (1 : ℂ) / 2 + I * z / 2) (by fun_prop)
  Ξ_eq_tsum := fun s hs => by
    show S.xi (1 / 2 + I * (-I * (2 * s - 1)) / 2) = _
    rw [half_add_I_mul_neg_I]
    exact S.xi_eq_tsum' hs
  Ξ_strip_bounded := fun B => by
    obtain ⟨C, hC⟩ := S.exists_bound_xi_vertical (1 / 2 - B / 2) (1 / 2 + B / 2)
    refine ⟨C, fun w hw => ?_⟩
    have h := abs_le.mp hw
    exact hC _ (by rw [re_half_add_I_mul_div_two]; linarith [h.2])
      (by rw [re_half_add_I_mul_div_two]; linarith [h.1])

@[simp] lemma toExtSelbergData_Ξ (z : ℂ) :
    S.toExtSelbergData.Ξ z = S.xi (1 / 2 + I * z / 2) := rfl

lemma toExtSelbergData_flow (t : ℝ) (z : ℂ) :
    S.toExtSelbergData.flow t z = (1 / ((Real.sqrt (4 * π * (-t)) : ℝ) : ℂ)) *
      ∫ ω : ℝ, DBNGaussConv.gaussKer (-t) ω * S.xi (1 / 2 + I * (z + ω) / 2) := rfl

end SelbergSharp

end DBNSelberg

/-- **Newman's conjecture for the extended Selberg class `S^#`** (Dobner's theorem): for every
element `S` of the class, as `DBNSelberg.SelbergSharp` states it, and every `t < 0`, the backward
heat flow of its completed function has a non-real zero. -/
theorem selberg_newman_sharp_ext (S : DBNSelberg.SelbergSharp) :
    ∀ t : ℝ, t < 0 → ∃ z : ℂ, S.toExtSelbergData.flow t z = 0 ∧ z.im ≠ 0 :=
  selberg_newman S.toExtSelbergData

/-- **Newman's conjecture for the extended Selberg class** (Dobner), in the registry's shape: for every
`S : SelbergSharp` and every `t < 0`, the heat flow of `ξ_S` has a non-real zero. `sharpFlow` is
`toExtSelbergData.flow` definitionally. The registered statement of node `RH_dbn_selberg_newman_sharp`. -/
theorem selberg_newman_sharp (S : DBNSelberg.SelbergSharp) :
    ∀ t : ℝ, t < 0 → ∃ z : ℂ, S.sharpFlow t z = 0 ∧ z.im ≠ 0 :=
  selberg_newman_sharp_ext S
