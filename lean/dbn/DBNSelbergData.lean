/-
# The extended Selberg class, in the form Dobner's argument consumes

Dobner (arXiv:2005.05142) proves Newman's conjecture for the extended Selberg class `S^#`.
On the dbn island the ζ case is `dbn_newman` (DBNNewman). This module introduces the data an
element `F` of the class contributes to that proof, and nothing more:

* Dirichlet coefficients `a : ℕ → ℂ` with `a 1 = 1`, at least one further nonzero coefficient, and
  absolute convergence on `Re s > 1`;
* a Gamma factor `γ_F(v) = P(v) Q^v ∏_j Γ(λ_j v + μ_j)` with `Q > 0`, `λ_j > 0`, `Re μ_j ≥ 0`,
  `∑ λ_j > 0` (degree `d_F = 2 ∑ λ_j > 0`), and a nonzero polynomial `P` (for ζ, `P(v) = v(v-1)/16`);
* the completed function `Ξ`, entire, equal to `∑_n a(n) γ_F(s) n^{-s}` on `Re s > 1` in the
  island's `z = -i(2s-1)` variable, and bounded on every horizontal strip.

For an honest element of `S^#` the last three hypotheses are theorems (the analytic continuation
axiom after removing the pole with `P`, and Phragmén–Lindelöf plus Stirling for the strip bound);
here they are hypotheses of the structure. `ExtSelbergData.flow t` is the backward heat flow for
`t < 0`, defined as the Gaussian convolution that `DBNGaussConv.H_neg_eq_gauss` proves the island's
`H_t` to be; so `zetaData.flow t = DBN.H t` for `t < 0` (DBNSelbergZeta).

All the saddle-point vocabulary (`ellF`, `JF`, `γtF`, `ρF`, `QF`, `KF`, `EF`, `BF`, `Ft`) is defined
here so that the analytic modules can be written independently of one another:
`DBNSelbergGauss` (Dobner's (9)), `DBNSelbergSaddleAlg` (exact bookkeeping), `DBNSelbergSaddleBounds`
(pointwise bounds), `DBNSelbergFtZero` (the Gaussian Dirichlet series has zeros at every height),
`DBNSelbergSaddleSum` (summation), `DBNSelbergNewman` (Theorem 4 and the transfer).

Nothing here is about the zeros of ζ or of any `F`; `conjecture1_proved = False`.
-/
import Mathlib
import DBNStirling
import DBNGaussConv
import DBNSaddleAlg

open Complex Filter Topology MeasureTheory Set
open scoped Real

namespace DBNSelberg

open DBNGaussConv DBNStirling

/-- The data of an element of the extended Selberg class that Dobner's proof uses. -/
structure ExtSelbergData where
  /-- Dirichlet coefficients; `a 0` is ignored by `LSeries`. -/
  a : ℕ → ℂ
  a_one : a 1 = 1
  nonconst : ∃ n : ℕ, 2 ≤ n ∧ a n ≠ 0
  summable : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s
  /-- Number of Gamma factors. -/
  r : ℕ
  /-- The conductor-type constant `Q > 0`. -/
  Q : ℝ
  Q_pos : 0 < Q
  lam : Fin r → ℝ
  lam_pos : ∀ j, 0 < lam j
  deg_pos : 0 < ∑ j, lam j
  mu : Fin r → ℂ
  mu_re_nonneg : ∀ j, 0 ≤ (mu j).re
  /-- The polynomial removing the poles of `F`. -/
  P : Polynomial ℂ
  P_ne_zero : P ≠ 0
  /-- The completed function, in the island's `z`-variable (`z = -i(2s-1)`, `s = 1/2 + iz/2`). -/
  Ξ : ℂ → ℂ
  Ξ_differentiable : Differentiable ℂ Ξ
  Ξ_eq_tsum : ∀ s : ℂ, 1 < s.re →
    Ξ (-I * (2 * s - 1)) = ∑' n : ℕ+, a n *
      (P.eval s * ((Q : ℝ) : ℂ) ^ s * ∏ j, Complex.Gamma (lam j * s + mu j)) * (1 / (n : ℂ) ^ s)
  Ξ_strip_bounded : ∀ B : ℝ, ∃ C : ℝ, ∀ w : ℂ, |w.im| ≤ B → ‖Ξ w‖ ≤ C

namespace ExtSelbergData

variable (F : ExtSelbergData)

/-! ### The Gamma factor -/

/-- `γ_F(v) = P(v) Q^v ∏_j Γ(λ_j v + μ_j)`. -/
noncomputable def gammaF (v : ℂ) : ℂ :=
  F.P.eval v * ((F.Q : ℝ) : ℂ) ^ v * ∏ j, Complex.Gamma (F.lam j * v + F.mu j)

theorem Ξ_eq_tsum_gammaF {s : ℂ} (hs : 1 < s.re) :
    F.Ξ (-I * (2 * s - 1)) = ∑' n : ℕ+, F.a n * F.gammaF s * (1 / (n : ℂ) ^ s) :=
  F.Ξ_eq_tsum s hs

/-- `Re (λ_j v + μ_j) > 0` whenever `Re v > 0`: no Gamma factor meets a pole on the right
half-plane. -/
lemma re_lam_mul_add_mu_pos {v : ℂ} (hv : 0 < v.re) (j : Fin F.r) :
    0 < (F.lam j * v + F.mu j).re := by
  have h1 : (F.lam j * v + F.mu j).re = F.lam j * v.re + (F.mu j).re := by simp
  rw [h1]
  have := F.lam_pos j
  have := F.mu_re_nonneg j
  positivity

lemma lam_mul_add_mu_ne_neg_nat {v : ℂ} (hv : 0 < v.re) (j : Fin F.r) (m : ℕ) :
    F.lam j * v + F.mu j ≠ -(m : ℂ) := by
  intro h
  have := F.re_lam_mul_add_mu_pos hv j
  rw [h] at this
  simp at this
  linarith [this, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

lemma differentiableAt_gammaF {v : ℂ} (hv : 0 < v.re) : DifferentiableAt ℂ F.gammaF v := by
  unfold gammaF
  have hQ : (0 : ℝ) < F.Q := F.Q_pos
  have h1 : DifferentiableAt ℂ (fun v : ℂ => F.P.eval v) v := F.P.differentiableAt
  have h2 : DifferentiableAt ℂ (fun v : ℂ => ((F.Q : ℝ) : ℂ) ^ v) v := by
    apply DifferentiableAt.const_cpow differentiableAt_id
    left
    exact_mod_cast hQ.ne'
  have h3 : DifferentiableAt ℂ (fun v : ℂ => ∏ j, Complex.Gamma (F.lam j * v + F.mu j)) v := by
    have h3' : DifferentiableAt ℂ (∏ j, fun v : ℂ => Complex.Gamma (F.lam j * v + F.mu j)) v := by
      refine DifferentiableAt.finsetProd fun j _ => ?_
      have hd : DifferentiableAt ℂ (fun v : ℂ => F.lam j * v + F.mu j) v := by fun_prop
      exact (Complex.differentiableAt_Gamma _ (F.lam_mul_add_mu_ne_neg_nat hv j)).comp v hd
    have heq : (∏ j, fun v : ℂ => Complex.Gamma (F.lam j * v + F.mu j)) =
        fun v => ∏ j, Complex.Gamma (F.lam j * v + F.mu j) := by
      funext v; simp [Finset.prod_apply]
    rwa [heq] at h3'
  exact (h1.mul h2).mul h3

lemma gammaF_ne_zero {v : ℂ} (hv : 0 < v.re) (hP : F.P.eval v ≠ 0) : F.gammaF v ≠ 0 := by
  unfold gammaF
  refine mul_ne_zero (mul_ne_zero hP ?_) ?_
  · intro h
    rw [Complex.cpow_eq_zero_iff] at h
    exact (show ((F.Q : ℝ) : ℂ) ≠ 0 by exact_mod_cast F.Q_pos.ne') h.1
  · rw [Finset.prod_ne_zero_iff]
    intro j _
    exact Complex.Gamma_ne_zero (F.lam_mul_add_mu_ne_neg_nat hv j)

/-- `‖γ_F(a + iτ)‖` on a vertical line: a polynomial in `|τ|` times a constant depending on `a`. -/
lemma norm_gammaF_le {a : ℝ} (ha : 0 < a) (τ : ℝ) :
    ‖F.gammaF ((a : ℂ) + τ * I)‖ ≤
      (∑ k ∈ Finset.range (F.P.natDegree + 1), ‖F.P.coeff k‖ * (a + |τ|) ^ k) *
        F.Q ^ a * ∏ j, Real.Gamma (F.lam j * a + (F.mu j).re) := by
  have hv : ‖(a : ℂ) + τ * I‖ ≤ a + |τ| := by
    calc ‖(a : ℂ) + τ * I‖ ≤ ‖(a : ℂ)‖ + ‖(τ : ℂ) * I‖ := norm_add_le _ _
      _ = a + |τ| := by simp [abs_of_pos ha]
  have hP : ‖F.P.eval ((a : ℂ) + τ * I)‖ ≤
      ∑ k ∈ Finset.range (F.P.natDegree + 1), ‖F.P.coeff k‖ * (a + |τ|) ^ k := by
    rw [Polynomial.eval_eq_sum_range]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_pow]
    gcongr
  have hQ : ‖((F.Q : ℝ) : ℂ) ^ ((a : ℂ) + τ * I)‖ = F.Q ^ a := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos F.Q_pos]
    congr 1
    simp
  have hΓ : ‖∏ j, Complex.Gamma (F.lam j * ((a : ℂ) + τ * I) + F.mu j)‖ ≤
      ∏ j, Real.Gamma (F.lam j * a + (F.mu j).re) := by
    rw [norm_prod]
    refine Finset.prod_le_prod (fun j _ => norm_nonneg _) fun j _ => ?_
    have hre : (F.lam j * ((a : ℂ) + τ * I) + F.mu j).re = F.lam j * a + (F.mu j).re := by simp
    have hpos : 0 < (F.lam j * ((a : ℂ) + τ * I) + F.mu j).re := by
      rw [hre]; have := F.lam_pos j; have := F.mu_re_nonneg j; positivity
    have := norm_Gamma_le_Gamma_re hpos
    rwa [hre] at this
  unfold gammaF
  rw [norm_mul, norm_mul, hQ]
  have h0 : 0 ≤ ∑ k ∈ Finset.range (F.P.natDegree + 1), ‖F.P.coeff k‖ * (a + |τ|) ^ k :=
    Finset.sum_nonneg fun k _ => by positivity
  have hQ0 : 0 ≤ F.Q ^ a := Real.rpow_nonneg F.Q_pos.le a
  gcongr

/-! ### The backward heat flow, for `t < 0`, as a Gaussian convolution -/

/-- `flow t z = (4π|t|)^{-1/2} ∫ e^{-ω²/(4|t|)} Ξ(z + ω) dω` for `t < 0` (junk for `t ≥ 0`).
This is the island's `H_t` when `Ξ = H_0` (`DBNGaussConv.H_neg_eq_gauss`). -/
noncomputable def flow (t : ℝ) (z : ℂ) : ℂ :=
  (1 / ((Real.sqrt (4 * π * (-t)) : ℝ) : ℂ)) * ∫ ω : ℝ, gaussKer (-t) ω * F.Ξ (z + ω)

/-! ### The Gaussian Dirichlet series `F_t` -/

/-- `F_t(s) = ∑ a(n) e^{-c' log² n} n^{-s}` with `c' = |t|/4`. -/
noncomputable def Ft (c : ℝ) (s : ℂ) : ℂ := LSeries (fun n => F.a n * DBNFtZero.gaussCoeff c n) s

/-! ### Dobner's `B_n` for `F` -/

/-- The integrand of `B_n`: `a(n) γ_F(a+iτ) n^{-(a+iτ)} e^{(a+iτ-s)²/c}`. -/
noncomputable def BInt (c a : ℝ) (n : ℕ+) (s : ℂ) (τ : ℝ) : ℂ :=
  F.a n * F.gammaF ((a : ℂ) + τ * I) * (1 / (n : ℂ) ^ ((a : ℂ) + τ * I)) *
    cexp ((((a : ℂ) + τ * I) - s) ^ 2 / c)

/-- `B_n(s) = (πc)^{-1/2} ∫ BInt`. -/
noncomputable def Bn (c a : ℝ) (n : ℕ+) (s : ℂ) : ℂ :=
  (1 / ((Real.sqrt (π * c) : ℝ) : ℂ)) * ∫ τ : ℝ, F.BInt c a n s τ

/-! ### Saddle-point vocabulary -/

/-- `ℓ_F(b) = log Q + ∑_j λ_j Log(λ_j b + μ_j)`, the local slope of `log γ_F`
(for ζ: `½ Log(b/2) − ½ log π = DBNSaddle.ell b`). -/
noncomputable def ellF (b : ℂ) : ℂ :=
  (Real.log F.Q : ℂ) + ∑ j, (F.lam j : ℂ) * log (F.lam j * b + F.mu j)

/-- Dobner's shift `J(s) = s + (c/2) ℓ_F(s + M₀)`. -/
noncomputable def JF (c M₀ : ℝ) (s : ℂ) : ℂ := s + (c / 2 : ℂ) * F.ellF (s + M₀)

/-- `γ_t(s) = γ_F(b) exp(−M₀ ℓ_F(b) + (c/4) ℓ_F(b)²)`, `b = s + M₀`. -/
noncomputable def γtF (c M₀ : ℝ) (s : ℂ) : ℂ :=
  F.gammaF (s + M₀) * cexp (-(M₀ : ℂ) * F.ellF (s + M₀) + (c / 4 : ℂ) * F.ellF (s + M₀) ^ 2)

/-- The polynomial ratio `ρ_F(δ) = P(b+δ)/P(b)`. -/
noncomputable def ρF (b δ : ℂ) : ℂ := F.P.eval (b + δ) / F.P.eval b

/-- `Q_F(δ) = ∑_j [L(λ_j(b+δ)+μ_j) − L(λ_j b+μ_j) − λ_j δ Log(λ_j b+μ_j)]`, with `L` Stirling's
`log Γ` (`DBNStirling.L`). -/
noncomputable def QF (b δ : ℂ) : ℂ :=
  ∑ j, (L (F.lam j * (b + δ) + F.mu j) - L (F.lam j * b + F.mu j) -
    (F.lam j : ℂ) * δ * log (F.lam j * b + F.mu j))

/-- `K_n(σ) = ρ_F(δ) exp(Q_F(δ))`, `δ = δ_n(σ) = h_n + iσ` (`DBNSaddle.δ`). -/
noncomputable def KF (c M₀ : ℝ) (n : ℕ+) (s : ℂ) (σ : ℝ) : ℂ :=
  F.ρF (s + M₀) (DBNSaddle.δ c n σ) * cexp (F.QF (s + M₀) (DBNSaddle.δ c n σ))

/-- The relative error `E_n(s) = e^{M₀²/c} (πc)^{-1/2} ∫ (K_n(σ) − 1) gw(σ) dσ`
(`gw` is `DBNSaddle.gw`). -/
noncomputable def EF (c M₀ : ℝ) (n : ℕ+) (s : ℂ) : ℂ :=
  cexp ((M₀ ^ 2 / c : ℝ)) * (1 / ((Real.sqrt (π * c) : ℝ) : ℂ)) *
    ∫ σ : ℝ, (F.KF c M₀ n s σ - 1) * DBNSaddle.gw c M₀ σ

/-! ### `γ_F` through Stirling -/

/-- `γ_F(v) = P(v) exp(G_F(v))` with `G_F(v) = v log Q + ∑_j L(λ_j v + μ_j)` on `Re v > 0`. -/
theorem gammaF_eq_exp {v : ℂ} (hv : 0 < v.re) :
    F.gammaF v = F.P.eval v *
      cexp (v * (Real.log F.Q : ℂ) + ∑ j, L (F.lam j * v + F.mu j)) := by
  unfold gammaF
  rw [Complex.exp_add, Complex.exp_sum Finset.univ (fun j => L (F.lam j * v + F.mu j))]
  have hQ : ((F.Q : ℝ) : ℂ) ^ v = cexp (v * (Real.log F.Q : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast F.Q_pos.ne'), Complex.ofReal_log F.Q_pos.le,
      mul_comm]
  rw [hQ, mul_assoc]
  congr 2
  exact Finset.prod_congr rfl fun j _ => Gamma_eq_exp_L (F.re_lam_mul_add_mu_pos hv j)

/-- The exact decomposition `γ_F(b+δ) = γ_F(b) ρ_F(δ) exp(Q_F(δ) + δ ℓ_F(b))`. -/
theorem gammaF_add_eq {b δ : ℂ} (hb : 0 < b.re) (hbδ : 0 < (b + δ).re) (hP : F.P.eval b ≠ 0) :
    F.gammaF (b + δ) = F.gammaF b * F.ρF b δ * cexp (F.QF b δ + δ * F.ellF b) := by
  rw [gammaF_eq_exp F hbδ, gammaF_eq_exp F hb, ρF]
  have key : (b + δ) * (Real.log F.Q : ℂ) + ∑ j, L (F.lam j * (b + δ) + F.mu j) =
      (b * (Real.log F.Q : ℂ) + ∑ j, L (F.lam j * b + F.mu j)) + (F.QF b δ + δ * F.ellF b) := by
    unfold QF ellF
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, mul_add, Finset.mul_sum]
    have : ∑ j, δ * ((F.lam j : ℂ) * log (F.lam j * b + F.mu j)) =
        ∑ j, (F.lam j : ℂ) * δ * log (F.lam j * b + F.mu j) :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    ring
  rw [key, Complex.exp_add]
  field_simp

end ExtSelbergData

end DBNSelberg
