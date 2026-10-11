/-
# The zeta instance of `ExtSelbergData` (the control)

`zetaData` packages the Riemann zeta function as an element of the extended Selberg class in the
form `DBNSelbergData.ExtSelbergData` consumes: coefficients `a(n) = 1`, one Gamma factor with
`Q = π^{-1/2}`, `λ = 1/2`, `μ = 0`, pole-removing polynomial `P(v) = v(v-1)/16`, and completed
function `Ξ = DBN.H 0`. The three analytic hypotheses of the structure are island theorems:
`DBN.differentiable_H`, `DBNGaussConv.H_zero_eq_tsum` (via `γ s = P(s) Q^s Γ(s/2)`), and
`DBNGaussConv.norm_H_zero_le`.

`zetaData_flow_eq` identifies the structure's Gaussian-convolution flow with the island's `H_t`
for `t < 0` (`DBNGaussConv.H_neg_eq_gauss`), so Newman for `zetaData` is `dbn_newman`
(`dbn_newman_of_zetaData_newman`). The general theorem `selberg_newman` lives in
DBNSelbergNewman; this module only supplies the instance.

Nothing here is about the zeros of ζ; `conjecture1_proved = False`.
-/
import Mathlib
import DBNDefs
import DBNGaussConv
import DBNSelbergData

open Complex Filter Topology MeasureTheory Set
open scoped Real

namespace DBNSelberg

open DBNGaussConv

/-! ### The conductor `Q = π^{-1/2}` -/

/-- `(π^{-1/2})^s = π^{-s/2}` in `ℂ`, for the positive real base `π`. -/
lemma ofReal_pi_rpow_neg_half_cpow (s : ℂ) :
    (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) ^ s = (π : ℂ) ^ (-s / 2) := by
  rw [← Complex.cpow_mul_ofReal_nonneg Real.pi_pos.le]
  congr 1
  push_cast
  ring

/-- The pole-removing polynomial of ζ, `P(v) = v(v-1)/16`. -/
noncomputable def zetaP : Polynomial ℂ :=
  Polynomial.C (1 / 16 : ℂ) * (Polynomial.X * (Polynomial.X - 1))

@[simp] lemma zetaP_eval (v : ℂ) : zetaP.eval v = 1 / 16 * (v * (v - 1)) := by
  simp [zetaP]

lemma zetaP_ne_zero : zetaP ≠ 0 := by
  intro h
  have h2 := congrArg (Polynomial.eval (2 : ℂ)) h
  rw [zetaP_eval, Polynomial.eval_zero] at h2
  norm_num at h2

/-- `DBNGaussConv.γ s = P(s) Q^s Γ(s/2)` with the zeta data, in the shape of `Ξ_eq_tsum`. -/
lemma γ_eq_zeta_gammaF (s : ℂ) :
    γ s = zetaP.eval s * (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) ^ s *
      ∏ _j : Fin 1, Complex.Gamma (((1 / 2 : ℝ) : ℂ) * s + 0) := by
  rw [γ, ofReal_pi_rpow_neg_half_cpow, Fin.prod_univ_one, zetaP_eval]
  have hΓ : Complex.Gamma (((1 / 2 : ℝ) : ℂ) * s + 0) = Complex.Gamma (s / 2) := by
    congr 1
    push_cast
    ring
  rw [hΓ]
  ring

/-- The Dirichlet-series identity for `H_0` in the shape `Ξ_eq_tsum` demands. -/
theorem H_zero_eq_tsum_zetaData {s : ℂ} (hs : 1 < s.re) :
    DBN.H 0 (-I * (2 * s - 1)) = ∑' n : ℕ+, (1 : ℂ) *
      (zetaP.eval s * (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) ^ s *
        ∏ _j : Fin 1, Complex.Gamma (((1 / 2 : ℝ) : ℂ) * s + 0)) * (1 / (n : ℂ) ^ s) := by
  have hz : (-I * (2 * s - 1)).im < -1 := by
    simp
    linarith
  rw [H_zero_eq_tsum hz]
  have hs' : (1 / 2 : ℂ) + I * (-I * (2 * s - 1)) / 2 = s := by
    linear_combination (-(2 * s - 1) / 2) * Complex.I_mul_I
  rw [hs']
  refine tsum_congr fun n => ?_
  rw [γ_eq_zeta_gammaF, one_mul]

/-! ### The instance -/

/-- The Riemann zeta function as an element of the extended Selberg class. -/
noncomputable def zetaData : ExtSelbergData where
  a := fun _ => 1
  a_one := rfl
  nonconst := ⟨2, le_rfl, one_ne_zero⟩
  summable := fun _ hs => LSeriesSummable_one_iff.mpr hs
  r := 1
  Q := Real.pi ^ (-(1 / 2 : ℝ))
  Q_pos := Real.rpow_pos_of_pos Real.pi_pos _
  lam := fun _ => 1 / 2
  lam_pos := fun _ => by norm_num
  deg_pos := by norm_num [Fin.sum_univ_one]
  mu := fun _ => 0
  mu_re_nonneg := fun _ => by simp
  P := zetaP
  P_ne_zero := zetaP_ne_zero
  Ξ := DBN.H 0
  Ξ_differentiable := DBN.differentiable_H 0
  Ξ_eq_tsum := fun _ hs => H_zero_eq_tsum_zetaData hs
  Ξ_strip_bounded := fun B => ⟨stripBound B, fun _ hw => norm_H_zero_le hw⟩

@[simp] lemma zetaData_a (n : ℕ) : zetaData.a n = 1 := rfl

@[simp] lemma zetaData_Ξ : zetaData.Ξ = DBN.H 0 := rfl

@[simp] lemma zetaData_P : zetaData.P = zetaP := rfl

@[simp] lemma zetaData_Q : zetaData.Q = Real.pi ^ (-(1 / 2 : ℝ)) := rfl

/-! ### The flow is the island's `H_t` -/

/-- For `t < 0` the structure's Gaussian-convolution flow of `zetaData` is `DBN.H t`. -/
theorem zetaData_flow_eq {t : ℝ} (ht : t < 0) (z : ℂ) : zetaData.flow t z = DBN.H t z := by
  have hc : 0 < -t := by linarith
  have h := H_neg_eq_gauss hc z
  rw [neg_neg] at h
  rw [h, ExtSelbergData.flow, zetaData_Ξ]

/-- Newman's conjecture for `zetaData` (in the structure's flow) is `dbn_newman`'s statement. -/
theorem dbn_newman_of_zetaData_newman
    (h : ∀ t : ℝ, t < 0 → ∃ z : ℂ, zetaData.flow t z = 0 ∧ z.im ≠ 0) :
    ∀ t : ℝ, t < 0 → ∃ z : ℂ, DBN.H t z = 0 ∧ z.im ≠ 0 := fun t ht =>
  let ⟨z, hz, him⟩ := h t ht
  ⟨z, (zetaData_flow_eq ht z).symm ▸ hz, him⟩

end DBNSelberg
