/-
# The completed function of an element of `S^#` is entire, of finite order

`DBNSelbergSharp.SelbergSharp` states the extended Selberg class: the functional equation is given
only on the open critical strip `0 < Re s < 1`, and finite order only on the right half-plane
`Re s ≥ 1/2`. This module glues the two expressions `xiRight` (holomorphic on `Re s > 0`, thanks to
the entire extension `G` of `(s-1)^m F` and the Gamma factors having no pole there) and `xiLeft = ω conj(xiRight(1 - conj s))`
(holomorphic on `Re s < 1`, Mathlib's `DifferentiableAt.conj_conj`) into the entire function `xi`:

* `xi_eq_xiRight`, `xi_eq_xiLeft`: the two expressions agree on the strip (the functional equation),
  so `xi` is the right expression on `Re s > 0` and the left one on `Re s < 1`;
* `differentiable_xi`: `xi` is entire;
* `xi_functional_equation`: `xi s = ω conj(xi(1 - conj s))` for EVERY `s` (`|ω| = 1`);
* `xi_eq_tsum`, `xi_eq_tsum'`: on `Re s > 1`, `xi` is the Gamma-weighted Dirichlet series, in the
  shape `DBNSelbergData.ExtSelbergData.Ξ_eq_tsum` consumes;
* `hasFiniteOrder_xi`: `xi` has finite order in the sense of `Hadamard.hasFiniteOrder` (the left
  half-plane by reflection, `‖1 - conj s‖ ≤ 2‖s‖`).

Nothing here is about zeros; `conjecture1_proved = False`.
-/
import Mathlib
import DBNSelbergSharp
import DBNSelbergData
import Hadamard.Basic

open Complex Filter Topology Set
open scoped Real ComplexConjugate

namespace DBNSelberg

namespace SelbergSharp

variable (S : SelbergSharp)

/-! ### Holomorphy of the right expression on `Re s > 0` -/

/-- `Re (λ_j v + μ_j) > 0` whenever `Re v > 0`. -/
lemma re_lam_mul_add_mu_pos {v : ℂ} (hv : 0 < v.re) (j : Fin S.r) :
    0 < (S.lam j * v + S.mu j).re := by
  have h1 : (S.lam j * v + S.mu j).re = S.lam j * v.re + (S.mu j).re := by simp
  rw [h1]
  have := S.lam_pos j
  have := S.mu_re_nonneg j
  positivity

lemma lam_mul_add_mu_ne_neg_nat {v : ℂ} (hv : 0 < v.re) (j : Fin S.r) (k : ℕ) :
    S.lam j * v + S.mu j ≠ -(k : ℂ) := by
  intro h
  have := S.re_lam_mul_add_mu_pos hv j
  rw [h] at this
  simp at this
  linarith [this, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

lemma differentiableAt_gammaProd {v : ℂ} (hv : 0 < v.re) :
    DifferentiableAt ℂ (fun v : ℂ => ∏ j, Complex.Gamma (S.lam j * v + S.mu j)) v := by
  have h3' : DifferentiableAt ℂ (∏ j, fun v : ℂ => Complex.Gamma (S.lam j * v + S.mu j)) v := by
    refine DifferentiableAt.finsetProd fun j _ => ?_
    have hd : DifferentiableAt ℂ (fun v : ℂ => S.lam j * v + S.mu j) v := by fun_prop
    exact (Complex.differentiableAt_Gamma _ (S.lam_mul_add_mu_ne_neg_nat hv j)).comp v hd
  have heq : (∏ j, fun v : ℂ => Complex.Gamma (S.lam j * v + S.mu j)) =
      fun v => ∏ j, Complex.Gamma (S.lam j * v + S.mu j) := by
    funext v; simp [Finset.prod_apply]
  rwa [heq] at h3'

lemma ne_one_of_re_ne {s : ℂ} (hs : s.re ≠ 1) : s ≠ 1 := by
  intro h
  rw [h] at hs
  exact hs Complex.one_re

lemma differentiableAt_xiRight {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ S.xiRight s := by
  unfold xiRight
  refine DifferentiableAt.mul (DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_)
    (S.differentiableAt_gammaProd hs)) (S.differentiable_G s)
  · fun_prop
  · apply DifferentiableAt.const_cpow differentiableAt_id
    left
    exact_mod_cast S.Q_pos.ne'

lemma differentiableOn_xiRight : DifferentiableOn ℂ S.xiRight {s | 0 < s.re} :=
  fun _ hs => (S.differentiableAt_xiRight hs).differentiableWithinAt

/-! ### Holomorphy of the reflected expression on `Re s < 1` -/

lemma re_one_sub_conj (s : ℂ) : (1 - conj s).re = 1 - s.re := by simp

lemma differentiableAt_xiLeft {s : ℂ} (hs : s.re < 1) : DifferentiableAt ℂ S.xiLeft s := by
  have heq : S.xiLeft = fun s => S.ω * (conj ∘ (fun w => S.xiRight (1 - w)) ∘ conj) s := by
    funext s
    simp [xiLeft, Function.comp]
  rw [heq]
  refine DifferentiableAt.const_mul ?_ _
  rw [differentiableAt_conj_conj_iff]
  have hre : 0 < (1 - conj s).re := by rw [re_one_sub_conj]; linarith
  have hlin : DifferentiableAt ℂ (fun w : ℂ => 1 - w) (conj s) := by fun_prop
  exact (S.differentiableAt_xiRight hre).comp (conj s) hlin

lemma differentiableOn_xiLeft : DifferentiableOn ℂ S.xiLeft {s | s.re < 1} :=
  fun _ hs => (S.differentiableAt_xiLeft hs).differentiableWithinAt

/-! ### The two expressions agree on the strip -/

lemma xiLeft_eq_xiRight {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) : S.xiLeft s = S.xiRight s := by
  have hs1 : s ≠ 1 := ne_one_of_re_ne h1.ne
  have hw1 : 1 - conj s ≠ 1 := ne_one_of_re_ne (by rw [re_one_sub_conj]; linarith)
  unfold xiLeft
  rw [S.xiRight_eq_Phi hs1, S.xiRight_eq_Phi hw1, map_mul, map_pow, S.functional_equation_Phi h0 h1]
  have hc : conj ((1 - conj s) * (1 - conj s - 1)) = s * (s - 1) := by
    simp only [map_mul, map_sub, map_one, Complex.conj_conj]
    ring
  rw [hc]
  ring

theorem xi_eq_xiRight {s : ℂ} (hs : 0 < s.re) : S.xi s = S.xiRight s := by
  unfold xi
  split_ifs with h
  · rfl
  · exact S.xiLeft_eq_xiRight hs (by linarith [not_le.mp h])

theorem xi_eq_xiLeft {s : ℂ} (hs : s.re < 1) : S.xi s = S.xiLeft s := by
  unfold xi
  split_ifs with h
  · exact (S.xiLeft_eq_xiRight (by linarith) hs).symm
  · rfl

/-! ### `xi` is entire -/

theorem differentiable_xi : Differentiable ℂ S.xi := by
  intro s
  rcases lt_or_ge 0 s.re with h | h
  · have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    refine (S.differentiableAt_xiRight h).congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds h] with z hz
    exact S.xi_eq_xiRight hz
  · have h1 : s.re < 1 := by linarith
    have hopen : IsOpen {z : ℂ | z.re < 1} := isOpen_lt Complex.continuous_re continuous_const
    refine (S.differentiableAt_xiLeft h1).congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds h1] with z hz
    exact S.xi_eq_xiLeft hz

/-! ### The functional equation everywhere -/

theorem xi_functional_equation (s : ℂ) :
    S.xi s = S.ω * (starRingEnd ℂ) (S.xi (1 - (starRingEnd ℂ) s)) := by
  rcases lt_or_ge s.re 1 with h | h
  · rw [S.xi_eq_xiLeft h, S.xi_eq_xiRight (by rw [re_one_sub_conj]; linarith)]
    rfl
  · have h' : (1 - conj s).re < 1 := by rw [re_one_sub_conj]; linarith
    rw [S.xi_eq_xiRight (by linarith), S.xi_eq_xiLeft h']
    unfold xiLeft
    simp only [map_mul, Complex.conj_conj, map_sub, map_one, sub_sub_cancel]
    rw [← mul_assoc, Complex.mul_conj', S.ω_norm]
    simp

/-! ### The Dirichlet series on `Re s > 1` -/

theorem xi_eq_tsum {s : ℂ} (hs : 1 < s.re) :
    S.xi s = (s * (s - 1)) ^ S.m * ((S.Q : ℝ) : ℂ) ^ s *
      (∏ j, Complex.Gamma (S.lam j * s + S.mu j)) * LSeries S.a s := by
  rw [S.xi_eq_xiRight (by linarith), S.xiRight_eq_Phi (ne_one_of_re_ne hs.ne'), Phi, S.F_eq s hs]
  ring

/-- `LSeries` as a sum over `ℕ+` (the `n = 0` term vanishes). -/
lemma lseries_eq_tsum_pnat {s : ℂ} (hs : 1 < s.re) :
    LSeries S.a s = ∑' n : ℕ+, S.a n * (1 / (n : ℂ) ^ s) := by
  rw [LSeries, (S.summable s hs).tsum_eq_zero_add, LSeries.term_zero, zero_add,
    ← tsum_pnat_eq_tsum_succ (f := fun n : ℕ => LSeries.term S.a s n)]
  congr 1
  funext n
  rw [LSeries.term_of_ne_zero n.ne_zero]
  ring

theorem xi_eq_tsum' {s : ℂ} (hs : 1 < s.re) :
    S.xi s = ∑' n : ℕ+, S.a n *
      (S.P.eval s * ((S.Q : ℝ) : ℂ) ^ s * ∏ j, Complex.Gamma (S.lam j * s + S.mu j)) *
        (1 / (n : ℂ) ^ s) := by
  rw [S.xi_eq_tsum hs, S.lseries_eq_tsum_pnat hs, P_eval, ← tsum_mul_left]
  congr 1
  funext n
  ring

/-! ### Finite order -/

/-- The finite-order axiom, read on `xiRight`. -/
lemma norm_xiRight_le : ∃ ρ₀ R₀ : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → R₀ ≤ ‖s‖ →
    ‖S.xiRight s‖ ≤ Real.exp (‖s‖ ^ ρ₀) := by
  obtain ⟨ρ₀, R₀, h⟩ := S.finite_order
  refine ⟨ρ₀, max R₀ 2, fun s h1 h2 => ?_⟩
  have hs1 : s ≠ 1 := by
    intro hs
    rw [hs, norm_one] at h2
    linarith [le_max_right R₀ 2]
  have e : S.xiRight s = (s * (s - 1)) ^ S.m * ((S.Q : ℝ) : ℂ) ^ s *
      (∏ j, Complex.Gamma (S.lam j * s + S.mu j)) * S.F s := by
    rw [S.xiRight_eq_Phi hs1, Phi]; ring
  rw [e]
  exact h s h1 (le_trans (le_max_left _ _) h2)

/-- `‖xi s‖ = ‖xi (1 - conj s)‖`. -/
lemma norm_xi_reflect (s : ℂ) : ‖S.xi s‖ = ‖S.xi (1 - conj s)‖ := by
  rw [S.xi_functional_equation s, norm_mul, S.ω_norm, one_mul, RCLike.norm_conj]

theorem hasFiniteOrder_xi : Hadamard.hasFiniteOrder S.xi := by
  refine ⟨S.differentiable_xi, ?_⟩
  obtain ⟨ρ₀, R₀, hR⟩ := S.norm_xiRight_le
  -- a nonnegative exponent dominating `ρ₀` on `‖s‖ ≥ 1`
  set ρ := max ρ₀ 0 with hρ
  have hρ0 : 0 ≤ ρ := le_max_right _ _
  have hρρ₀ : ρ₀ ≤ ρ := le_max_left _ _
  refine ⟨ρ + 1, max (max (R₀ + 1) 2) (2 ^ ρ + 1), fun s hs => ?_⟩
  have hs2 : 2 ≤ ‖s‖ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs
  have hsR : R₀ + 1 ≤ ‖s‖ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs
  have hs2ρ : 2 ^ ρ + 1 ≤ ‖s‖ := le_trans (le_max_right _ _) hs
  have hs1 : 1 < ‖s‖ := by linarith
  have hs0 : 0 < ‖s‖ := by linarith
  -- `exp(‖w‖^ρ₀) ≤ exp(‖w‖^ρ)` for `‖w‖ ≥ 1`
  have hmono : ∀ w : ℂ, 1 ≤ ‖w‖ → Real.exp (‖w‖ ^ ρ₀) ≤ Real.exp (‖w‖ ^ ρ) := fun w hw =>
    Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hw hρρ₀)
  have hpow : ‖s‖ ^ (ρ + 1) = ‖s‖ ^ ρ * ‖s‖ := Real.rpow_add_one hs0.ne' ρ
  have hsρ_pos : 0 < ‖s‖ ^ ρ := Real.rpow_pos_of_pos hs0 ρ
  rcases le_or_gt (1 / 2) s.re with h | h
  · -- right half-plane: the axiom
    rw [S.xi_eq_xiRight (by linarith)]
    calc ‖S.xiRight s‖ ≤ Real.exp (‖s‖ ^ ρ₀) := hR s h (by linarith)
      _ ≤ Real.exp (‖s‖ ^ ρ) := hmono s hs1.le
      _ < Real.exp (‖s‖ ^ (ρ + 1)) := by
          rw [Real.exp_lt_exp]
          exact Real.rpow_lt_rpow_of_exponent_lt hs1 (by linarith)
  · -- left half-plane: reflect
    rw [S.norm_xi_reflect]
    set w := 1 - conj s with hw
    have hwre : 1 / 2 ≤ w.re := by rw [hw, re_one_sub_conj]; linarith
    have hw_le : ‖w‖ ≤ 2 * ‖s‖ := by
      calc ‖w‖ = ‖(1 : ℂ) - conj s‖ := rfl
        _ ≤ ‖(1 : ℂ)‖ + ‖conj s‖ := norm_sub_le _ _
        _ = 1 + ‖s‖ := by rw [norm_one, RCLike.norm_conj]
        _ ≤ 2 * ‖s‖ := by linarith
    have hw_ge : ‖s‖ - 1 ≤ ‖w‖ := by
      have : ‖s‖ ≤ ‖w‖ + 1 := by
        calc ‖s‖ = ‖conj s‖ := (RCLike.norm_conj s).symm
          _ = ‖(conj s - 1) + 1‖ := by ring_nf
          _ ≤ ‖conj s - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
          _ = ‖w‖ + 1 := by rw [norm_one, hw, norm_sub_rev]
      linarith
    have hwR : R₀ ≤ ‖w‖ := by linarith
    have hw1 : 1 ≤ ‖w‖ := by linarith
    rw [S.xi_eq_xiRight (by linarith)]
    calc ‖S.xiRight w‖ ≤ Real.exp (‖w‖ ^ ρ₀) := hR w hwre hwR
      _ ≤ Real.exp (‖w‖ ^ ρ) := hmono w hw1
      _ ≤ Real.exp ((2 * ‖s‖) ^ ρ) :=
          Real.exp_le_exp.mpr (Real.rpow_le_rpow (norm_nonneg _) hw_le hρ0)
      _ = Real.exp (2 ^ ρ * ‖s‖ ^ ρ) := by
          rw [Real.mul_rpow (by norm_num) (norm_nonneg _)]
      _ < Real.exp (‖s‖ ^ (ρ + 1)) := by
          rw [Real.exp_lt_exp, hpow, mul_comm (‖s‖ ^ ρ) ‖s‖]
          exact mul_lt_mul_of_pos_right (by linarith) hsρ_pos

end SelbergSharp

end DBNSelberg
