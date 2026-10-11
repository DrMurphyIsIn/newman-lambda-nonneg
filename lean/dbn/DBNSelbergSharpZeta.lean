/-
# The zeta instance of `SelbergSharp` (the control)

`zetaSharp` exhibits the Riemann zeta function as an element of the extended Selberg class in the
form `DBNSelbergSharp.SelbergSharp` states it: coefficients `a(n) = 1`, `F = riemannZeta`, a simple
pole at `s = 1` (`m = 1`, with the entire extension `zetaG` of `(s - 1) ζ(s)` produced by Mathlib's
removable-singularity theorem from `riemannZeta_residue_one`), one Gamma factor with `Q = π^{-1/2}`,
`λ = 1/2`, `μ = 0`, root number `ω = 1`.

The two analytic fields are classical facts about `ζ`:

* the functional equation on the strip `0 < Re s < 1`, in the class's conjugated form
  `Φ(s) = conj Φ(1 - conj s)`: both sides are `completedRiemannZeta s`, by Mathlib's
  `completedRiemannZeta_one_sub` together with the conjugation symmetry `conj Λ(s) = Λ(conj s)`,
  which this module proves from Riemann's symmetric integral for `Λ₀`
  (`DBN.completedRiemannZeta₀_eq_integral_psi`, a real kernel against `x^{w}`);
* finite order of `s(s-1) Φ(s) = 2 ξ(s)` on `Re s ≥ 1/2`, from the pinned
  `LiCriterion.XiGrowth.riemannXi_hasFiniteOrder`.

`zetaSharp_xiRight_eq_H` identifies the structure's completed function with the island's `H_0`:
`ξ_{zetaSharp}(s) = s(s-1) Λ(s) = 16 H_0(-i(2s-1))` (the C2 representation theorem `dbn_H0_eq_xi`
in the variable `s = 1/2 + iz/2`).

`zetaSharp_sharpFlow_eq` identifies the structure's Gaussian flow with the island's `H_t` for
`t < 0` (`sharpFlow t = 16 H_t`), so `selberg_newman_sharp` at `zetaSharp` recovers `dbn_newman`
(`dbn_newman_of_sharp`): the zeta control of the `S^#` theorem.

Nothing here is about the zeros of `ζ`; `conjecture1_proved = False`.
-/
import Mathlib
import DBNDefs
import DBNXiRiemann
import DBNXi
import DBNSelbergSharp
import DBNSelbergSharpXi
import DBNSelbergSharpStrip
import DBNSelbergZeta
import DBNGaussConv
import Lc.LiCriterion.XiGrowth

open Complex Filter Topology MeasureTheory Set
open scoped Real ComplexConjugate

namespace DBNSelberg

/-! ### Conjugation symmetry of `Λ₀`, `Λ`, `ζ` -/

/-- `conj (x^w) = x^(conj w)` for a positive real base `x`. -/
lemma conj_ofReal_cpow {x : ℝ} (hx : 0 < x) (w : ℂ) :
    conj ((x : ℂ) ^ w) = (x : ℂ) ^ (conj w) := by
  have harg : (x : ℂ).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact Real.pi_ne_zero.symm
  rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal]

/-- `conj Λ₀(s) = Λ₀(conj s)`, from Riemann's symmetric integral with its real kernel `ψ`. -/
lemma conj_completedRiemannZeta₀ (s : ℂ) :
    conj (completedRiemannZeta₀ s) = completedRiemannZeta₀ (conj s) := by
  rw [DBN.completedRiemannZeta₀_eq_integral_psi, DBN.completedRiemannZeta₀_eq_integral_psi,
    ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  simp only [map_mul, map_add, Complex.conj_ofReal, conj_ofReal_cpow hx0, map_sub, map_div₀,
    map_one, map_ofNat]

/-- `conj Λ(s) = Λ(conj s)`. -/
lemma conj_completedRiemannZeta (s : ℂ) :
    conj (completedRiemannZeta s) = completedRiemannZeta (conj s) := by
  rw [completedRiemannZeta_eq, completedRiemannZeta_eq]
  simp only [map_sub, map_div₀, map_one, conj_completedRiemannZeta₀]

/-- `conj Γ_ℝ(s) = Γ_ℝ(conj s)`. -/
lemma conj_Gammaℝ (s : ℂ) : conj (Gammaℝ s) = Gammaℝ (conj s) := by
  rw [Gammaℝ_def, Gammaℝ_def, map_mul, ← Complex.Gamma_conj, conj_ofReal_cpow Real.pi_pos]
  simp only [map_neg, map_div₀, map_ofNat]

/-- `conj ζ(s) = ζ(conj s)` for `s ≠ 0`. -/
lemma conj_riemannZeta {s : ℂ} (hs : s ≠ 0) : conj (riemannZeta s) = riemannZeta (conj s) := by
  have hs' : conj s ≠ 0 := by
    intro h
    exact hs (by simpa using congrArg conj h)
  rw [riemannZeta_def_of_ne_zero hs, riemannZeta_def_of_ne_zero hs', map_div₀,
    conj_completedRiemannZeta, conj_Gammaℝ]

/-! ### The entire extension of `(s - 1) ζ(s)` -/

/-- The entire extension of `(s - 1) ζ(s)` (the value at `1` is the limit, i.e. the residue `1`). -/
noncomputable def zetaG : ℂ → ℂ :=
  Function.update (fun s => (s - 1) * riemannZeta s) 1
    (limUnder (𝓝[≠] 1) (fun s => (s - 1) * riemannZeta s))

lemma zetaG_eq {s : ℂ} (hs : s ≠ 1) : zetaG s = (s - 1) * riemannZeta s :=
  Function.update_of_ne hs _ _

lemma differentiable_zetaG : Differentiable ℂ zetaG := by
  set f : ℂ → ℂ := fun s => (s - 1) * riemannZeta s with hf
  have hd : ∀ s : ℂ, s ≠ 1 → DifferentiableAt ℂ f s := fun s hs =>
    (differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs)
  -- a punctured ball on which `f` is bounded, from the residue
  have hev : ∀ᶠ s in 𝓝[≠] (1 : ℂ), ‖f s‖ < 2 :=
    riemannZeta_residue_one.norm.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hev
  have hball : Metric.ball (1 : ℂ) ε ∈ 𝓝 (1 : ℂ) :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)
  have hdOn : DifferentiableOn ℂ f (Metric.ball (1 : ℂ) ε \ {1}) := fun s hs =>
    (hd s hs.2).differentiableWithinAt
  have hb : BddAbove (norm ∘ f '' (Metric.ball (1 : ℂ) ε \ {1})) := by
    refine ⟨2, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact (hsub ⟨hx.1, hx.2⟩).le
  have hG : DifferentiableOn ℂ zetaG (Metric.ball (1 : ℂ) ε) :=
    Complex.differentiableOn_update_limUnder_of_bddAbove hball hdOn hb
  intro s
  by_cases hs : s = 1
  · subst hs
    exact hG.differentiableAt hball
  · have hopen : {s : ℂ | s ≠ 1} ∈ 𝓝 s := isOpen_ne.mem_nhds hs
    exact (hd s hs).congr_of_eventuallyEq (eventually_of_mem hopen fun t ht => zetaG_eq ht)

/-! ### The Gamma factor and the functional equation -/

/-- The class's Gamma factor with the zeta data is Mathlib's `Γ_ℝ`. -/
lemma zeta_gammaF_eq (s : ℂ) :
    (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) ^ s *
      (∏ _j : Fin 1, Complex.Gamma (((1 / 2 : ℝ) : ℂ) * s + 0)) = Gammaℝ s := by
  rw [ofReal_pi_rpow_neg_half_cpow, Fin.prod_univ_one, Gammaℝ_def]
  congr 2
  push_cast
  ring

/-- `Γ_ℝ(s) ζ(s) = Λ(s)` on `Re s > 0`. -/
lemma Gammaℝ_mul_riemannZeta {s : ℂ} (hs : 0 < s.re) :
    Gammaℝ s * riemannZeta s = completedRiemannZeta s := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  rw [riemannZeta_def_of_ne_zero hs0, mul_div_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hs)]

/-- The functional equation of `ζ` on the critical strip, in the shape of the
`SelbergSharp.functional_equation` field for the zeta data (`ω = 1`). -/
lemma zeta_functional_equation_strip {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) ^ s *
      (∏ _j : Fin 1, Complex.Gamma (((1 / 2 : ℝ) : ℂ) * s + 0)) * riemannZeta s =
      1 * (starRingEnd ℂ) ((((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) ^ (1 - (starRingEnd ℂ) s) *
        (∏ _j : Fin 1, Complex.Gamma (((1 / 2 : ℝ) : ℂ) * (1 - (starRingEnd ℂ) s) + 0)) *
        riemannZeta (1 - (starRingEnd ℂ) s)) := by
  have hre : 0 < (1 - conj s).re := by
    simp only [sub_re, one_re, conj_re]
    linarith
  rw [zeta_gammaF_eq, zeta_gammaF_eq, Gammaℝ_mul_riemannZeta h0, Gammaℝ_mul_riemannZeta hre,
    one_mul, conj_completedRiemannZeta, map_sub, map_one, conj_conj,
    completedRiemannZeta_one_sub]

/-! ### Finite order on the right half-plane -/

/-- Finite order of `s(s-1) Γ_ℝ(s) ζ(s) = 2 ξ(s)` on `Re s ≥ 1/2`, in the shape of the
`SelbergSharp.finite_order` field for the zeta data (`m = 1`). -/
lemma zeta_finite_order : ∃ ρ₀ R₀ : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → R₀ ≤ ‖s‖ →
    ‖(s * (s - 1)) ^ 1 * (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) ^ s *
      (∏ _j : Fin 1, Complex.Gamma (((1 / 2 : ℝ) : ℂ) * s + 0)) * riemannZeta s‖ ≤
      Real.exp (‖s‖ ^ ρ₀) := by
  obtain ⟨_, ρ, R, hbd⟩ := LiCriterion.XiGrowth.riemannXi_hasFiniteOrder
  refine ⟨max ρ 0 + 1, max R 2, fun s hre hR => ?_⟩
  have hR' : R ≤ ‖s‖ := le_trans (le_max_left _ _) hR
  have h2 : (2 : ℝ) ≤ ‖s‖ := le_trans (le_max_right _ _) hR
  have h1 : (1 : ℝ) ≤ ‖s‖ := by linarith
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at h2
    linarith
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at h2
  have hpos : 0 < s.re := by linarith
  -- the expression is `2 ξ(s)`
  have hexpr : (s * (s - 1)) ^ 1 * (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) ^ s *
      (∏ _j : Fin 1, Complex.Gamma (((1 / 2 : ℝ) : ℂ) * s + 0)) * riemannZeta s =
      2 * LiCriterion.riemannXi s := by
    rw [mul_assoc ((s * (s - 1)) ^ 1), zeta_gammaF_eq, mul_assoc, Gammaℝ_mul_riemannZeta hpos,
      DBN.riemannXi_eq_completedRiemannZeta hs0 hs1]
    ring
  rw [hexpr, norm_mul, Complex.norm_ofNat]
  -- `2 exp(‖s‖^ρ) ≤ exp(‖s‖^ρ + 1) ≤ exp(‖s‖^(max ρ 0 + 1))`
  have hxi : ‖LiCriterion.riemannXi s‖ ≤ Real.exp (‖s‖ ^ ρ) := (hbd s hR').le
  have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hpow : ‖s‖ ^ ρ + 1 ≤ ‖s‖ ^ (max ρ 0 + 1) := by
    rw [Real.rpow_add (by linarith : (0 : ℝ) < ‖s‖), Real.rpow_one]
    have hA : ‖s‖ ^ ρ ≤ ‖s‖ ^ max ρ 0 := Real.rpow_le_rpow_of_exponent_le h1 (le_max_left _ _)
    have hB : 1 ≤ ‖s‖ ^ max ρ 0 := Real.one_le_rpow h1 (le_max_right _ _)
    nlinarith
  calc 2 * ‖LiCriterion.riemannXi s‖ ≤ Real.exp 1 * Real.exp (‖s‖ ^ ρ) :=
        mul_le_mul hexp1 hxi (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (‖s‖ ^ ρ + 1) := by rw [Real.exp_add, mul_comm]
    _ ≤ Real.exp (‖s‖ ^ (max ρ 0 + 1)) := Real.exp_le_exp.mpr hpow

/-! ### The instance -/

/-- The Riemann zeta function as an element of the extended Selberg class `S^#`. -/
noncomputable def zetaSharp : SelbergSharp where
  a := fun _ => 1
  a_one := rfl
  nonconst := ⟨2, le_rfl, one_ne_zero⟩
  summable := fun _ hs => LSeriesSummable_one_iff.mpr hs
  F := riemannZeta
  F_eq := fun _ hs => (LSeries_one_eq_riemannZeta hs).symm
  m := 1
  pole_entire := ⟨zetaG, differentiable_zetaG, fun _ hs => by rw [zetaG_eq hs, pow_one]⟩
  r := 1
  Q := Real.pi ^ (-(1 / 2 : ℝ))
  Q_pos := Real.rpow_pos_of_pos Real.pi_pos _
  lam := fun _ => 1 / 2
  lam_pos := fun _ => by norm_num
  deg_pos := by norm_num [Fin.sum_univ_one]
  mu := fun _ => 0
  mu_re_nonneg := fun _ => by simp
  ω := 1
  ω_norm := norm_one
  functional_equation := fun _ h0 h1 => zeta_functional_equation_strip h0 h1
  finite_order := zeta_finite_order

@[simp] lemma zetaSharp_a (n : ℕ) : zetaSharp.a n = 1 := rfl

@[simp] lemma zetaSharp_F : zetaSharp.F = riemannZeta := rfl

@[simp] lemma zetaSharp_m : zetaSharp.m = 1 := rfl

@[simp] lemma zetaSharp_Q : zetaSharp.Q = Real.pi ^ (-(1 / 2 : ℝ)) := rfl

@[simp] lemma zetaSharp_ω : zetaSharp.ω = 1 := rfl

/-- The structure's `G` (chosen from `pole_entire`) is `(s - 1) ζ(s)` away from `1`. -/
lemma zetaSharp_G_eq {s : ℂ} (hs : s ≠ 1) : zetaSharp.G s = (s - 1) * riemannZeta s := by
  rw [zetaSharp.G_eq hs, zetaSharp_m, zetaSharp_F, pow_one]

/-- The value of the structure's `G` at the pole: `G(1) = 1` (the residue of `ζ` at `1`), by
continuity of `G` and `riemannZeta_residue_one`. -/
lemma zetaSharp_G_one : zetaSharp.G 1 = 1 := by
  have hcont : Tendsto zetaSharp.G (𝓝[≠] (1 : ℂ)) (𝓝 (zetaSharp.G 1)) :=
    (zetaSharp.differentiable_G 1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have heq : zetaSharp.G =ᶠ[𝓝[≠] (1 : ℂ)] fun s => (s - 1) * riemannZeta s :=
    eventually_nhdsWithin_of_forall fun s hs => zetaSharp_G_eq hs
  exact tendsto_nhds_unique (hcont.congr' heq) riemannZeta_residue_one

/-- The completed function of `zetaSharp` on the right half-plane is `2 ξ(s)`,
`ξ = LiCriterion.riemannXi` (entire; the identity holds at `s = 1` too). -/
theorem zetaSharp_xiRight_eq_riemannXi {s : ℂ} (h0 : 0 < s.re) :
    zetaSharp.xiRight s = 2 * LiCriterion.riemannXi s := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at h0
  show s ^ 1 * (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) ^ s *
    (∏ _j : Fin 1, Complex.Gamma (((1 / 2 : ℝ) : ℂ) * s + 0)) * zetaSharp.G s = _
  rw [pow_one, mul_assoc s, zeta_gammaF_eq]
  by_cases hs1 : s = 1
  · subst hs1
    rw [zetaSharp_G_one, Gammaℝ_one]
    unfold LiCriterion.riemannXi
    ring
  · rw [zetaSharp_G_eq hs1, DBN.riemannXi_eq_completedRiemannZeta hs0 hs1,
      ← Gammaℝ_mul_riemannZeta h0]
    ring

/-- The completed function of `zetaSharp` is `s(s-1) Λ(s)` on `Re s > 0`, `s ≠ 1`. (The
restriction to the right half-plane is necessary: at the trivial zeros `s = -2n` the Gamma factor
vanishes and `xiRight s = 0 ≠ s(s-1)Λ(s)`; the structure only uses `xiRight` on `Re s ≥ 1/2`.) -/
theorem zetaSharp_xiRight_eq {s : ℂ} (h0 : 0 < s.re) (h1 : s ≠ 1) :
    zetaSharp.xiRight s = s * (s - 1) * completedRiemannZeta s := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at h0
  rw [zetaSharp_xiRight_eq_riemannXi h0, DBN.riemannXi_eq_completedRiemannZeta hs0 h1]
  ring

/-- **`ξ_{zetaSharp} = 16 H_0` in the variable `s = 1/2 + iz/2`**: on the right half-plane the
completed function of the zeta instance is `16 H_0(-i(2s-1))` (the C2 representation theorem
`dbn_H0_eq_xi`, `H_0(z) = (1/8) ξ(1/2 + iz/2)`). -/
theorem zetaSharp_xiRight_eq_H {s : ℂ} (h0 : 0 < s.re) :
    zetaSharp.xiRight s = 16 * DBN.H 0 (-I * (2 * s - 1)) := by
  rw [zetaSharp_xiRight_eq_riemannXi h0, dbn_H0_eq_xi]
  have hs' : (1 / 2 : ℂ) + I * (-I * (2 * s - 1)) / 2 = s := by
    linear_combination (-(2 * s - 1) / 2) * Complex.I_mul_I
  rw [hs']
  ring

/-- The glued completed function `zetaSharp.xi` on `Re s ≥ 1/2` is `16 H_0(-i(2s-1))`. -/
theorem zetaSharp_xi_eq_H {s : ℂ} (h : 1 / 2 ≤ s.re) :
    zetaSharp.xi s = 16 * DBN.H 0 (-I * (2 * s - 1)) := by
  rw [SelbergSharp.xi, ite_eq_left h]
  exact zetaSharp_xiRight_eq_H (by linarith)

/-! ### `ξ_{zetaSharp} = 16 H_0` everywhere, and the flow -/

/-- `conj H_t(z) = H_t(conj z)`: the integrand `e^{tu²} Φ(u) cos(zu)` has real coefficients. -/
lemma H_conj (t : ℝ) (z : ℂ) : conj (DBN.H t z) = DBN.H t (conj z) := by
  unfold DBN.H DBN.HIntegrand
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  simp only [map_mul, Complex.conj_ofReal, ← Complex.cos_conj]

lemma H_zero_conj (z : ℂ) : conj (DBN.H 0 z) = DBN.H 0 (conj z) := H_conj 0 z

/-- The glued completed function `zetaSharp.xi` is `16 H_0(-i(2s-1))` for EVERY `s` (the left
half-plane through the reflected branch `xiLeft`, `ω = 1`, and `conj H_0 = H_0 ∘ conj`). -/
theorem zetaSharp_xi_eq_H_all (s : ℂ) : zetaSharp.xi s = 16 * DBN.H 0 (-I * (2 * s - 1)) := by
  by_cases h : 1 / 2 ≤ s.re
  · exact zetaSharp_xi_eq_H h
  · rw [SelbergSharp.xi, ite_eq_right h, SelbergSharp.xiLeft, zetaSharp_ω, one_mul]
    have hre : 0 < (1 - conj s).re := by
      simp only [sub_re, one_re, conj_re]
      linarith
    rw [zetaSharp_xiRight_eq_H hre, map_mul, map_ofNat, H_zero_conj]
    congr 2
    rw [map_mul, map_neg, Complex.conj_I, map_sub, map_mul, map_sub, map_one, conj_conj,
      map_ofNat]
    ring

/-- The structure's Gaussian flow of `zetaSharp` is `16 H_t` for `t < 0`. -/
theorem zetaSharp_sharpFlow_eq {t : ℝ} (ht : t < 0) (z : ℂ) :
    zetaSharp.sharpFlow t z = 16 * DBN.H t z := by
  have hc : 0 < -t := by linarith
  have hH := DBNGaussConv.H_neg_eq_gauss hc z
  rw [neg_neg] at hH
  have harg : ∀ ω : ℝ, -I * (2 * (1 / 2 + I * (z + ω) / 2) - 1) = z + ω := fun ω => by
    linear_combination (-(z + ω)) * Complex.I_mul_I
  unfold SelbergSharp.sharpFlow
  simp_rw [zetaSharp_xi_eq_H_all, harg]
  rw [hH, show (∫ ω : ℝ, DBNGaussConv.gaussKer (-t) ω * (16 * DBN.H 0 (z + ω))) =
      16 * ∫ ω : ℝ, DBNGaussConv.gaussKer (-t) ω * DBN.H 0 (z + ω) from by
    rw [← integral_const_mul]
    congr 1
    ext ω
    ring]
  ring

end DBNSelberg

/-- **The ζ control for the `S^#` theorem**: `selberg_newman_sharp` applied to `zetaSharp` recovers
`dbn_newman` (for every `t < 0`, `H_t` has a non-real zero), because
`zetaSharp.sharpFlow t = 16 · H_t` for `t < 0`.  `Λ ≥ 0` in the sInf-free vocabulary; `Λ = 0` is
RH and is NOT proved.  conjecture1_proved = False. -/
theorem dbn_newman_of_sharp : ∀ t : ℝ, t < 0 → ∃ z : ℂ, DBN.H t z = 0 ∧ z.im ≠ 0 := by
  intro t ht
  obtain ⟨z, hz, him⟩ := selberg_newman_sharp DBNSelberg.zetaSharp t ht
  refine ⟨z, ?_, him⟩
  rw [DBNSelberg.zetaSharp_sharpFlow_eq ht] at hz
  simpa using hz
