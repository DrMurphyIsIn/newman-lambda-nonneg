/-
# The extended Selberg class `S^#` as a structure, and its completed function

`DBNSelbergData.ExtSelbergData` carries the five analytic facts Dobner's proof consumes; two of
them (the completed function is entire; it is bounded on vertical strips) are THEOREMS for an honest
element of the extended Selberg class, not axioms. This module states the class itself, as close to
Kaczorowski–Perelli's definition of `S^#` as the island can state it:

* a Dirichlet series `F(s) = ∑ a(n) n^{-s}`, absolutely convergent for `Re s > 1`, normalized
  `a(1) = 1`, not a single term;
* a meromorphic continuation with at most a pole at `s = 1` of order `m`: `F : ℂ → ℂ` with
  `(s - 1)^m F(s)` extending to an entire function `G` and `F = LSeries a` on `Re s > 1`;
* Gamma data `Q > 0`, `λ_j > 0`, `Re μ_j ≥ 0`, `d_F = 2 ∑ λ_j > 0`, a root number `|ω| = 1`;
* the functional equation `Φ(s) = ω conj(Φ(1 - conj s))` for `Φ(s) = Q^s ∏ Γ(λ_j s + μ_j) F(s)`,
  stated on the open strip `0 < Re s < 1` where both sides are holomorphic (no pole of `F` or of
  any Gamma factor lies there); by the identity theorem this is the identity of meromorphic
  functions;
* finite order of the completed function `ξ_F(s) = (s(s-1))^m Φ(s)` on the right half-plane
  `Re s ≥ 1/2` (the left half-plane follows from the functional equation). This is the class's
  "`(s-1)^m F` has finite order" axiom combined with Stirling's bound for the Gamma factors; the
  island takes the combination as the axiom.

What is derived (DBNSelbergSharpXi, DBNSelbergSharpStrip): `ξ_F` extends to an entire function of
finite order, equal to `(s(s-1))^m Q^s ∏Γ · ∑ a(n) n^{-s}` on `Re s > 1`, and bounded on every
vertical strip (Phragmén–Lindelöf between `Re s = -1` and `Re s = 2`, with the Gamma factors'
exponential decay `DBNStirling.norm_Gamma_le_vertical` beating the polynomial). Hence every
`SelbergSharp` yields an `ExtSelbergData` (`toExtSelbergData`) and `selberg_newman` applies:
Newman's conjecture for the extended Selberg class as Dobner states it. `Λ_F = 0` is not touched;
`conjecture1_proved = False`.
-/
import Mathlib
import DBNSelbergData

open Complex Filter Topology MeasureTheory Set
open scoped Real

namespace DBNSelberg

/-- An element of the extended Selberg class `S^#`, as the island states it. -/
structure SelbergSharp where
  /-- Dirichlet coefficients; `a 0` is ignored by `LSeries`. -/
  a : ℕ → ℂ
  a_one : a 1 = 1
  nonconst : ∃ n : ℕ, 2 ≤ n ∧ a n ≠ 0
  summable : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s
  /-- The meromorphic continuation of the Dirichlet series (values at poles are irrelevant). -/
  F : ℂ → ℂ
  F_eq : ∀ s : ℂ, 1 < s.re → F s = LSeries a s
  /-- Order of the pole at `s = 1` (`m = 0` if `F` is entire). -/
  m : ℕ
  /-- `(s - 1)^m F(s)` extends to an entire function. (Stated as an extension, not as
  `Differentiable (fun s => (s-1)^m * F s)`: the value of `F` AT the pole is junk, e.g. Mathlib's
  `riemannZeta 1`, so the product's value at `s = 1` need not be the limit.) -/
  pole_entire : ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ ∀ s : ℂ, s ≠ 1 → G s = (s - 1) ^ m * F s
  /-- Number of Gamma factors. -/
  r : ℕ
  Q : ℝ
  Q_pos : 0 < Q
  lam : Fin r → ℝ
  lam_pos : ∀ j, 0 < lam j
  deg_pos : 0 < ∑ j, lam j
  mu : Fin r → ℂ
  mu_re_nonneg : ∀ j, 0 ≤ (mu j).re
  /-- The root number. -/
  ω : ℂ
  ω_norm : ‖ω‖ = 1
  /-- The functional equation on the critical strip, where both sides are holomorphic. -/
  functional_equation : ∀ s : ℂ, 0 < s.re → s.re < 1 →
    ((Q : ℝ) : ℂ) ^ s * (∏ j, Complex.Gamma (lam j * s + mu j)) * F s =
      ω * (starRingEnd ℂ) (((Q : ℝ) : ℂ) ^ (1 - (starRingEnd ℂ) s) *
        (∏ j, Complex.Gamma (lam j * (1 - (starRingEnd ℂ) s) + mu j)) * F (1 - (starRingEnd ℂ) s))
  /-- Finite order of the completed function on the right half-plane. -/
  finite_order : ∃ ρ₀ R₀ : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → R₀ ≤ ‖s‖ →
    ‖(s * (s - 1)) ^ m * ((Q : ℝ) : ℂ) ^ s * (∏ j, Complex.Gamma (lam j * s + mu j)) * F s‖ ≤
      Real.exp (‖s‖ ^ ρ₀)

namespace SelbergSharp

variable (S : SelbergSharp)

/-- `Φ(s) = Q^s ∏ Γ(λ_j s + μ_j) F(s)`: the completed function before the pole-removing factor. -/
noncomputable def Phi (s : ℂ) : ℂ :=
  ((S.Q : ℝ) : ℂ) ^ s * (∏ j, Complex.Gamma (S.lam j * s + S.mu j)) * S.F s

/-- The entire extension of `(s - 1)^m F(s)` (chosen from `pole_entire`). -/
noncomputable def G : ℂ → ℂ := Classical.choose S.pole_entire

lemma differentiable_G : Differentiable ℂ S.G := (Classical.choose_spec S.pole_entire).1

lemma G_eq {s : ℂ} (hs : s ≠ 1) : S.G s = (s - 1) ^ S.m * S.F s :=
  (Classical.choose_spec S.pole_entire).2 s hs

/-- `ξ_F(s) = s^m Q^s ∏ Γ(λ_j s + μ_j) G(s)`, i.e. `(s(s-1))^m Φ(s)` with the pole removed; holomorphic
on the right half-plane `Re s > 0`. -/
noncomputable def xiRight (s : ℂ) : ℂ :=
  s ^ S.m * ((S.Q : ℝ) : ℂ) ^ s * (∏ j, Complex.Gamma (S.lam j * s + S.mu j)) * S.G s

lemma xiRight_eq_Phi {s : ℂ} (hs : s ≠ 1) : S.xiRight s = (s * (s - 1)) ^ S.m * S.Phi s := by
  unfold xiRight Phi
  rw [S.G_eq hs, mul_pow]
  ring

/-- The reflected expression `ω conj(ξ_F(1 - conj s))`, holomorphic on `Re s < 1`. -/
noncomputable def xiLeft (s : ℂ) : ℂ :=
  S.ω * (starRingEnd ℂ) (S.xiRight (1 - (starRingEnd ℂ) s))

/-- The completed function `ξ_F`, glued: the right expression on `Re s ≥ 1/2`, the reflected one
on `Re s < 1/2`. DBNSelbergSharpXi proves it is entire (the two agree on `0 < Re s < 1` by the
functional equation) and of finite order. -/
noncomputable def xi (s : ℂ) : ℂ := if 1 / 2 ≤ s.re then S.xiRight s else S.xiLeft s

/-- The backward heat flow of `ξ_F` for `t < 0`, in the island's `z`-variable (`s = 1/2 + iz/2`):
the Gaussian convolution `(4π|t|)^{-1/2} ∫ e^{-ω²/(4|t|)} ξ_F(1/2 + i(z+ω)/2) dω`. This is
`(toExtSelbergData S).flow t z` definitionally (DBNSelbergSharpStrip); it is the function whose
non-real zeros `selberg_newman_sharp` exhibits. -/
noncomputable def sharpFlow (t : ℝ) (z : ℂ) : ℂ :=
  (1 / ((Real.sqrt (4 * π * (-t)) : ℝ) : ℂ)) *
    ∫ ω : ℝ, DBNGaussConv.gaussKer (-t) ω * S.xi (1 / 2 + I * (z + ω) / 2)

/-- The pole-removing polynomial `(X(X-1))^m`. -/
noncomputable def P : Polynomial ℂ := (Polynomial.X * (Polynomial.X - 1)) ^ S.m

lemma P_eval (s : ℂ) : S.P.eval s = (s * (s - 1)) ^ S.m := by
  simp [P]

lemma P_ne_zero : S.P ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 2) h
  rw [P_eval] at this
  norm_num at this

lemma functional_equation_Phi {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    S.Phi s = S.ω * (starRingEnd ℂ) (S.Phi (1 - (starRingEnd ℂ) s)) := by
  unfold Phi
  exact S.functional_equation s h0 h1

end SelbergSharp

end DBNSelberg
