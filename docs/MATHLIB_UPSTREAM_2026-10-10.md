# Mathlib upstreaming report: dbn-island analysis lemmas

Date: 2026-10-10
Fork: https://github.com/DrMurphyIsIn/mathlib4 (clone at `~/mathlib4-fork`, `upstream` = leanprover-community/mathlib4)
Base: upstream/master at `30a8d74cfa` (toolchain `leanprover/lean4:v4.35.0-rc4`), cache hit confirmed.
Sources (read-only): `~/arda-e9-audit/telperion/examples/dbn/lean/` (Mathlib pin `de5ce8a9`, Lean v4.34.0-rc1).

No pull request, issue, or comment was opened. No posts anywhere. Five branches are pushed to the fork.

Every branch: one commit, author `Peter W. Murphy <petermurphy@mountainviewdirectcare.com>`, builds with
`lake build Mathlib.<Path>` (no errors, no warnings), `lake exe lint-style` passes, and `#print axioms` on every main
declaration reports exactly `[propext, Classical.choice, Quot.sound]`. No `sorry`, no `set_option maxHeartbeats`.
Swap stayed at 715 MB used throughout (never near the 8 GB limit).

Master-API notes that apply to all branches: master now uses the module system (`module` / `public import` /
`@[expose] public section`), so the island's `import Mathlib` was replaced by explicit imports and the new files use
the module header. Mathlib's text linter rejects the combining tilde in `B̃₂`; it was replaced with `B₂` plus the word
"periodised". Inside `namespace Complex`, `open Stirling` is flagged as ambiguous with the root `Stirling` namespace;
the file uses `open _root_.Complex.Stirling` and `_root_.Stirling.*`. In `GaussianIntegral.lean`, `open Complex hiding
exp` makes `exp_add` etc. ambiguous, so the real lemmas are written `Real.exp_add` etc.

## Summary table

| # | Candidate | Master status | Branch | Lines added | Build | Axioms |
|---|-----------|---------------|--------|-------------|-------|--------|
| 1 | Complex Stirling with remainder, digamma asymptotic | ABSENT (master: real `Stirling.*`, `Complex.digamma` basics only) | `complex-stirling-remainder` | 753 (+1 in `Mathlib.lean`) | OK | clean |
| 2 | `‖Gamma v‖ ≤ Real.Gamma v.re` | ABSENT | `gamma-norm-le-gamma-re` | 11 | OK | clean |
| 3 | `‖exp Q - 1‖ ≤ ‖Q‖ exp ‖Q‖` | PARTIALLY PRESENT: `Complex.norm_exp_sub_sum_le_norm_mul_exp x 1` gives it after `simp` | `norm-exp-sub-one-le` (2 one-line corollaries) | 10 | OK | clean |
| 4 | Bohr almost periodicity of Dirichlet series | ABSENT | `lseries-almost-periodic` | 307 (+1 in `Mathlib.lean`) | OK | clean |
| 5 | `(1+|x|)^k exp(-b x^2 + a|x|)` integrable + bound | ABSENT (not one line from `integrable_rpow_mul_exp_neg_mul_sq`: the linear term `a|x|` needs completing the square) | `gaussian-poly-integrable` | 66 | OK | clean |

Not in the branch list, recorded for completeness: `DBNSaddleBounds.log_half_add_eq` (the branch-free split
`log ((b+δ)/2) = log (b/2) + log (1 + δ/b)` under `0 < im b`, `0 < im (b+δ)`, `‖δ‖ ≤ ‖b‖/2`) was not searched for or
ported.

---

## 1. `complex-stirling-remainder`

File: `Mathlib/Analysis/SpecialFunctions/Gamma/ComplexStirling.lean` (new, 753 lines; registered in `Mathlib.lean`).
Commit: `ff9f4322a7` "feat(Analysis/SpecialFunctions/Gamma): Stirling's formula for the complex Gamma function with
remainder".

Master search: `Mathlib/Analysis/SpecialFunctions/Stirling.lean` has only the real factorial version
(`Stirling.stirlingSeq`, `tendsto_stirlingSeq_sqrt_pi`, `log_stirlingSeq_formula`, `le_log_factorial_stirling`).
`Gamma/Digamma.lean` (Thomas Browning, 2026) defines `Complex.digamma := logDeriv Gamma` and proves the recurrence,
reflection, duplication, values at 1 and 1/2, meromorphy; its TODO lists Gauss' integral representation. No complex
Stirling, no digamma asymptotic, no Euler-Maclaurin remainder anywhere in master.

Imports: `Analysis.Calculus.ParametricIntegral`, `Analysis.SpecialFunctions.Complex.LogDeriv`,
`Analysis.SpecialFunctions.Gamma.Beta`, `Analysis.SpecialFunctions.Gamma.Digamma`,
`Analysis.SpecialFunctions.Stirling`, `MeasureTheory.Function.Floor`.

Main declarations (namespace `Complex`):

```lean
noncomputable def stirlingRemainder (z : ℂ) : ℂ :=
  1 / (12 * z) + (1 / 2) * ∫ x in Ioi 0, Stirling.kernel z x
  -- Stirling.kernel z x = (periodicBernoulliTwo x : ℂ) * (-(1 / (z + x) ^ 2)),
  -- periodicBernoulliTwo x = Int.fract x ^ 2 - Int.fract x + 1 / 6

theorem Gamma_eq_exp_stirling {z : ℂ} (hz : 0 < z.re) :
    Gamma z = exp ((z - 1 / 2) * log z - z + (1 / 2) * Real.log (2 * π) + stirlingRemainder z)

theorem norm_stirlingRemainder_le {z : ℂ} (hz : 0 < z.re) : ‖stirlingRemainder z‖ ≤ 1 / (4 * ‖z‖)

noncomputable def stirlingRemainderDeriv (z : ℂ) : ℂ :=
  -1 / (12 * z ^ 2) + ∫ x in Ioi 0, Stirling.kernelDeriv z x
  -- Stirling.kernelDeriv z x = (periodicBernoulliTwo x : ℂ) * (1 / (z + x) ^ 3)

theorem hasDerivAt_stirlingRemainder {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt stirlingRemainder (stirlingRemainderDeriv z) z
theorem differentiableAt_stirlingRemainder {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ stirlingRemainder z
theorem deriv_stirlingRemainder {z : ℂ} (hz : 0 < z.re) : deriv stirlingRemainder z = stirlingRemainderDeriv z

theorem norm_stirlingRemainderDeriv_le {z : ℂ} (hz : 0 < z.re) :
    ‖stirlingRemainderDeriv z‖ ≤ 1 / (2 * ‖z‖ ^ 2)

theorem digamma_eq_stirling {z : ℂ} (hz : 0 < z.re) :
    digamma z = log z - 1 / (2 * z) + stirlingRemainderDeriv z

theorem norm_digamma_sub_log_le {z : ℂ} (hz : 0 < z.re) :
    ‖digamma z - log z‖ ≤ 1 / (2 * ‖z‖) + 1 / (2 * ‖z‖ ^ 2)
```

Auxiliary material lives in `Complex.Stirling` (periodicBernoulliTwo, kernel, antiderivLog, bernoulliCell,
bernoulliCellDeriv, cellAntideriv, cellTelescope, the Euler-Maclaurin identity `sum_log_add_natCast_eq`,
`logGammaSeq` with `exp_logGammaSeq : exp (logGammaSeq z n) = GammaSeq z n`, `logGammaStirling`, `seqError`,
`tendsto_logGammaSeq`, `Gamma_eq_exp_logGammaStirling`, `hasDerivAt_logGammaStirling`, the elementary integrals
`integral_inv_sq_add : ∫ x in Ioi 0, 1 / (a + x) ^ 2 = 1 / a` and `integral_inv_cube_add`).

`#print axioms`: `Gamma_eq_exp_stirling`, `norm_stirlingRemainder_le`, `hasDerivAt_stirlingRemainder`,
`norm_stirlingRemainderDeriv_le`, `digamma_eq_stirling`, `norm_digamma_sub_log_le`,
`Stirling.sum_log_add_natCast_eq`: all `[propext, Classical.choice, Quot.sound]`.

Changes relative to `DBNStirling.lean` (655 lines): renamed everything to Mathlib conventions
(`sawB2` -> `Complex.Stirling.periodicBernoulliTwo`, `kern`/`kern'` -> `kernel`/`kernelDeriv`, `F` -> `antiderivLog`,
`P`/`Pd` -> `bernoulliCell`/`bernoulliCellDeriv`, `Φ` -> `cellAntideriv`, `G` -> `cellTelescope`,
`Lseq` -> `logGammaSeq`, `D` -> `seqError`, `L` -> `logGammaStirling`, `R` -> `Complex.stirlingRemainder`,
`R'` -> `Complex.stirlingRemainderDeriv`, `sum_log_eq` -> `sum_log_add_natCast_eq`, `Gamma_eq_exp_L` ->
`Gamma_eq_exp_stirling` with the right-hand side written out, `digamma_eq` -> `digamma_eq_stirling`); the public
theorem is stated without the auxiliary `L`, via an intermediate `Gamma_eq_exp_logGammaStirling`; the last step of the
digamma proof uses `mul_div_cancel_left₀` instead of `field_simp` (the `field_simp` left a goal once the two sides were
no longer syntactically `exp (L z)`); `show` -> `change` (Mathlib's `linter.style.show`); long lines wrapped; registry
commentary dropped; added `differentiableAt_stirlingRemainder` and `deriv_stirlingRemainder`; module docstring with
`# Title`, `## Main definitions`, `## Main results`, `## References` (`[WW21]`, the existing Whittaker-Watson key in
`docs/references.bib`). No API drift was hit: every lemma name used by the island proof still exists on master.

Reviewer-facing notes: `Mathlib/NumberTheory/ZetaValues.lean` already has `periodizedBernoulli 2` (as
`AddCircle.liftIco 1 0 (bernoulliFun 2)`); the file does not import it (that import pulls in Fourier analysis) and uses
the elementary `Int.fract` definition instead. A reviewer may ask for the two to be identified or for the
Euler-Maclaurin pieces to be made `private`.

Suggested PR title: `feat(Analysis/SpecialFunctions/Gamma): Stirling's formula for the complex Gamma function with remainder`

Suggested PR description: This PR proves Stirling's formula for `Complex.Gamma` on the right half-plane in the
Euler-Maclaurin form `Gamma z = exp ((z - 1/2) * log z - z + (1/2) * log (2π) + R z)` with the explicit remainder
`R z = 1/(12 z) - (1/2) ∫_0^∞ B₂({x})/(z+x)² dx` and the bound `‖R z‖ ≤ 1/(4‖z‖)`. The remainder is shown to be
differentiable with `‖R' z‖ ≤ 1/(2‖z‖²)`, which gives the asymptotic expansion of the digamma function,
`digamma z = log z - 1/(2z) + R' z`, and `‖digamma z - log z‖ ≤ 1/(2‖z‖) + 1/(2‖z‖²)`. Mathlib previously had only
the real factorial Stirling formula (`Stirling.tendsto_stirlingSeq_sqrt_pi`) and the Bohr-Mollerup characterisation.
The proof goes through Euler's limit formula `GammaSeq_tendsto_Gamma`, second-order Euler-Maclaurin summation of
`∑ log (z + k)` on unit intervals from an explicit antiderivative, and the real Stirling formula for `log n!`; no
branch of `log Γ` is chosen, every statement is about `exp` of the right-hand side.

---

## 2. `gamma-norm-le-gamma-re`

File: `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean` (11 lines added after `Complex.Gamma_ofReal`, inside
`namespace Real`, declared with `_root_.Complex.`).
Commit: `5571594f31` "feat(Analysis/SpecialFunctions/Gamma): `‖Gamma s‖ ≤ Gamma (re s)` on the right half-plane".

Master search: grep for `norm_Gamma`, `abs_Gamma`, `Gamma_re`, `‖Gamma`, `‖Complex.Gamma` across `Mathlib/` finds
nothing of this shape (only `‖Gammaℝ (1/2 + t I)‖` in `LSeries/HardyZ.lean`). ABSENT.

```lean
theorem Complex.norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) : ‖Complex.Gamma s‖ ≤ Real.Gamma s.re
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

Changes relative to `DBNGaussConv.norm_Gamma_le_Gamma_re`: variable renamed `v` -> `s` to match the file;
`norm_integral_le_integral_norm` qualified as `MeasureTheory.norm_integral_le_integral_norm` (ambiguous with the
`intervalIntegral` version in that file); otherwise the proof is the island's (compare Euler's integrals termwise using
`Complex.norm_cpow_eq_rpow_re_of_pos`).

Suggested PR title: `feat(Analysis/SpecialFunctions/Gamma): norm of the complex Gamma function is bounded by the real Gamma function`

Suggested PR description: Adds `Complex.norm_Gamma_le_Gamma_re`: for `0 < re s`, `‖Complex.Gamma s‖ ≤ Real.Gamma
s.re`. The proof compares the two Euler integrals pointwise. This is the standard estimate used to dominate
Gamma-weighted Dirichlet series and Mellin-type integrals on vertical lines.

---

## 3. `norm-exp-sub-one-le`

File: `Mathlib/Analysis/Complex/Exponential.lean` (10 lines added: one lemma after
`Complex.norm_exp_sub_sum_le_norm_mul_exp`, one after `Real.abs_exp_sub_one_sub_id_le`).
Commit: `ffb9dd1504` "feat(Analysis/Complex/Exponential): `‖exp x - 1‖ ≤ ‖x‖ * exp ‖x‖` without a size restriction".

Master search: `Complex.norm_exp_sub_one_le : ‖x‖ ≤ 1 → ‖exp x - 1‖ ≤ 2 * ‖x‖` (needs the size restriction);
`Complex.norm_exp_sub_sum_le_norm_mul_exp (x) (n) : ‖exp x - ∑ m ∈ range n, x^m/m! ‖ ≤ ‖x‖^n * Real.exp ‖x‖`
(Mathlib/Analysis/Complex/Exponential.lean:485) specialises at `n = 1` to exactly the island statement after `simp`.
Status: PARTIALLY PRESENT (content present, named corollary absent). The branch is therefore tiny and optional; it
records the named form the island uses.

```lean
lemma Complex.norm_exp_sub_one_le_norm_mul_exp (x : ℂ) : ‖exp x - 1‖ ≤ ‖x‖ * Real.exp ‖x‖
theorem Real.abs_exp_sub_one_le_abs_mul_exp (x : ℝ) : |exp x - 1| ≤ |x| * exp |x|
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

Changes relative to `DBNSaddleBounds.norm_exp_sub_one_le_mul_exp`: the island's 20-line FTC proof (integrate
`t ↦ exp (t Q)` over `[0,1]`) is replaced by `simpa using norm_exp_sub_sum_le_norm_mul_exp x 1`; a real corollary was
added for symmetry with the neighbouring `abs_exp_sub_one_le` pair. The IsROrC/normed-algebra generalisation was not
attempted because the series lemma it rests on is specific to `Complex.exp`.

Suggested PR title: `feat(Analysis/Complex/Exponential): ‖exp x - 1‖ ≤ ‖x‖ * exp ‖x‖`

Suggested PR description: Adds `Complex.norm_exp_sub_one_le_norm_mul_exp` and `Real.abs_exp_sub_one_le_abs_mul_exp`,
the `n = 1` case of `Complex.norm_exp_sub_sum_le_norm_mul_exp`. Unlike `Complex.norm_exp_sub_one_le` these need no
bound on `‖x‖`, which is the form needed when the argument is only known to be `O(1)`.

---

## 4. `lseries-almost-periodic`

File: `Mathlib/NumberTheory/LSeries/AlmostPeriodic.lean` (new, 307 lines; registered in `Mathlib.lean`).
Commit: `0dd3afaa8f` "feat(NumberTheory/LSeries): Bohr almost periodicity of Dirichlet series".

Master search: no `AlmostPeriodic` file, no `almost periodic`/`Bohr` hits in `Mathlib/NumberTheory/LSeries/`
(the only `Bohr` hits in Mathlib are Bohr-Mollerup and a `ConvexBody` comment). ABSENT.

Imports: `NumberTheory.LSeries.Basic`, `Topology.Sequences`, `Topology.UniformSpace.LocallyUniformConvergence`.

Main declarations (namespace `LSeries`):

```lean
noncomputable def twist (k n : ℕ) : ℂ := (n : ℂ) ^ (-((k : ℂ) * I))
lemma norm_twist {n : ℕ} (hn : 0 < n) (k : ℕ) : ‖twist k n‖ = 1
lemma term_add_natCast_mul_I (f : ℕ → ℂ) (s : ℂ) (k n : ℕ) :
    term f (s + (k : ℂ) * I) n = term f s n * twist k n

theorem exists_twist_close (N : ℕ) {ε : ℝ} (hε : 0 < ε) (T : ℕ) :
    ∃ k : ℕ, T ≤ k ∧ ∀ n : ℕ, 1 ≤ n → n ≤ N → ‖twist k n - 1‖ < ε

theorem norm_sub_le_of_le_re (f : ℕ → ℂ) {r : ℝ} (hr : LSeriesSummable f r) {s : ℂ} (hs : r ≤ s.re) (k m : ℕ) :
    ‖LSeries f (s + (k : ℂ) * I) - LSeries f s‖ ≤
      (∑ n ∈ Finset.range m, ‖term f r n‖ * ‖twist k n - 1‖) + 2 * ∑' i, ‖term f r (i + m)‖

theorem exists_le_norm_sub_lt (f : ℕ → ℂ) {r : ℝ} (hr : LSeriesSummable f r) {ε : ℝ} (hε : 0 < ε) (T : ℕ) :
    ∃ k : ℕ, T ≤ k ∧ ∀ s : ℂ, r ≤ s.re → ‖LSeries f (s + (k : ℂ) * I) - LSeries f s‖ < ε

theorem exists_strictMono_forall_norm_sub_lt (f : ℕ → ℂ) {a : ℕ → ℝ} (ha : ∀ j, LSeriesSummable f (a j)) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∀ j, ∀ s : ℂ, a j ≤ s.re →
      ‖LSeries f (s + (τ j : ℂ) * I) - LSeries f s‖ < 1 / ((j : ℝ) + 1)

theorem exists_strictMono_tendstoLocallyUniformlyOn (f : ℕ → ℂ) {σ : ℝ}
    (hf : ∀ s : ℂ, σ < s.re → LSeriesSummable f s) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ TendstoLocallyUniformlyOn
      (fun j s => LSeries f (s + (τ j : ℂ) * I)) (LSeries f) atTop {s | σ < s.re}

theorem exists_strictMono_tendstoLocallyUniformly (f : ℕ → ℂ) (hf : ∀ s : ℂ, LSeriesSummable f s) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧
      TendstoLocallyUniformly (fun j s => LSeries f (s + (τ j : ℂ) * I)) (LSeries f) atTop
```

Axioms (`exists_twist_close`, `exists_le_norm_sub_lt`, `exists_strictMono_tendstoLocallyUniformlyOn`,
`exists_strictMono_tendstoLocallyUniformly`): `[propext, Classical.choice, Quot.sound]`.

Changes relative to `DBNBohr.lean` (307 lines): the island's theorem `exists_shifts_tendstoLocallyUniformly` (whole
plane, `∀ s, LSeriesSummable f s`) is now `exists_strictMono_tendstoLocallyUniformly`, and the requested half-plane
version `exists_strictMono_tendstoLocallyUniformlyOn` (uniform convergence on compact subsets of `{σ < re s}`) was added.
Both are corollaries of a new core lemma `exists_strictMono_forall_norm_sub_lt` parametrised by an arbitrary sequence of
real levels `a j` (the whole-plane case uses `a j = -j`, the half-plane case `a j = σ + 1/(j+1)`, with the minimum of
`re` on the compact set via `IsCompact.exists_isMinOn`). The island's `Classical.choose`-based definitions `cutoff`,
`headMass`, `delta`, `shift` (defs carrying proof arguments) were removed; the shifts are built inside the proof with
`choose` and `Nat.rec`. The basic estimate now only assumes summability at the single real point `r` (summability at
`s` and `s + kI` follows from `LSeriesSummable.of_re_le_re`), instead of everywhere. Renames:
`norm_term_mul_twist_sub_one_le` -> `norm_term_mul_norm_twist_sub_one_le`, `term_add_mul_I` ->
`term_add_natCast_mul_I`, `norm_LSeries_shift_sub_le` -> `norm_sub_le_of_le_re`; `tail`, `eps`, `twistVec` inlined.
No API drift was hit.

Suggested PR title: `feat(NumberTheory/LSeries): Bohr almost periodicity of Dirichlet series`

Suggested PR description: Bohr's theorem says that a Dirichlet series which converges absolutely on a half-plane is
uniformly almost periodic on every smaller half-plane. This PR proves the sequential form: if `∑ f n / n^s` converges
absolutely for all `s` with `σ < re s`, there is a strictly increasing sequence of natural numbers `τ j` such that the
vertical translates `s ↦ LSeries f (s + τ j * I)` converge to `LSeries f` locally uniformly on `{s | σ < re s}`
(`LSeries.exists_strictMono_tendstoLocallyUniformlyOn`), and locally uniformly on `ℂ` when the series converges
absolutely everywhere (`LSeries.exists_strictMono_tendstoLocallyUniformly`). The only arithmetic input is the
recurrence of the finite vectors of unit twists `(n^(-k I))_{n ≤ N}`, `LSeries.exists_twist_close`, which is proved by
sequential compactness of the closed unit ball of `Fin N → ℂ`; no Diophantine approximation (Kronecker/Dirichlet) is
needed. The one-level statement `LSeries.exists_le_norm_sub_lt` (a shift `k ≥ T` with the translate within `ε` of the
series uniformly on `r ≤ re s`) is exposed separately.

---

## 5. `gaussian-poly-integrable`

File: `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean` (66 lines added as a new
`section PolynomialGaussian` after `integral_gaussian_Ioi`, before `Real.Gamma_one_half_eq`).
Commit: `42d5ff626e` "feat(Analysis/SpecialFunctions/Gaussian): integrability of polynomial-times-Gaussian majorants".

Master search: `GaussianIntegral.lean` has `integrable_rpow_mul_exp_neg_mul_sq` (`x^s * exp(-b x²)`),
`integrable_exp_neg_mul_sq`, `integrable_mul_exp_neg_mul_sq`, `integral_gaussian`; `FourierTransform.lean` has the
complex `integrable_cexp_neg_mul_sq_add_real_mul_I` and `integral_cexp_quadratic`; `PoissonSummation.lean` has
`isLittleO` statements for `exp (a x² + b x)`. None covers a `|x|`-linear term in the exponent on all of `ℝ` with a
polynomial prefactor, and the reduction to `integrable_rpow_mul_exp_neg_mul_sq` is not one line (it needs the
completed square and the `(1+|x|)^k ≤ exp (k|x|)` step). Status: ABSENT; the branch was created (not skipped).

```lean
theorem one_add_abs_pow_mul_exp_le (k : ℕ) (a x : ℝ) :
    (1 + |x|) ^ k * exp (a * |x|) ≤ exp ((a + k) * |x|)
theorem neg_mul_sq_add_mul_abs_le {b : ℝ} (hb : 0 < b) (a x : ℝ) :
    -b * x ^ 2 + a * |x| ≤ -(b / 2) * x ^ 2 + a ^ 2 / (2 * b)
theorem one_add_abs_pow_mul_exp_neg_mul_sq_add_mul_abs_le {b : ℝ} (hb : 0 < b) (a : ℝ) (k : ℕ) (x : ℝ) :
    (1 + |x|) ^ k * exp (-b * x ^ 2 + a * |x|) ≤ exp ((a + k) ^ 2 / (2 * b)) * exp (-(b / 2) * x ^ 2)
theorem integrable_one_add_abs_pow_mul_exp_neg_mul_sq_add_mul_abs {b : ℝ} (hb : 0 < b) (a : ℝ) (k : ℕ) :
    Integrable fun x : ℝ => (1 + |x|) ^ k * exp (-b * x ^ 2 + a * |x|)
theorem integral_one_add_abs_pow_mul_exp_neg_mul_sq_add_mul_abs_le {b : ℝ} (hb : 0 < b) (a : ℝ) (k : ℕ) :
    ∫ x : ℝ, (1 + |x|) ^ k * exp (-b * x ^ 2 + a * |x|) ≤ exp ((a + k) ^ 2 / (2 * b)) * √(π / (b / 2))
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

Changes relative to `DBNSaddleSum.lean` (`one_add_abs_pow_mul_exp_le`, `neg_mul_sq_add_le`, `gauss_poly_le`,
`integrable_gauss_poly`, `integral_gauss_poly_le`): renamed to Mathlib conventions (the `gauss_poly` vocabulary is
gone), variable `σ` -> `x`, real exponential lemmas qualified `Real.*` because the file does `open Complex hiding exp`.
Proofs otherwise identical. The names are long; a reviewer may prefer a `def` for the majorant or shorter names.

Suggested PR title: `feat(Analysis/SpecialFunctions/Gaussian): integrability of (1 + |x|)^k * exp (-b x^2 + a |x|)`

Suggested PR description: Adds integrability on `ℝ` of `(1 + |x|)^k * exp (-b * x^2 + a * |x|)` for `0 < b` and any
real `a`, together with the pointwise domination by `exp ((a+k)²/(2b)) * exp (-(b/2) x²)` (completing the square and
`1 + t ≤ exp t`) and the resulting explicit bound on the integral in terms of `√(π/(b/2))`. These are the standard
majorants for Gaussian integrals perturbed by a polynomial prefactor and a linear exponential twist, e.g. in
saddle-point estimates.

---

## Verification log

Per branch, in `~/mathlib4-fork`, all Lean invocations wrapped with `ARDA_LEAN_SLOTS=1 ~/hodge-engine/leanlock.sh`:

- `lake build Mathlib.Analysis.SpecialFunctions.Gamma.ComplexStirling` : Build completed successfully (2925 jobs), no warnings.
- `lake build Mathlib.Analysis.SpecialFunctions.Gamma.Basic` : Build completed successfully (2855 jobs).
- `lake build Mathlib.Analysis.Complex.Exponential` : Build completed successfully (1577 jobs).
- `lake build Mathlib.NumberTheory.LSeries.AlmostPeriodic` : Build completed successfully (2449 jobs).
- `lake build Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral` : Build completed successfully (2863 jobs).
- `lake exe lint-style` : no new style errors on any branch (first Stirling run found 9 unicode errors from the
  combining tilde, fixed before commit).
- `#print axioms` outputs saved in the scratchpad: `axioms_stirling.out`, `axioms_gamma.out`, `axioms_exp.out`,
  `axioms_bohr.out`, `axioms_gauss.out`.
- `lake exe cache get` : 9023 files, exit 0. Sanity build of `Gamma.Beta` took under 5 s (cache hit).

Only the target module was built on each branch, not all of Mathlib. Nothing downstream imports the new files, and the
three edited files only gained declarations at the end of sections, so downstream breakage is not expected, but a full
`lake build` was not run.

## Branch URLs and compare pages

Fork: https://github.com/DrMurphyIsIn/mathlib4

Compare pages (open in a browser; the "Create pull request" button is on each page):

- https://github.com/leanprover-community/mathlib4/compare/master...DrMurphyIsIn:mathlib4:complex-stirling-remainder
- https://github.com/leanprover-community/mathlib4/compare/master...DrMurphyIsIn:mathlib4:gamma-norm-le-gamma-re
- https://github.com/leanprover-community/mathlib4/compare/master...DrMurphyIsIn:mathlib4:norm-exp-sub-one-le
- https://github.com/leanprover-community/mathlib4/compare/master...DrMurphyIsIn:mathlib4:lseries-almost-periodic
- https://github.com/leanprover-community/mathlib4/compare/master...DrMurphyIsIn:mathlib4:gaussian-poly-integrable

Git commands to inspect locally:

```sh
cd ~/mathlib4-fork
git fetch origin
for b in complex-stirling-remainder gamma-norm-le-gamma-re norm-exp-sub-one-le \
         lseries-almost-periodic gaussian-poly-integrable; do
  echo "== $b"; git log --oneline upstream/master..origin/$b; git diff --stat upstream/master..origin/$b
done
# open a compare page from the shell (macOS):
open "https://github.com/leanprover-community/mathlib4/compare/master...DrMurphyIsIn:mathlib4:complex-stirling-remainder"
# or, if you decide to open a PR yourself with gh (NOT done by the agent):
# gh pr create --repo leanprover-community/mathlib4 --base master --head DrMurphyIsIn:complex-stirling-remainder \
#   --title "..." --body-file body.md
```

Mathlib PR conventions worth remembering before opening anything: PRs need the `t-analysis` / `t-number-theory`
labels and the author needs write access to the Mathlib repo (or must ask on Zulip `#mathlib4 > new members` for a
maintainer to push the branch to `leanprover-community/mathlib4`, since CI only runs on branches of the main repo).
The user's Zulip policy applies: the user writes any Zulip post themselves.
