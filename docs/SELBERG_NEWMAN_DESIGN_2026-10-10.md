# Newman's conjecture for the extended Selberg class: design (2026-10-10)

Programme item 3 of `RH_PROGRAM_2026-10-10.md`. Dobner (arXiv:2005.05142) proves Newman's
conjecture for every element of the extended Selberg class `S^#`; the dbn island has the ζ case
(`dbn_newman`, DBNNewman, PR #679). This note fixes what "the class" means on the island and how
the ζ proof is generalized, module by module. Nothing here concerns the zeros of ζ or of any `F`;
`conjecture1_proved = False`.

## 1. What an element of the class contributes to the proof

Dobner's argument uses five facts about `F`, and only those:

1. the Dirichlet series `F(s) = Σ a(n) n^{-s}` converges absolutely for `Re s > 1`;
2. `F` is normalized, `a(1) = 1`, and is not a single term (some `a(n) ≠ 0` with `n ≥ 2`);
3. the Gamma factor has the shape `γ_F(v) = P(v) Q^v ∏_j Γ(λ_j v + μ_j)` with `Q > 0`, `λ_j > 0`,
   `Re μ_j ≥ 0`, degree `d_F = 2 Σ λ_j > 0`, and a nonzero polynomial `P` that removes the poles;
4. the completed function `Ξ_F` is entire and equals `Σ a(n) γ_F(s) n^{-s}` on `Re s > 1`;
5. `Ξ_F` is bounded on every vertical strip (in `s`), i.e. on every horizontal strip in the
   island's `z = -i(2s-1)` variable.

For an honest element of `S^#` items 4 and 5 are theorems: 4 is the analytic-continuation axiom
after multiplying by `P`, and 5 follows from the functional equation, Phragmén–Lindelöf and
Stirling (the Gamma factor decays like `e^{-(π/2) d_F |Im s| /2}` on vertical strips and `F` is
polynomially bounded there). The functional equation itself is never used beyond that. So the
Lean structure `DBNSelberg.ExtSelbergData` (DBNSelbergData.lean) carries exactly 1–5 as fields, and
the theorem is proved for every instance of the structure. Instantiating it for an actual `S^#`
element means discharging 4–5 for that element; for ζ both are island theorems already
(`DBN.differentiable_H`, `DBNGaussConv.H_zero_eq_tsum`, `DBNGaussConv.norm_H_zero_le`), and
DBNSelbergZeta does that and recovers `dbn_newman` from the general theorem as the control.

The heat flow for `t < 0` is DEFINED as the Gaussian convolution
`flow t z = (4π|t|)^{-1/2} ∫ e^{-ω²/(4|t|)} Ξ_F(z+ω) dω`, which `DBNGaussConv.H_neg_eq_gauss`
proves is the island's `H_t` when `Ξ_F = H_0`. For a general `F` there is no `Φ_F`-series
definition on the island, and none is needed: the Weierstrass transform is the backward heat flow
of any entire function of order one bounded on strips. The registered statement will be

    theorem selberg_newman (F : ExtSelbergData) : ∀ t : ℝ, t < 0 → ∃ z : ℂ, F.flow t z = 0 ∧ z.im ≠ 0

with the caveat, written into the node, that the hypotheses are the structure's fields.

## 2. How the ζ proof generalizes (module map)

The ζ modules are kept untouched; the Selberg modules are new files with `F : ExtSelbergData`
threaded through. All saddle vocabulary is defined once in DBNSelbergData so the analytic modules
are independent of one another.

| ζ module | Selberg module | what changes |
|---|---|---|
| DBNGaussConv (`shift_line`, `H_zero_eq_tsum`, `xi_eq_tsum_B`) | DBNSelbergGauss | `H_0 ↦ Ξ_F` (entire + strip bound from the structure); `γ ↦ γ_F`, dominated by `norm_gammaF_le` (polynomial × `Q^a` × `∏ Γ(λ_j a + Re μ_j)`) and `|a(n)| n^{-a}` summable for `a > 1` |
| DBNSaddleAlg | DBNSelbergSaddleAlg | `ℓ_F(b) = log Q + Σ λ_j Log(λ_j b + μ_j)`; `Q_F(δ) = Σ_j [L(λ_j(b+δ)+μ_j) − L(λ_j b+μ_j) − λ_j δ Log(λ_j b+μ_j)]`; `ρ_F = P(b+δ)/P(b)`; `gammaF_add_eq` is already in DBNSelbergData. `h_n = (c/2) log n` and `a_n = e^{-h_n²/c}` are unchanged: the Gaussian coefficient does not depend on the degree. `B_shift` needs `γ_F` bounded on a compact `a`-range (polynomial, `Q^a`, Gamma continuous on `Re > 0`). `P(b) ≠ 0` is needed where `b(b-1) ≠ 0` was: for `Im b` above the largest root modulus |
| DBNSaddleBounds | DBNSelbergSaddleBounds | near field: for each `j`, `w_j = λ_j b + μ_j`, `u_j = λ_j δ / w_j`; `‖w_j‖ ≥ λ_j y/2` once `y ≥ 2 |Im μ_j| / λ_j` (define `Y₀(F)`), and the log split needs `Im w_j > 0` and `Im(w_j + λ_j δ) > 0`, true in the near region `|σ| ≤ y/2` for `y ≥ Y₀`. Polynomial ratio: `‖ρ_F − 1‖ ≤ C_P (1+‖δ‖)^{deg P} ‖δ‖ / ‖b‖` for `‖δ‖ ≤ ‖b‖/2`, `‖b‖ ≥ R_P`. Global: sum over `j` of the ζ-case estimate; `‖ρ_F‖ ≤ C'_P (‖b‖+‖δ‖+1)^{deg P} / ‖b‖^{deg P}`. The unified bound keeps the Gaussian factor `e^{((h+|σ|)²−y²/4)/(8c)} ≥ 1` as the far-region indicator; polynomial factors are now of degree `deg P + 2` instead of 2 |
| DBNSaddleSum | DBNSelbergSaddleSum | weights carry `|a(n)|`; summability from `Σ |a(n)| n^{-2} < ∞` (field `summable` at `s = 2`) times `sup_n (1+h_n)^k e^{-κ h_n²} n^{β}` bounded; `integral_gauss_poly_le` generalized to degree `k` |
| DBNFtZero, DBNFtZeroHigh | DBNSelbergFtZero | `F_t = Σ a(n) e^{-c' log² n} n^{-s}`: summable everywhere; finite order (`‖F_t(z)‖ ≤ C e^{(2+‖z‖)²/(4c')}`); zero via Hadamard: `F_t = e^g`, `g` polynomial, `F_t(σ) → 1` and `F_t'(σ) → 0` as `σ → ∞` so `g' → 0`, `g'` constant `= 0`, `F_t ≡ 1`, contradiction with `n₀^σ F_t'(σ) → −a(n₀) log n₀ e^{-c' log² n₀} ≠ 0` for the least `n₀ ≥ 2` with `a(n₀) ≠ 0` (dominated tail). Zeros at every height: DBNBohr is already general |
| DBNTheorem4, DBNNewman | DBNSelbergNewman | Theorem 4 for `F`; transfer identical, with `γ_t ≠ 0` from `P(b) ≠ 0` for `Im b` large and `Re J(w) = Re w + (c/2)(log Q + Σ λ_j log‖λ_j(w+M₀)+μ_j‖) → ∞` because `Σ λ_j > 0` |
| — | DBNSelbergZeta | `zetaData : ExtSelbergData` with `a = 1`, `Q = π^{-1/2}`, `r = 1`, `λ = 1/2`, `μ = 0`, `P = X(X−1)/16`, `Ξ = DBN.H 0`; `flow t = DBN.H t` for `t < 0`; `dbn_newman` recovered |

Estimated 2.5–4k lines. Registry: node `RH_dbn_selberg_newman` (campaign rh, draft until the
operator's read-back), statement in `Statements/`, artifact DBNSelbergNewman.lean carrying the
registered statement verbatim; `RH_dbn_newman_of_selberg` for the control.

## 3. What is and is not claimed

Proved for every `ExtSelbergData`: for `t < 0`, `flow t` has a non-real zero. Not proved here:
that a given `S^#` element yields an `ExtSelbergData` (fields 4–5); the Phragmén–Lindelöf input for
that is a separate, later task. Dirichlet `L`-functions and Davenport–Heilbronn are instances of
the class in the literature; instantiating them on the island requires their completed functions
and strip bounds, which Mathlib has in part (`DirichletCharacter.completedLFunction`) and which
are not attempted in this campaign. Newman's conjecture for `S^#` is Dobner's theorem; the
contribution is the formalization. `Λ_F = 0` for any `F` (the generalized RH) is not touched.

## 4. Status (2026-10-10, same day)

Built and kernel-checked on branch `rh/selberg-newman` (full island `lake build`, 8,847 jobs; AxiomGuardDBN
prints `[propext, Classical.choice, Quot.sound]` for every Selberg declaration):

| module | lines | main statements |
|---|---|---|
| DBNSelbergData | 253 | `ExtSelbergData`, `flow`, `Ft`, `Bn`, saddle vocabulary, `gammaF_eq_exp`, `gammaF_add_eq` |
| DBNSelbergGauss | 511 | `shift_line`, `flow_neg_eq_gauss_shift`, `xi_eq_tsum_Bn` (Dobner's (9)) |
| DBNSelbergSaddleAlg | 548 | `BInt_J_eq`, `Bn_J_eq`, `Bn_shift`, `tsum_coef_eq_Ft`, `tsum_Bn_J_eq` |
| DBNSelbergSaddleBounds | 879 | `P_eval_ne_zero`, `norm_KF_sub_one_le`, `norm_KF_le`, `norm_KF_sub_one_le_unified` |
| DBNSelbergFtZero | 377 | `lseriesSummable_Ft`, `hasFiniteOrder_Ft`, `exists_zero_Ft`, `exists_zero_im_ge_Ft` |
| DBNSelbergSaddleSum | 549 | `norm_EF_le`, `norm_term_le_weights`, `error_sum_small` |
| DBNSelbergNewman | 401 | `differentiable_flow`, `theorem4_of`, `selberg_newman_of`, `selberg_newman`, `dbn_newman_of_selberg` |
| DBNSelbergZeta | 127 | `zetaData`, `zetaData_flow_eq`, `dbn_newman_of_zetaData_newman` |

Two places where the general data forced a different estimate than the ζ template (recorded in
DBNSelbergSaddleBounds): the near-field log split works at ratio 2/3 rather than 1/2 because `Im μ_j` may be
nonzero, and the global bound carries a `½ log(‖w‖/‖w+v‖)` term because `Re(w+v) − ½` can be negative when
`λ_j < 1/4`; both are absorbed into the constants `CN`, `CG`, `Y₀`. `differentiable_flow` (the Gaussian
convolution of an entire function bounded on strips is entire) is the one analytic lemma that was free for ζ
(`DBN.differentiable_H`) and had to be proved here by differentiation under the integral with a Cauchy estimate.

Registry: draft node `RH_dbn_selberg_newman` (statement `selberg_newman (F : DBNSelberg.ExtSelbergData) :
∀ t : ℝ, t < 0 → ∃ z : ℂ, F.flow t z = 0 ∧ z.im ≠ 0`, carried verbatim by the artifact DBNSelbergNewman.lean;
RHDefs mirrors `gaussKer`, `ExtSelbergData`, `flow`), artifact linked, `mission verify rh` OK, judge bundle
unchanged (drafts are not judged). The grant waits for the operator's independent read-back, as for
`RH_dbn_newman`. The ζ control `dbn_newman_of_selberg` is a kernel-checked second proof of `dbn_newman`.

## 5. Closing the honest gap: `S^#` itself (started 2026-10-10, same branch)

Section 1 took the entire continuation and the strip bound as fields of `ExtSelbergData`. The next layer
states the class as Kaczorowski–Perelli do and DERIVES those two fields:

* `DBNSelbergSharp.lean`: `structure SelbergSharp` with the Dirichlet series (`a`, `summable` on `Re s > 1`,
  `a 1 = 1`, not a single term), the meromorphic continuation `F : ℂ → ℂ` with `(s-1)^m F` entire and
  `F = LSeries a` on `Re s > 1`, Gamma data `Q, λ_j, μ_j`, root number `|ω| = 1`, the functional equation
  `Φ(s) = ω conj Φ(1 − conj s)` on the open strip `0 < Re s < 1` (where both sides are holomorphic; by the
  identity theorem this is the identity of meromorphic functions), and finite order of `ξ_F = (s(s−1))^m Φ`
  on the right half-plane `Re s ≥ 1/2` (the class's "`(s−1)^m F` of finite order" combined with Stirling for
  the Gamma factors; the island takes the combination as the axiom — the one remaining simplification).
  Defines `Phi`, `xiRight`, `xiLeft` (the reflected expression) and the glued `xi`.
* `DBNSelbergSharpXi.lean`: `xi` is entire (the two expressions agree on the strip by the functional
  equation; holomorphic on `Re s > 0` and on `Re s < 1`), satisfies the functional equation everywhere, has
  finite order everywhere (left half-plane by reflection), and equals the Gamma-weighted Dirichlet series on
  `Re s > 1`.
* `DBNGammaVertical.lean`: `‖Γ(σ+iτ)‖ ≤ C (1+|τ|)^{σ₁} e^{−π|τ|/2}` on `σ₀ ≤ σ ≤ σ₁`, `σ₀ > 0`, from
  `DBNStirling` (`Re L(w) ≤ (σ−½) log‖w‖ − τ arg w − σ + …` with `arg w ≥ π/2 − σ/τ`).
* `DBNSelbergSharpStrip.lean`: `xi` is bounded on every vertical strip. On `Re s = 2` the Dirichlet series is
  bounded and the Gamma product decays like `e^{−(π/2)(∑λ_j)|τ|}`, beating `(s(s−1))^m`; on `Re s = −1` by
  the functional equation; between them by Phragmén–Lindelöf (`PhragmenLindelof.vertical_strip`, growth
  `exp(B exp(c|τ|))` from finite order); outside `[−1, 2]` directly / by reflection. Then
  `toExtSelbergData : SelbergSharp → ExtSelbergData` (with `Ξ z := xi (1/2 + iz/2)`) and
  `selberg_newman_sharp (S : SelbergSharp) : ∀ t < 0, ∃ z, S.toExtSelbergData.flow t z = 0 ∧ z.im ≠ 0`.

Instances: ζ as a `SelbergSharp` (Mathlib's `completedRiemannZeta`, `completedRiemannZeta_one_sub`,
`differentiable_completedZeta₀`; finite order from LiCriterion's `riemannXi` bounds) is the natural control and
is deferred; Dirichlet `L` (`DirichletCharacter.completedLFunction`, `completedLFunction_one_sub` for primitive
characters) needs a finite-order bound Mathlib does not have.

### 5.1 Status (2026-10-10, later the same day): the `S^#` layer is proved

Full island `lake build` 8,859 jobs; AxiomGuardDBN standard for every line.

| module | lines | main statements |
|---|---|---|
| DBNGammaVertical | 192 | `DBNStirling.norm_Gamma_le_vertical`: `‖Γ(σ+iτ)‖ ≤ C (1+|τ|)^{σ₁} e^{−π|τ|/2}` on `σ₀ ≤ σ ≤ σ₁` |
| DBNSelbergSharp | 139 | `SelbergSharp`, `G` (the chosen entire extension of `(s−1)^m F`), `xiRight`, `xiLeft`, `xi`, `sharpFlow`, `P` |
| DBNSelbergSharpXi | 259 | `differentiable_xi`, `xi_functional_equation`, `xi_eq_tsum'`, `hasFiniteOrder_xi` |
| DBNSelbergSharpStrip | 369 | `exists_bound_xi_vertical`, `toExtSelbergData`, `selberg_newman_sharp_ext`, **`selberg_newman_sharp`** |
| DBNSelbergSharpZeta | 348 | `conj_completedRiemannZeta`, `differentiable_zetaG`, `zetaSharp : SelbergSharp` (m = 1), `zetaSharp_xi_eq_H_all : zetaSharp.xi s = 16 H₀(−i(2s−1))`, `zetaSharp_sharpFlow_eq : zetaSharp.sharpFlow t = 16 H_t`, **`dbn_newman_of_sharp`** |

```lean
theorem selberg_newman_sharp (S : DBNSelberg.SelbergSharp) :
    ∀ t : ℝ, t < 0 → ∃ z : ℂ, S.sharpFlow t z = 0 ∧ z.im ≠ 0
theorem dbn_newman_of_sharp : ∀ t : ℝ, t < 0 → ∃ z : ℂ, DBN.H t z = 0 ∧ z.im ≠ 0
```

Two corrections the formalization forced on the textbook statement. (i) The pole axiom is an EXTENSION,
`∃ G entire, ∀ s ≠ 1, G s = (s−1)^m F s`, not `Differentiable (fun s ↦ (s−1)^m F s)`: Mathlib's `riemannZeta 1`
is a junk value, so the latter is literally false for ζ with `m = 1` (the product is `0` at `1`, the limit is `1`);
`ξ_F` is defined through the chosen `G`, and for ζ the chosen `G` takes the residue value `1` at `s = 1`.
(ii) The identity `ξ_ζ = 16 H₀` holds for `xiRight` only on `Re s > 0`: on the left half-plane `Gammaℝ` vanishes
at the trivial zeros and kills `xiRight` while `s(s−1)Λ(s)` does not vanish; the glued `xi` (reflected on
`Re s < 1/2`) equals `16 H₀` everywhere, by the conjugation symmetry of `H₀` (`H_conj`, from the real
integrand), and that is what `dbn_newman_of_sharp` uses. The one remaining simplification against the textbook
definition is that finite order is assumed for `(s(s−1))^m Φ` on `Re s ≥ 1/2` rather than for `(s−1)^m F` alone
(the two are equivalent by Stirling; not proved here).

Registry: draft node `RH_dbn_selberg_newman_sharp` (depends on `RH_dbn_selberg_newman`), statement in
`Statements/RH_dbn_selberg_newman_sharp.lean`, artifact DBNSelbergSharpStrip.lean carrying it verbatim, RHDefs
mirroring `SelbergSharp`, `G`, `xiRight`, `xiLeft`, `xi`, `sharpFlow`; `mission verify rh` OK. Both Selberg nodes wait
for the operator's read-back. Dirichlet `L` as a `SelbergSharp` instance remains undone (needs the conjugation
symmetry of the completed `L` for a real character or the general `L(χ̄)` form, and a finite-order bound).
