# RH programme after `0 ≤ Λ ≤ 9/32` (agreed 2026-10-10)

Standing rules (unchanged): no numerical chase of `Λ`; no new equivalences (Weil / Li / NB / dbn are
coordinate changes, see the Mirrormere wall map); nothing here is progress on RH itself, and no
document may say otherwise. `Λ = 0` is RH and is open. conjecture1_proved = False.

State of the registry: `RH_dbn_debruijn_real_zeros` (`Λ ≤ 1/2`), `RH_dbn_real_zeros_nine_thirtyseconds`
(`Λ ≤ 9/32`, cross-pin at OpenAI's environment) and `RH_dbn_newman` (`Λ ≥ 0`, after Dobner) are
proved, operator-read-back, Comparator-judged (nanoda) and recorded. The four items below were
agreed by the operator on 2026-10-10 in this order.

## 1. Publish the lower half (`Λ ≥ 0`)

Deliverable: a public repository with a paper, the Lean sources, a self-contained reproduction
script, logs, and provenance, released on Zenodo (new concept DOI; the 9/32 release stays
separate and is cross-linked), formatted for arXiv.

* Paper (15–25 pp, CC-BY-4.0, sole author P. W. Murphy, AI assistance acknowledged as in the 9/32
  paper): the statement in the island's vocabulary; Dobner's route and where the formalization
  departs from it (base point `b = s + M₀`, contours in `Re v ≥ 2`, one pointwise bound, no rate);
  the nine modules and their main theorems; the verification trail (gate 2026-09-23.1, operator
  read-back, Comparator run 38062595826 job 114244014550 and the main run 38070548082 dbn shard,
  nanoda); the combined picture `0 ≤ Λ ≤ 9/32`; limitations.
* Reproduction: `scripts/materialize.sh` checks out DrMurphyIsIn/Arda at the release tag and builds
  the dbn island (`lake build`, `AxiomGuardDBN`), then runs Comparator locally on
  `MissionJudge.RH_dbn_newman` as the 9/32 release did.
* Zenodo: the operator supplies a one-time token at publish time; it lives only in the scratchpad,
  is used once, is deleted, and the operator revokes it afterwards.
* Arda back-links (README, STATUS, PROOF_STATUS, explorer entry) once the DOI exists.

## 2. Upstream the reusable analysis to Mathlib

Candidates, all already Mathlib-only on the island (pin de5ce8a9), to be rebased on current Mathlib
master and renamed to Mathlib conventions:

| Island source | Proposed Mathlib home | Content |
|---|---|---|
| `DBNStirling` | `Analysis/SpecialFunctions/Gamma/Stirling.lean` (complex) | `Γ z = exp L z` with explicit remainder on `Re z > 0`; `digamma` asymptotic; second-order Euler–Maclaurin cell lemma for `Log (z + x)` |
| `DBNBohr` | `NumberTheory/LSeries/AlmostPeriodic.lean` | integer vertical shifts along which an everywhere absolutely convergent `LSeries` converges to itself locally uniformly |
| `DBNGaussConv.norm_Gamma_le_Gamma_re` | `Gamma/Basic.lean` | `‖Γ v‖ ≤ Γ (Re v)` (check master first; may exist) |
| `DBNSaddleBounds.norm_exp_sub_one_le_mul_exp` | `Analysis/Complex/Exponential.lean` | `‖exp Q − 1‖ ≤ ‖Q‖ exp ‖Q‖` |
| `DBNSaddleBounds.log_half_add_eq` (generalised) | `Analysis/SpecialFunctions/Complex/Log.lean` | `log (a·b) = log a + log b` when both arguments lie in the open upper half-plane and `‖b/a − 1‖`-type control, via `exp_eq_exp_iff_exists_int` |
| `DBNSaddleSum.integrable_gauss_poly` | `Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean` | `(1+|x|)^k exp(−b x² + a|x|)` integrable with the explicit bound |

Process: one Mathlib fork branch per item; the operator posts on Zulip (house rule: no LLM-written
Zulip text) and decides who opens each PR; reviewer requests are iterated here. Stopping rule: an
item is dropped if master already has it or a reviewer prefers a different formulation that would
mean rewriting the island.

## 3. Newman's conjecture for the extended Selberg class (Dobner's theorem as stated)

On the dbn island, following arXiv:2005.05142 sections 2–3 in full generality: a structure
`ExtSelberg` carrying the Dirichlet coefficients `a : ℕ → ℂ` with `‖a n‖ ≤ C n^2` (Dobner's growth),
the Gamma data `Q > 0`, `ω i > 0`, `μ i` with `Re μ i ≥ 0`, and the functional equation in the
`ξ^F` form; `Φ^F`, `H_t^F`, and the theorem `∀ t < 0, ∃ z, H_t^F z = 0 ∧ z.im ≠ 0`.

New work relative to the ζ instance: the Dirichlet-series layer for general coefficients (steps 1–2
already take arbitrary coefficients, step 4's expansion needs the general `Φ^F` series and its
termwise Mellin evaluation against `∏ Γ(ω_i s + μ_i)`), the Stirling sum over the Gamma factors
(`DBNStirling` applies factor by factor; `ℓ(s) = ½ ∑ ω_i Log(ω_i s)` + constants), and the saddle
bookkeeping with `h_n = (c/2) log n` replaced by Dobner's `J_t` with `log Q`. Estimate 2–4k lines.
Controls: `ζ` recovers `dbn_newman`; Dirichlet `L(s, χ)` for primitive `χ` as a positive control;
the Davenport–Heilbronn function is in the class (no Euler product needed) and is a second positive
control; a negative control is a series violating the growth or functional-equation hypotheses.
Registry: one node per layer in the rh campaign, judged one at a time.

## 4. Effective Theorem 4 (bounded exploration)

Question: with the remainders now explicit, make `DBNSaddleSum.error_sum_small` quantitative —
`‖∑ a_n n^{-s} E_n(s)‖ ≤ C₁(c, x₀)/y + C₂ e^{-y²/32c + πy}` is already in the proof; extract the
constants, add a quantitative Bohr step (density of the shifts, Bohr's `lim inf (τ_{m+1} − τ_m) > 0`
and `lim sup τ_m/m < ∞`, Dobner's Theorem 5 in full), and conclude explicit statements of the form
"for `t < 0` and every `T ≥ T₀(t)` there are `≥ κ(t) T` zeros of `H_t` with `|Im z| ≥ δ(t, T)` and
`|Re z| ≤ T`". Rodgers–Tao's dynamics say these zeros reach the real axis exactly at `t = 0` if RH
holds; an effective picture of that approach from below is the exploration.

Stopping rule: at most three weeks of session time or 3k lines; stop immediately if the effective
statement reduces to inputs already in Rodgers–Tao (pair correlation, the ODE energy bounds) without
new information, or if the only quantitative content is a restatement of `Λ ≥ 0`. Outcome is a
written note either way; no registry node unless a theorem is proved.

## Order and gating

1 → 2 → 3 → 4. Item 1 is blocked only on the operator's Zenodo token at publish time. Item 2 is
blocked on the operator's Zulip posts and PR decisions. Items 3 and 4 are internal and can start
once 1's paper is drafted.
