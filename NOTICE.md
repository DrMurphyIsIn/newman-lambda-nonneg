# Notice and provenance

- **The result.** For every real `t < 0` the de Bruijn–Newman function `H_t` has a zero off the real axis
  (`dbn_newman : ∀ t : ℝ, t < 0 → ∃ z : ℂ, DBN.H t z = 0 ∧ z.im ≠ 0`). Classically this is Newman's conjecture
  `Λ ≥ 0`, proved by Rodgers and Tao in 2018; the proof formalized here follows Dobner (2020). Together with the
  Arda registry's `Λ ≤ 1/2` (de Bruijn) and `Λ ≤ 9/32` (from OpenAI's quasi-Riemann hypothesis) the
  kernel-checked range is `0 ≤ Λ ≤ 9/32`. `Λ = 0` is the Riemann Hypothesis and is not proved.
- **Mathematics.** Newman's conjecture is Rodgers and Tao's theorem (Forum Math. Pi 8 (2020), e6). The route
  formalized is Alexander Dobner's, "A proof of Newman's conjecture for the extended Selberg class",
  arXiv:2005.05142. The ζ instance is formalized; the extended Selberg class is not (yet).
- **Arda.** The ten modules in `lean/dbn/` were written on the Arda dbn island
  (<https://github.com/DrMurphyIsIn/Arda>, tag `newman-v1.0.0`, commit `ddf2ecff0`) and are copied here
  byte-identically. The island's other 46 modules (the heat-flow family, de Bruijn's theorem, the Hadamard
  machinery, Hurwitz) are built from the Arda checkout by `scripts/materialize.sh`.
- **Lean and Mathlib.** Lean 4 `v4.34.0-rc1`, Mathlib `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`,
  LiCriterion `35df682f` (Apache-2.0; supplies `Hadamard.entire_no_zeros_is_exp_polynomial`).
- **Verification.** Lean's kernel (`#print axioms`: `[propext, Classical.choice, Quot.sound]`); the Arda
  missions registry's gate (version 2026-09-23.1); an independent operator read-back of the formal statement;
  the `missions-comparator` job, which builds a challenge whose TYPE is the registered statement and whose
  proof is the artifact constant, exports it, checks the axiom whitelist and replays it through Lean's kernel
  and nanoda (runs 38062595826 and 38070548082; `logs/`); the `[comparator]` record on the node (`provenance/`).
- **Machine assistance.** The formalization, the tooling, the audit trail and the paper were produced with
  extensive use of an AI coding assistant (Claude, Anthropic) under the direction of the author. The Lean
  kernel is the sole trusted component: every claim is either a kernel-checked theorem or labelled otherwise.
