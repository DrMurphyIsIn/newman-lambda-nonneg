# Λ ≥ 0, kernel-checked

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23287832.svg)](https://doi.org/10.5281/zenodo.23287832)

The de Bruijn–Newman constant Λ is a single real number that encodes the Riemann Hypothesis.
Take the Riemann ξ function, write it as a Fourier transform, and let that transform evolve
under the backward heat equation for time t. For each t you get an entire function H_t, and
H_0 is ξ in disguise. De Bruijn showed in 1950 that once the zeros of H_t are all real they stay
real as t grows, so there is a threshold Λ: the zeros of H_t are all real exactly when t ≥ Λ.
The Riemann Hypothesis is the statement that the zeros of H_0 are real, that is, Λ ≤ 0.

Newman conjectured in 1976 that Λ ≥ 0: if the Riemann Hypothesis is true, it is only barely
so, and the zeros of H_t for t < 0 leave the real axis. Lower bounds crept up to zero from below
over three decades of Lehmer-pair computations, and in 2018 Rodgers and Tao proved the
conjecture by following the zeros along the heat flow and contradicting the pair-correlation
estimates for the zeros of ζ. In 2020 Dobner gave a second proof, for the extended Selberg
class, which uses no information about the zeros of ζ at all: it exhibits zeros of H_t off the
axis directly, by approximating ξ_t at great height with an everywhere-convergent Dirichlet
series whose zeros are forced by Hadamard's theorem and spread to every height by Bohr's
almost periodicity.

This repository records a formalization of that proof in Lean 4, on the Arda project's dbn island:

> **For every t < 0, H_t has a zero off the real axis.** Classically, Λ ≥ 0.

```lean
theorem dbn_newman :
    ∀ t : ℝ, t < 0 → ∃ z : ℂ, DBN.H t z = 0 ∧ z.im ≠ 0
-- 'dbn_newman' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Together with the island's kernel-checked Λ ≤ 1/2 (de Bruijn) and Λ ≤ 9/32 (from OpenAI's
zero-free half-plane Re s > 7/8, see
[qrh-debruijn-newman](https://github.com/DrMurphyIsIn/qrh-debruijn-newman)), the machine-checked
picture of the constant is now **0 ≤ Λ ≤ 9/32**. Λ = 0 is the Riemann Hypothesis and is not proved.
Nothing here is progress on it. The theorem is Rodgers and Tao's, the proof is Dobner's, and the
contribution is the formalization and its verification record.

## How the proof goes, and where the formalization departs from it

Fix t < 0 and write c = −t. Dobner's argument has six steps, and the Lean development has one
module group per step.

1. **A contour representation.** ξ_t is a Gaussian convolution of ξ along a vertical line. The
   island already knew how to expand H_0 termwise in a Gamma series for Im z < −1 (that was the
   zero-strip work of September), so instead of going through ξ = γζ and a contour of ξ we write
   H_{−c} as a Gaussian average of H_0 along the real line, move the line by Cauchy into the region
   where the termwise expansion holds, and expand there. Dobner's equation (9) comes out with no
   ζ, no ξ and no Dirichlet series of ζ anywhere (`DBNGaussConv`).
2. **Theorem 4, the saddle point.** After the nonlinear shift J(s) = s + (c/4) Log(s/2π), each
   term of the series is, to leading order, a Gamma-type factor times e^{−(c/4) log² n} n^{−s}.
   The paper proof expands around a saddle that moves with n and handles the poles of the Gamma
   factor by a remark on their height. We fix a base point b = s + M₀ with 2 ≤ Re b ≤ 4 instead, so
   every contour lives in Re v ≥ 2 and Stirling's formula applies to every Gamma value that
   occurs; the shift is absorbed exactly into the Gaussian algebra. One pointwise bound, with the
   Gaussian factor e^{((h+|σ|)²−y²/4)/8c} ≥ 1 playing the role of an indicator of the far region,
   covers every term and every point of every contour. No case split in n, no rate, no restriction
   on the strip (`DBNSaddleAlg`, `DBNSaddleBounds`, `DBNSaddleSum`, `DBNTheorem4`).
3. **The Dirichlet series has a zero.** F(s) = Σ e^{−(c/4) log² n} n^{−s} converges everywhere and
   has finite order. If it were zero-free it would be e^g for a polynomial g (Hadamard, from the
   LiCriterion library), so F' = F g'; but F ≥ 1 and F' → 0 along the real axis, so g' is the zero
   polynomial, and F'(0) ≠ 0 says otherwise (`DBNFtZero`).
4. **Bohr.** The vertical shifts F(s + iτ) converge to F locally uniformly along some τ → ∞. The
   usual proof is Kronecker-style Diophantine approximation; we use sequential compactness of the
   twist vectors (n^{−ki})_{n ≤ N} in ℂ^N and a diagonal argument, which is shorter and needs no
   Diophantine theorem (`DBNBohr`, `DBNFtZeroHigh`).
5. **Transfer.** Rouché is not in Mathlib, but the island has Hurwitz in zero-free form: if
   holomorphic zero-free functions converge locally uniformly to a non-trivial limit, the limit is
   zero-free too. Both uses of Rouché in the paper are the contrapositive of that. So ξ_t ∘ J has a
   zero near the shifted zero of F, and its real part Re w + (c/4) log(‖w + M₀‖/2π) is far from
   1/2 once the height is large (`DBNNewman`).
6. **Conclusion.** `dbn_newman`.

The departures are why the development is 3,900 lines rather than the 8–15 thousand first
estimated. Along the way the island acquired infrastructure Mathlib does not have: Stirling's
formula for the complex Gamma function on Re z > 0 with the explicit remainder ‖R(z)‖ ≤ 1/(4‖z‖),
the digamma asymptotic ψ(z) = Log z − 1/(2z) + O(‖z‖^{−2}), Bohr almost periodicity for
everywhere-convergent Dirichlet series, ‖Γ(v)‖ ≤ Γ(Re v), and ‖e^Q − 1‖ ≤ ‖Q‖e^{‖Q‖} without a
size restriction (`DBNStirling` and friends). Those are written to be upstreamed.

## Version 1.1: Dobner's theorem in full

Dobner proved Newman's conjecture for the whole extended Selberg class, and every step above except
the Dirichlet-series layer was already general. Version 1.1.0 carries that generalization, in two
layers, both kernel-checked under the same three axioms and both judged by the registry's Comparator
job (runs 38093443787 and 38108898132, second kernel nanoda; transcripts in `logs/`).

The first layer isolates what the proof consumes. `DBNSelberg.ExtSelbergData` is a structure holding
Dirichlet coefficients absolutely convergent on Re s > 1 with a(1) = 1 and a second nonzero term, the
Gamma data P(v) Q^v ∏ Γ(λ_j v + μ_j) with λ_j > 0, Re μ_j ≥ 0 and positive degree, and a completed
function Ξ that is entire, equals the Gamma-weighted Dirichlet series on Re s > 1, and is bounded on
horizontal strips. The heat flow for t < 0 is the Gaussian convolution the island already proved H_t to be.

> **`selberg_newman`: for every `F : ExtSelbergData` and every t < 0, `F.flow t` has a non-real zero.**

The second layer states the class itself. `DBNSelberg.SelbergSharp` has a meromorphic continuation
F with (s−1)^m F extending to an entire function, the Gamma data, a root number, the functional
equation Φ(s) = ω·conj Φ(1 − conj s) on the critical strip, and finite order of (s(s−1))^m Φ on the
right half-plane. Its completed function is glued from the right-half-plane expression and its
reflection, proved entire (the two agree on the strip by the functional equation), of finite order,
and bounded on every vertical strip: Gamma decays like e^{−(π/2)(Σλ_j)|τ|} on vertical lines, which
the island's Stirling formula now delivers, and Phragmén–Lindelöf fills in the strip between
Re s = −1 and Re s = 2.

> **`selberg_newman_sharp`: for every `S : SelbergSharp` and every t < 0, the heat flow of ξ_S has a non-real zero.**

ζ is an honest instance of the class (`zetaSharp`, pole order 1, the conjugation symmetry of Λ from
Riemann's symmetric integral, finite order from LiCriterion's ξ bound), its heat flow is exactly
16·H_t, and `dbn_newman_of_sharp` recovers the ζ theorem from the class theorem. Two things the
formalization corrected in the textbook statement are recorded in the paper and the design note:
the pole axiom has to be an extension because Mathlib's ζ carries a junk value at s = 1, and the
identification ξ_ζ = 16·H₀ holds for the right-half-plane expression only on Re s > 0. The one
remaining simplification is that finite order is assumed for (s(s−1))^m Φ rather than for (s−1)^m F
alone. Dirichlet L-functions are not instantiated. Thirteen modules, about 4,950 lines; design and
module map in `docs/SELBERG_NEWMAN_DESIGN_2026-10-10.md`.

## What was checked, and by what

- **The kernel.** Every theorem is checked by Lean's kernel. The island's axiom guard re-elaborates
  all 56 modules and prints the axioms of 687 named theorems; every line reads
  `[propext, Classical.choice, Quot.sound]`. The only dependency beyond Mathlib is the pinned
  LiCriterion library, for Hadamard's exp-polynomial theorem.
- **A registered statement and an independent read-back.** The theorem is node `RH_dbn_newman` in
  Arda's missions registry. Its statement lives in a separate package (`lean/statements/`), and
  the registry refuses to promote a node on the authoring session's word: the operator read the
  formal statement back under his own identity and session before the gate would run. The gate
  then required the artifact to contain the registered statement verbatim, rebuilt the island,
  checked the axiom closure, and hashed artifact and statement (`provenance/registry/`).
- **A second kernel.** The registry's judge generates a challenge whose *type* is the registered
  statement and whose *proof* is `dbn_newman`; it elaborates only if the artifact proves exactly
  the registered proposition. CI runs openai/ten-proofs Comparator on it, replaying through Lean's
  kernel and through nanoda. It passed on the pull-request head (run 38062595826) and again on
  the merge commit on main (run 38070548082); transcripts in `logs/`, verdict line:

  ```
  COMPARATOR PASS island=dbn node=RH_dbn_newman theorem=dbn_newman run=38062595826 kernel=nanoda
  ```

- **Continuous integration here.** `verify.yml` materializes Arda at the recorded tag, checks the
  vendored files byte for byte, builds the island, greps the axioms of `dbn_newman`, and builds
  the judge challenge, on every push.

Trusted as code rather than checked: Lean 4 v4.34.0-rc1, Mathlib `de5ce8a9` and LiCriterion
`35df682f` as the source of the definitions (Gamma, LSeries, the Bochner integral), nanoda, and
the island's transcription of the Polymath15 formula for H_t. The read-back is the human check that
the registered statement says what this README says it says.

## What this does and does not advance

Newman's conjecture was a theorem before this work. The known range of Λ was [0, 1/2] before and
after, and the kernel-checked upper bound 9/32 did not change it either. What is new is that both
halves of 0 ≤ Λ ≤ 9/32 now rest on the same kind of evidence: a proof term under three standard
axioms, a registered statement read back by a person, and a replay by two kernels. The two halves
live in two Lean environments (this one at Mathlib `de5ce8a9`, the upper bound at OpenAI's
`d13f23b`); porting this development to OpenAI's pin, as was done for de Bruijn's theorem, would
put the whole range in one environment.

Two doors it opens, with no promise attached. Dobner's theorem for the whole class is now in the kernel
(version 1.1), so any future zero-free strip for any element of the class converts into a certified
statement about its heat flow in a day. And the remainder
bounds in `DBNSaddleSum` are explicit, so Theorem 4 can be made quantitative: how far off the axis
the zeros of H_t sit as t → 0⁻ is a question the dynamics of Rodgers and Tao speak to and no
kernel has yet.

## The paper

`paper/paper.pdf`, CC-BY-4.0 (15 pages in v1.1.0); archived with this repository at Zenodo, DOI
[10.5281/zenodo.23287833](https://doi.org/10.5281/zenodo.23287833) for v1.0.0 (v1.1.0 to follow) and
[10.5281/zenodo.23287832](https://doi.org/10.5281/zenodo.23287832) for all versions. It states the theorem
as formalized, walks Dobner's six steps and the three departures, gives the module map with the
headline statements in Lean, lays out the verification chain, and says plainly what is and is not
established.

The arXiv source package is `paper/arxiv.tar.gz` and the submission metadata is in `paper/ARXIV.md`;
the arXiv identifier will be added here once assigned.

## Reproducing it

You need Lean 4 (elan), about 20 GB of disk, and a few CPU-hours the first time.

```sh
scripts/materialize.sh                       # Arda at tag newman-v1.0.0, vendored copies checked
cd work/arda/telperion/examples/dbn/lean
lake exe cache get && lake build             # 56 modules, 8,829 jobs cold
lake env lean AxiomGuardDBN.lean | grep -E 'dbn_newman|selberg_newman'
cd ../../../missions/judge/dbn && lake build MissionChallenges.RH_dbn_newman MissionChallenges.RH_dbn_selberg_newman MissionChallenges.RH_dbn_selberg_newman_sharp
```

For the second kernel, build [leanprover/comparator](https://github.com/leanprover/comparator) at
tag v4.34.0 with its `lean-toolchain` set to v4.34.0-rc1, build
[nanoda](https://github.com/ammkrn/nanoda_lib), and run
`lake env comparator RH_dbn_newman.comparator.json` in the judge directory. It must accept.
`provenance/arda-missions-comparator.yml` is the exact CI recipe.

## Layout

```
lean/dbn/           the ten Newman modules, the thirteen Selberg-class modules, DBNTheorem4Effective, AxiomGuardDBN,
                    lakefile, toolchain, manifest (byte-identical to Arda at tag newman-v1.1.0)
lean/judge/         the registry judge bundle for the dbn island: challenges whose TYPE is the registered statement
lean/statements/    the registered statement package (RH_dbn_newman, RH_dbn_selberg_newman, RH_dbn_selberg_newman_sharp, RHDefs)
provenance/         registry node records (Newman, both Selberg nodes, de Bruijn, 9/32), the Arda source tag, the CI workflow
logs/               the four Comparator CI transcripts (v1.0.0 and v1.1.0, pull-request head and main)
docs/               the scoping document, the programme note, the Selberg design note, the effective Theorem 4 note,
                    the Mathlib upstreaming report
scripts/            materialize.sh
paper/              the paper, the arXiv sheet, make_arxiv.sh
```

## Credit

The theorem is Rodgers and Tao's and the proof is Dobner's. The dbn island's heat-flow family,
de Bruijn's theorem, Hadamard and Hurwitz machinery were formalized by the Arda project in
September 2026; Hadamard's exp-polynomial theorem is from Nicholas Bulka's LiCriterion library.
The formalization, the registry tooling and the paper were produced with extensive use of an AI
coding assistant (Claude, Anthropic) under the direction of the author; see `NOTICE.md`. Licensing
in `LICENSING.md`. Not yet refereed.
