/-
  Statements.RHDefs -- vocabulary mirror for the RH missions registry.  NOT a node statement.

  Every definition below is a VERBATIM copy: the ZeroFreeBridge/DiffractionCore/Backlund
  blocks by exact line range from the v4.34 li_positivity island (toolchain
  leanprover/lean4:v4.34.0-rc1) and the DBN block from the v4.34 examples/dbn island
  (Route C, same pin), source module cited above each extract; the LiCriterion block from
  the upstream pinned dependency nicholasbulka/li-criterion-rh-equivalence-lean @ 35df682f,
  Lc/LiCriterion/Basic.lean, lines cited.  The copies are regenerated/diffed by
  missions/rh/build_rhdefs.py (--verify-upstream re-fetches and diffs the upstream block).
  This file exists so that node statement files elaborate standalone against Mathlib; the
  *registry statements* are the node files, which the verify gate matches against the real
  island artifacts by normalized containment.  conjecture1_proved = False.
-/
import Mathlib
open MeasureTheory

namespace LiCriterion

-- ===== upstream Lc/LiCriterion/Basic.lean:379 (rev 35df682f) =====
noncomputable def phi (f : ℂ → ℂ) (z : ℂ) : ℂ := f (1 / (1 - z))

-- ===== upstream Lc/LiCriterion/Basic.lean:525-526 (rev 35df682f) =====
noncomputable def taylorCoeff (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  (deriv^[n] (logDeriv (phi f))) 0 / n.factorial

-- ===== upstream Lc/LiCriterion/Basic.lean:1236-1237 (rev 35df682f) =====
noncomputable def riemannXi (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + (1 / 2 : ℂ)

end LiCriterion

namespace ZeroFreeBridge

-- ===== StripRepr.lean:42,45-46,49,52 (v4.34 island) =====
noncomputable def fractIntegrand (s : ℂ) (x : ℝ) : ℂ := ((Int.fract x : ℝ) : ℂ) / (x : ℂ) ^ (s + 1)

noncomputable def fractIntegral (s : ℂ) : ℂ :=
  ∫ x in Set.Ioi (1 : ℝ), fractIntegrand s x

noncomputable def stripRHS (s : ℂ) : ℂ := s / (s - 1) - s * fractIntegral s

def stripDomain : Set ℂ := {s : ℂ | 0 < s.re} \ {1}

-- ===== DlvpZetaRateEffective.lean:23-25,28 (v4.34 island) =====
noncomputable def dlvpRateK : ℝ :=
  1 + 2 * ((8 / (3 * Real.log ((23/16) / (11/8))) + 608/9) / 16)
        * (Real.log (15 / (2 - Real.pi ^ 2 / 6)) + 1)

noncomputable def dlvpRateC : ℝ := 1 / (112 * 16 * dlvpRateK)

end ZeroFreeBridge

namespace DiffractionCore
open Real Complex

-- ===== RvMDiffractionCore.lean:916-917,921-922 (v4.34 island) =====
noncomputable def argChangeVert (f : ℂ → ℂ) (σ T0 T1 : ℝ) : ℝ :=
  (∫ y in T0..T1, logDeriv f ((σ : ℂ) + y * I)).re

noncomputable def argChangeHoriz (f : ℂ → ℂ) (T x0 x1 : ℝ) : ℝ :=
  (∫ x in x0..x1, logDeriv f ((x : ℂ) + T * I)).im

-- ===== RvMDiffractionCore.lean:1001-1002 (v4.34 island) =====
noncomputable def riemannS (T : ℝ) : ℝ :=
  (argChangeVert riemannZeta 2 0 T + argChangeHoriz riemannZeta T 2 (1/2)) / π

-- ===== RvMDiffractionCore.lean:1691-1692 (v4.34 island) =====
noncomputable def zetaPoleCompanion : ℂ → ℂ :=
  Function.update (fun z : ℂ => (z - 1) * riemannZeta z) 1 1

end DiffractionCore

namespace Backlund
open Complex

-- ===== RvMBacklundAux.lean:24-25 (v4.34 island) =====
noncomputable def backlundAux (T : ℝ) (z : ℂ) : ℂ :=
  (riemannZeta (z + (T : ℂ) * I) + riemannZeta (z - (T : ℂ) * I)) / 2

end Backlund

namespace RvMCount

-- ===== AUTHORED for the registry (NOT in the island; 2026-09-17 critical-path nodes).  The
-- nontrivial-zero count to height T WITH MULTIPLICITY: a finsum over the strip zeros with
-- 0 < Im <= T of the order given by zeta's meromorphic divisor on the open critical strip.
-- RECTANGLE-based by design: a ball-based count (the island's RHInBoxAnalytic.zeroFinset shape)
-- miscounts conjugates (routes roadmap section 9).  finsum is 0 on infinite support, so the
-- definition is total; finiteness of the support is a theorem, not an assumption. =====
noncomputable def zetaZeroCount (T : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T},
    ((MeromorphicOn.divisor riemannZeta {s : ℂ | 0 < s.re ∧ s.re < 1} : ℂ → ℤ) ρ).toNat

end RvMCount

namespace DBN

-- ===== examples/dbn/lean/DBNDefs.lean:40-41 (v4.34 dbn island, Route C) =====
noncomputable def thetaMoment (k : ℕ) (u : ℝ) : ℝ :=
  ∑' n : ℤ, ((n : ℝ) ^ 2) ^ k * Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (4 * u))

-- ===== examples/dbn/lean/DBNDefs.lean:211-214 (v4.34 dbn island, Route C) =====
noncomputable def Φ (u : ℝ) : ℝ :=
  ∑' n : ℕ+, (2 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u)
      - 3 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u))
    * Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (4 * u))

-- ===== examples/dbn/lean/DBNDefs.lean:408-409 (v4.34 dbn island, Route C) =====
noncomputable def HIntegrand (t : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  ((Real.exp (t * u ^ 2) : ℝ) : ℂ) * ((Φ u : ℝ) : ℂ) * Complex.cos (z * u)

-- ===== examples/dbn/lean/DBNDefs.lean:413 (v4.34 dbn island, Route C) =====
noncomputable def H (t : ℝ) (z : ℂ) : ℂ := ∫ u in Set.Ioi (0 : ℝ), HIntegrand t z u

end DBN

namespace WeilExplicit
open MeasureTheory Complex

-- ===== AUTHORED for the registry (NOT in the island; 2026-09-18 E8 limit explicit formula,
-- design memo telperion/docs/E8_LIMIT_EXPLICIT_FORMULA_DESIGN_2026-09-18.md).  Vocabulary for
-- RH_limit_explicit_formula: the Weil 1952 / Guinand 1948 identity on the class of smooth
-- compactly supported complex test functions g on the line (Iwaniec-Kowalski Thm 5.12 shape).
-- The test function lives on the PRIME (direct) side; its transform weilKernel g is an ENTIRE
-- function of s defined by one Bochner integral, so its values at off-line zeros are literal
-- (no analytic continuation -- this is what survives the Paley-Wiener obstruction, roadmap D3).
-- Compact support makes the prime side a FINITE sum, so the PNT growth Sum Lambda(n)/sqrt n
-- ~ 2e^{R/2} (roadmap section 1) never enters.  Smoothness index is C^infinity, written
-- ((top : ENat) : WithTop ENat); top alone would mean ANALYTIC and, with compact support on
-- the line, collapse the class to {0}.  No evenness hypothesis: the identity holds for every
-- g in the class (numerically checked with a shifted Gaussian, memo section 4). =====

/-- The E8 test class: smooth, compactly supported g : R -> C. -/
def IsWeilTest (g : ℝ → ℂ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ HasCompactSupport g

/-- H_g(s) = ∫ g(u) e^{(s - 1/2) u} du, the zero-side transform.  With s = 1/2 + i r this is
    h(r) = ∫ g(u) e^{i r u} du (the Iwaniec-Kowalski pair); entire for compactly supported g,
    so H_g(ρ) at a zero ρ = 1/2 + iγ is h(γ) with γ complex when ρ is off the line.
    H_g(0) = h(i/2) and H_g(1) = h(-i/2) are the two pole terms. -/
noncomputable def weilKernel (g : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ u : ℝ, g u * Complex.exp ((s - 1 / 2) * (u : ℂ))

/-- Multiplicity of ρ as a nontrivial zero: the order of ζ at ρ on the open critical strip
    (0 off the strip and at non-zeros).  The SAME divisor expression as
    RvMCount.zetaZeroCount, so the E8 zero side and the RvM count carry identical weights. -/
noncomputable def zeroMult (ρ : ℂ) : ℕ :=
  ((MeromorphicOn.divisor riemannZeta {s : ℂ | 0 < s.re ∧ s.re < 1} : ℂ → ℤ) ρ).toNat

/-- The archimedean integrand h(r) · Re ψ(1/4 + i r/2), ψ = Γ'/Γ = Complex.digamma. -/
noncomputable def archIntegrand (g : ℝ → ℂ) (r : ℝ) : ℂ :=
  weilKernel g (1 / 2 + (r : ℂ) * I) * ((Complex.digamma (1 / 4 + ((r : ℂ) / 2) * I)).re : ℂ)

/-- The archimedean side: h(i/2) + h(-i/2) - g(0) log π + (1/2π) ∫ h(r) Re ψ(1/4 + i r/2) dr. -/
noncomputable def archSide (g : ℝ → ℂ) : ℂ :=
  weilKernel g 0 + weilKernel g 1 - g 0 * (Real.log Real.pi : ℂ)
    + (1 / (2 * (Real.pi : ℂ))) * ∫ r : ℝ, archIntegrand g r

/-- The prime side: Σ_n Λ(n)/√n · (g(log n) + g(-log n)); a finite sum for compactly
    supported g (Λ(0) = Λ(1) = 0; the two terms are the two vertical edges of the finite
    explicit formula rect_explicit_formula in the T → ∞ limit). -/
noncomputable def primeSide (g : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
    * (g (Real.log n) + g (-Real.log n))

end WeilExplicit

-- ===== CROSS-CAMPAIGN VOCABULARY MIRROR (2026-09-21): the two AUTHORED definitions of
-- telperion/missions/mirrormere/lean/Statements/MMDefs.lean (namespace WeilExplicit), VERBATIM
-- with their docstrings, themselves mirrored on the rvm_bridge island in
-- telperion/examples/rvm_bridge/lean/E6Bridge5.lean:55-59.  Vocabulary for RH_weil_criterion_iff,
-- the rh campaign's consumption of MIRRORMERE's zeta_comb_membership_iff_rh (E6Bridge9).  The
-- `WeilForm` namespace below (crossCorr + abbrev autocorr) is the weil_form_enclosure emitter's
-- own vocabulary and is a DIFFERENT name: WeilForm.autocorr vs WeilExplicit.autocorr; both stay.
-- conjecture1_proved = False. =====
namespace WeilExplicit
open MeasureTheory Complex

-- ===== AUTHORED for the MIRRORMERE registry (NOT in any island, NOT in RHDefs): the two
-- definitions the W3c membership goal needs on top of the mirrored E8 vocabulary.  Design
-- memo telperion/docs/MM_w3c_goal_weil_membership_DESIGN_2026-09-18.md.  Flagged for the
-- blind read-back audit cycle.  conjecture1_proved = False. =====

/-- AUTHORED.  The Hermitian autocorrelation `g ⋆ g̃` with `g̃ u = conj (g (-u))`:
    `(g ⋆ g̃) u = ∫ g v * conj (g (v - u)) dv`.  For `g` smooth and compactly supported so is
    `autocorr g` (Mathlib compact-support convolution smoothness), so `archSide`/`primeSide`
    take honest values on it and the membership statement is not a junk-value sentence.
    Its transform factors: `weilKernel (autocorr g) s = weilKernel g s * conj (weilKernel g
    (1 - conj s))`, which on the critical line `s = 1/2 + i r`, `r : ℝ`, is `‖h (r)‖ ^ 2` —
    the Weil-criterion positivity shape.  `autocorr g` is Hermitian-even, NOT even: its
    imaginary part is odd (E8 memo section 3.4), which is why the mirrored class keeps `g`
    complex-valued with no parity hypothesis. -/
noncomputable def autocorr (g : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ v : ℝ, g v * (starRingEnd ℂ) (g (v - u))

/-- AUTHORED.  The Weil functional READ FROM THE PRIMES SIDE: `archSide f - primeSide f`.
    By the kernel-checked E8 limit explicit formula (`RvMBridge4.limit_explicit_formula`,
    rvm_bridge island, node `RH_limit_explicit_formula`) this value is exactly the zero-side
    sum `∑_ρ zeroMult ρ * weilKernel f ρ`, so `weilForm` is the diffraction pairing of the
    regularized triple (zero comb against `h`, prime comb against `g`, archimedean density
    against `h`) with NO temperedness claim about any comb (the naive dual-comb temperedness
    clause is unconditionally false, roadmap section 1). -/
noncomputable def weilForm (f : ℝ → ℂ) : ℂ := archSide f - primeSide f

end WeilExplicit

namespace BombieriLagarias
open Complex

-- ===== AUTHORED for the registry (NOT in the island; 2026-09-18 B7, the Bombieri-Lagarias
-- explicit formula on Li's test class, design memo
-- telperion/docs/B7_BL_EXPLICIT_FORMULA_DESIGN_2026-09-18.md).  Vocabulary for
-- RH_bl_explicit_formula.  Zero side: Li's kernel 1 - (1 - 1/rho)^n (Li 1997, eq. (1.2);
-- Bombieri-Lagarias 1999, eq. (1.1)) weighted by the E8 / RvMCount divisor multiplicity, summed
-- over the SYMMETRIC windows |Im rho| <= T.  The family rho |-> m(rho) (1 - (1 - 1/rho)^n) is NOT
-- summable in C (its terms are ~ n/(i gamma) and sum 1/gamma diverges since N(T) ~ (T/2pi) log T),
-- so a HasSum statement would be FALSE, and the one-sided windows 0 < Im rho <= T diverge
-- (imaginary part ~ -i n (log(T/2pi))^2/(4pi)); only the symmetric order converges, because the
-- window is closed under rho -> 1 - rho and the paired terms are O(1/gamma^2).  Right-hand side:
-- Bombieri-Lagarias 1999, Theorem 2: the archimedean closed form S_inf(n) and the finite part
-- S_f(n) = - sum_{j=1}^n C(n,j) eta_{j-1}, where -zeta'/zeta(s) - 1/(s-1) = sum_j eta_j (s-1)^j
-- near s = 1 (eta_0 = -gamma).  The function -logDeriv zeta - 1/(s-1) is extended at s = 1 by
-- its limit -gamma (Mathlib tendsto_riemannZeta_sub_one_div) so that iteratedDeriv sees the
-- analytic extension; without the update Lean's junk value of logDeriv riemannZeta at the pole
-- would make every eta_j equal to 0 (eta_0 included: -logDeriv riemannZeta 1 - 1/(1-1) = 0,
-- since riemannZeta is not differentiable at 1 so deriv returns the junk value 0) and the
-- statement FALSE already for n = 1 (finiteSide 1 = 0 instead of gamma).  Numerically
-- verified to 1e-39 for n = 1..8 against Li's generating function (memo section 5). =====

/-- Li's kernel `1 - (1 - 1/ρ)^n`; `λ_n = Σ_ρ liKernel n ρ` in the symmetric order. -/
noncomputable def liKernel (n : ℕ) (ρ : ℂ) : ℂ := 1 - (1 - 1 / ρ) ^ n

/-- The symmetric partial zero sum: strip zeros with `|Im ρ| ≤ T`, weight
    `WeilExplicit.zeroMult` (the E8 / RvMCount divisor).  `finsum` is 0 on infinite support, so
    the definition is total; finiteness of every window is a theorem. -/
noncomputable def liZeroSum (n : ℕ) (T : ℝ) : ℂ :=
  ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
    (WeilExplicit.zeroMult ρ : ℂ) * liKernel n ρ

/-- The archimedean side `S_∞(n) = 1 - (n/2)(γ + log π + 2 log 2)
    + Σ_{j=2}^n (-1)^j C(n,j) (1 - 2^{-j}) ζ(j)` (Bombieri-Lagarias 1999, Thm 2). -/
noncomputable def archSide (n : ℕ) : ℂ :=
  1 - ((n : ℂ) / 2) * ((Real.eulerMascheroniConstant : ℂ) + (Real.log Real.pi : ℂ)
      + 2 * (Real.log 2 : ℂ))
    + ∑ j ∈ Finset.Icc 2 n,
        (-1 : ℂ) ^ j * (n.choose j : ℂ) * (1 - 1 / (2 : ℂ) ^ j) * riemannZeta (j : ℂ)

/-- `-ζ'/ζ(s) - 1/(s - 1)`, extended at `s = 1` by its limit `-γ`. -/
noncomputable def zetaLogDerivReg : ℂ → ℂ :=
  Function.update (fun s : ℂ => -logDeriv riemannZeta s - 1 / (s - 1)) 1
    (-(Real.eulerMascheroniConstant : ℂ))

/-- The Laurent constants `η_j`: `-ζ'/ζ(s) - 1/(s-1) = Σ_j η_j (s-1)^j`, `η_0 = -γ`. -/
noncomputable def eta (j : ℕ) : ℂ := iteratedDeriv j zetaLogDerivReg 1 / (j.factorial : ℂ)

/-- The finite part `S_f(n) = -Σ_{j=1}^n C(n,j) η_{j-1}` (Bombieri-Lagarias 1999, Thm 2). -/
noncomputable def finiteSide (n : ℕ) : ℂ :=
  -∑ j ∈ Finset.Icc 1 n, (n.choose j : ℂ) * eta (j - 1)

end BombieriLagarias

namespace WeilForm
open WeilExplicit

/-- The Weil pairing of a test function: the E8 right-hand side `archSide f - primeSide f`,
    which `RH_limit_explicit_formula` identifies with the sum over the zeros
    `Σ_ρ zeroMult ρ · weilKernel f ρ`.  Evaluating THIS is what the `weil_form_enclosure`
    emitter's Arb backend does; the kernel only ever sees an enclosure of it as a hypothesis. -/
noncomputable def weilForm (f : ℝ → ℂ) : ℂ :=
  archSide f - primeSide f

/-- The cross-correlation `f_{ij}(x) = ∫ g_i(t) conj (g_j (t - x)) dt`.  Its diagonal
    `crossCorr g g` is the autocorrelation `g ⋆ g̃` on which Weil positivity is stated; the
    off-diagonal entries are the Weil-Gram matrix's off-diagonal entries. -/
noncomputable def crossCorr (gi gj : ℝ → ℂ) : ℝ → ℂ :=
  fun x => ∫ t : ℝ, gi t * (starRingEnd ℂ) (gj (t - x))

/-- The autocorrelation, the diagonal of `crossCorr`. -/
noncomputable abbrev autocorr (g : ℝ → ℂ) : ℝ → ℂ := crossCorr g g

end WeilForm

namespace WeilWindow
open MeasureTheory Complex WeilExplicit WeilForm
open scoped Nat

-- ===== AUTHORED for the registry (NOT in the island; 2026-09-19, the Zhu compact-window import;
-- design memo telperion/docs/ZHU_WINDOW_POSITIVITY_IMPORT_2026-09-19.md).  Vocabulary for
-- RH_weil_window_floor_of_certified_block, the one-stroke window reduction of Xuefeng Zhu,
-- arXiv:2608.24827 v2, Theorem 1.1, whose certified execution at L = 0.8 (Theorem 1.2) is the
-- unconditional bound Q(f) >= 8.9e-18 ||f||_2^2 on autocorrelation support 1.6, i.e. 2.3 times
-- the classical (log 2)/2 range of Yoshida and Connes-Consani.
--
-- The `WeilForm` namespace ABOVE is a VERBATIM mirror of
-- telperion/examples/weil_form_enclosure/lean/WeilFormDefs.lean, where those names are the
-- `weil_form_enclosure` emitter's proposed registry vocabulary; `weilForm f = archSide f -
-- primeSide f` is the right-hand side that the PROVED node RH_limit_explicit_formula identifies
-- with the sum over the zeros.  That identification is what makes a window statement expressible
-- here at all.  Mirroring it verbatim (rather than renaming it into WeilWindow) is what keeps the
-- island and the registry from silently decoupling.  Zhu's Q(f) is (weilForm (autocorr f)).re.
--
-- THE SEAM.  Zhu's reduction is NOT one step in Lean.  It is a chain:
--   RH_limit_explicit_formula (PROVED on main)
--     -> SymbolRepresentation  (eq. 2, the frequency-side rearrangement)   -- PROVED 2026-09-23
--     -> EnvelopeBound         (Lemma 3.1, the digamma envelope)           -- PROVED 2026-09-23
--     -> Parseval on the half-line                                         -- inside SymbolRepresentation
--     -> the frequency split (eq. 4)                                       -- provable
--     -> LegendreLocalization  (eqs. 6 and 12, spherical Bessel decay)     -- PROVED 2026-09-23 (ZhuTail, closed forms)
--     -> the two-block bound (eq. 13)                                      -- PROVABLE, elementary
--     -> ReducedHeadFloor      (lam0, an Arb/mpmath enclosure)             -- NON-KERNEL TRUST SEAM
--     -> min(lam0, beta* - epsD) - epsB > 0                                -- norm_num
-- Until 2026-09-23 the four analytic links were carried as OPAQUE predicates.  On 2026-09-23 the
-- three analytic ones were RE-SPECIFIED as concrete definitions mirrored verbatim from the
-- rvm_bridge island (ZhuSymbol / ZhuEnvelope / ZhuLegendre / ZhuParity), for BOTH parity sectors
-- (Zhu Lemma 6.1, proved: windowFloor_of_sectors), where the symbol representation and the
-- envelope are proved outright and the localization's analytic content (eqs. 6, 12) is proved;
-- the trust seams ReducedHeadFloor (even block) and ReducedHeadFloorOdd (odd block, added the
-- same day) stay opaque, so a certified NUMBER still cannot masquerade as a proved THEOREM.
--
-- SCOPE.  `WindowFloor L lam` with `lam > 0` at a FIXED L is a finite fragment of RH.  The
-- RH-equivalent clause is `WindowFloor L 0` for EVERY L (Weil 1952; Bombieri 2000 on
-- C_c^infinity), and nothing here reduces, weakens or approaches it.  Zhu's own Theorem 1.4
-- proves the pointwise-envelope route to it is closed: any application of Theorem 1.1 needs
-- T# > T_1 = 2 pi e^{A_L} with A_L = (4 + o(1)) e^L, so the certificate size is doubly exponential
-- in the support, and by Lemma 3.2 (sup_t of the prime comb = A_L exactly, by Weyl equidistribution
-- on {log p}) that threshold cannot be lowered.  PRE-WALL.  conjecture1_proved = False. =====

/-- Zhu eq. (1): the window floor.  `WindowFloor L lam` says the Weil form of every smooth
    compactly supported test function supported in `[-L, L]` is at least `lam ‖f‖₂²`.  Zhu's
    `λ*(L)` is the largest such `lam`; `WindowFloor L lam` with `lam > 0` is a finite fragment
    of RH, and `∀ L, WindowFloor L 0` is RH-equivalent. -/
def WindowFloor (L lam : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, WeilExplicit.IsWeilTest f → tsupport f ⊆ Set.Icc (-L) L →
    lam * (∫ x : ℝ, ‖f x‖ ^ 2) ≤ (WeilForm.weilForm (WeilForm.autocorr f)).re

/-- Zhu's comb mass `A_L = Σ_{log n < 2L} 2 Λ(n)/√n`.  A FINITE sum (`n < e^{2L}`), and the
    only information about the prime comb that the reduction uses; by Lemma 3.2 it is the exact
    supremum of the comb, so no smaller pointwise constant exists. -/
noncomputable def combMass (L : ℝ) : ℝ :=
  ∑' n : ℕ, if Real.log n < 2 * L then 2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n else 0

/-- Zhu's threshold `β* = log(T#/2π) - 1/T# - A_L`.  Theorem 1.1 requires `β* > 0`, which is
    exactly the requirement `T# > T₁ = 2π e^{A_L}` of the Theorem 1.4 barrier. -/
noncomputable def betaStar (L Tsharp : ℝ) : ℝ :=
  Real.log (Tsharp / (2 * Real.pi)) - 1 / Tsharp - combMass L

-- ===== RE-SPECIFIED 2026-09-23 (opaque -> concrete).  The three analytic inputs below are VERBATIM
-- mirrors of the rvm_bridge island modules ZhuSymbol.lean (weilSymbol, SymbolRepresentation),
-- ZhuEnvelope.lean (EnvelopeBound) and ZhuLegendre.lean (legendreP .. LegendreLocalization), plus
-- ZhuParity.lean (OddSectorFloor, EvenSectorFloor).  SymbolRepresentation and EnvelopeBound are
-- PROVED there (RvMBridgeZhu.symbolRepresentation, RvMBridgeZhu.envelopeBound); of
-- LegendreLocalization the analytic content (eqs. 6 and 12) is proved and the tail sums are the
-- paper's numerically evaluated constants.  ReducedHeadFloor below is UNCHANGED and stays opaque:
-- it is the Arb trust seam, never asserted by the kernel.  Design doc:
-- telperion/docs/ZHU_INPUTS_DISCHARGE_2026-09-23.md.  conjecture1_proved = False. =====

/-- Zhu eq. (3), the Weil symbol `Ψ_L(t) = Re ψ(1/4 + it/2) - log π - Σ_{log n < 2L} (2Λ(n)/√n)
    cos(t log n)`.  The comb is a FINITE sum (`n < e^{2L}`) with total mass `combMass L`. -/
noncomputable def weilSymbol (L : ℝ) (t : ℝ) : ℝ :=
  (Complex.digamma (1 / 4 + ((t : ℂ) / 2) * Complex.I)).re - Real.log Real.pi
    - ∑' n : ℕ, if Real.log n < 2 * L then
        2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * Real.cos (t * Real.log n) else 0

/-- Zhu eq. (2), CONCRETE: for real even smooth compactly supported `f` supported in `[-L, L]`,
    `Q(f) = 2 F(i/2)² + (1/2π) ∫ |F(t)|² Ψ_L(t) dt` with `F(t) = weilKernel f (1/2 + it)` and
    `F(i/2) = weilKernel f 0`.  A rearrangement of the PROVED `RH_limit_explicit_formula`'s
    primes-side functional. -/
def SymbolRepresentation (L : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, WeilExplicit.IsWeilTest f → (∀ x, (f x).im = 0) → (∀ x, f (-x) = f x) →
    tsupport f ⊆ Set.Icc (-L) L →
    (WeilForm.weilForm (WeilForm.autocorr f)).re
      = 2 * ‖WeilExplicit.weilKernel f 0‖ ^ 2
        + (1 / (2 * Real.pi)) *
          ∫ t : ℝ, ‖WeilExplicit.weilKernel f (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2 * weilSymbol L t

/-- Zhu eq. (2) in the ODD sector (Lemma 6.1): for real ODD smooth compactly supported `f`
    supported in `[-L, L]`, `Q(f) = -2 F(i/2)² + (1/2π) ∫ |F(t)|² Ψ_L(t) dt`; the pole term
    changes sign, the multiplier term is parity-blind. -/
def SymbolRepresentationOdd (L : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, WeilExplicit.IsWeilTest f → (∀ x, (f x).im = 0) → (∀ x, f (-x) = -f x) →
    tsupport f ⊆ Set.Icc (-L) L →
    (WeilForm.weilForm (WeilForm.autocorr f)).re
      = -2 * ‖WeilExplicit.weilKernel f 0‖ ^ 2
        + (1 / (2 * Real.pi)) *
          ∫ t : ℝ, ‖WeilExplicit.weilKernel f (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2 * weilSymbol L t

/-- Zhu Lemma 3.1, CONCRETE: `Re ψ(1/4 + it/2) - log π ≥ log(t/2π) - 1/t` for `t ≥ 15/4`.
    The digamma expression is the one `WeilExplicit.archIntegrand` integrates against. -/
def EnvelopeBound : Prop :=
  ∀ t : ℝ, 15 / 4 ≤ t →
    Real.log (t / (2 * Real.pi)) - 1 / t
      ≤ (Complex.digamma (1 / 4 + ((t : ℂ) / 2) * Complex.I)).re - Real.log Real.pi

/-- The Legendre polynomial `P_n`, Rodrigues form `P_n = (1/(2^n n!)) D^n (X² - 1)^n`. -/
noncomputable def legendreP (n : ℕ) : Polynomial ℝ :=
  Polynomial.C (1 / (2 ^ n * (n.factorial : ℝ)))
    * (Polynomial.derivative^[n] ((Polynomial.X ^ 2 - 1) ^ n))

/-- The spherical Bessel function `j_n` by the Poisson integral (cosine form, the sine part
    vanishing by parity): `j_n(x) = x^n/(2^{n+1} n!) ∫_{-1}^{1} (1 - u²)^n cos(xu) du`. -/
noncomputable def sphericalBessel (n : ℕ) (x : ℝ) : ℝ :=
  x ^ n / (2 ^ (n + 1) * (n.factorial : ℝ))
    * ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n * Real.cos (x * u)

/-- Zhu's orthonormal Legendre mode `T_n(x) = P̄_n(x/L)/√L = sqrt((n+1/2)/L) P_n(x/L)` on
    `[-L, L]`, extended by zero. -/
noncomputable def legendreMode (L : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  if |x| ≤ L then Real.sqrt ((n + 1 / 2) / L) * (legendreP n).eval (x / L) else 0

/-- The cosine transform `∫ T_n(x) cos(tx) dx`; for even `n` this is the full transform
    `T̂_n(t) = ∫ T_n(x) e^{itx} dx` of eq. (6). -/
noncomputable def legendreModeFT (L : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ x in (-L)..L, legendreMode L n x * Real.cos (t * x)

/-- The pole vector `p_n = ∫ T_n(x) cosh(x/2) dx` (so `F(i/2) = Σ c_n p_n` for even `f = Σ c_n T_n`). -/
noncomputable def poleVec (L : ℝ) (n : ℕ) : ℝ :=
  ∫ x in (-L)..L, legendreMode L n x * Real.cosh (x / 2)

/-- Zhu's C-matrix, the operator with symbol `(Ψ_L - β*) χ_[0,T#]` in the Legendre basis:
    `C_{nm} = (1/π) ∫_0^{T#} (Ψ_L(t) - β*) T̂_n(t) T̂_m(t) dt`. -/
noncomputable def combMatrix (L Tsharp : ℝ) (n m : ℕ) : ℝ :=
  (1 / Real.pi) * ∫ t in (0 : ℝ)..Tsharp,
    (weilSymbol L t - betaStar L Tsharp) * (legendreModeFT L n t * legendreModeFT L m t)

/-- Zhu's reduced matrix `M_R = β* I + 2 p pᵀ + C` on the even modes `0, 2, 4, …`, indexed by
    `k ↦ 2k`. -/
noncomputable def reducedMat (L Tsharp : ℝ) (k j : ℕ) : ℝ :=
  (if k = j then betaStar L Tsharp else 0)
    + 2 * poleVec L (2 * k) * poleVec L (2 * j) + combMatrix L Tsharp (2 * k) (2 * j)

/-- Zhu eqs. (6), (12), (13), CONCRETE: the tail data of the block decomposition after `N` even
    modes.  (i) Gershgorin: every tail row `k ≥ N` of `M_R - β* I` has absolute row sum over the
    tail `≤ epsD` (so `λ_min(D) ≥ β* - epsD`); (ii) Schur: every leading column `j < N` has
    absolute tail-column sum `≤ epsB` and every tail row `k ≥ N` has absolute leading-row sum
    `≤ epsB` (so `‖B‖ ≤ epsB`).  Summability is required explicitly so the `tsum`s are honest.
    In the certified run both constants are below `1e-100` (Zhu Section 5.3). -/
def LegendreLocalization (L Tsharp : ℝ) (N : ℕ) (epsD epsB : ℝ) : Prop :=
  (∀ k, N ≤ k →
    Summable (fun j : ℕ => if N ≤ j then
      |reducedMat L Tsharp k j - (if k = j then betaStar L Tsharp else 0)| else 0) ∧
    ∑' j : ℕ, (if N ≤ j then
      |reducedMat L Tsharp k j - (if k = j then betaStar L Tsharp else 0)| else 0) ≤ epsD) ∧
  (∀ j, j < N →
    Summable (fun k : ℕ => if N ≤ k then |reducedMat L Tsharp k j| else 0) ∧
    ∑' k : ℕ, (if N ≤ k then |reducedMat L Tsharp k j| else 0) ≤ epsB) ∧
  (∀ k, N ≤ k → ∑ j ∈ Finset.range N, |reducedMat L Tsharp k j| ≤ epsB)

/-- The sine transform `∫ T_n(x) sin(tx) dx`; for odd `n` the full transform is `i` times it, so
    `|T̂_n(t)|² = (∫ T_n sin(tx))²`. -/
noncomputable def legendreModeFTs (L : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ x in (-L)..L, legendreMode L n x * Real.sin (t * x)

/-- The odd-sector pole vector `s_n = ∫ T_n(x) sinh(x/2) dx` (so `F(i/2) = -Σ c_n s_n` for odd
    `f = Σ c_n T_n`, and the pole term is `-2 (Σ c_n s_n)²`, Zhu Lemma 6.1). -/
noncomputable def poleVecOdd (L : ℝ) (n : ℕ) : ℝ :=
  ∫ x in (-L)..L, legendreMode L n x * Real.sinh (x / 2)

/-- The C-matrix on odd modes: `C_{nm} = (1/π) ∫_0^{T#} (Ψ_L(t) - β*) T̂_n(t) T̂_m(t) dt` with
    `|T̂_n| = |∫ T_n sin(t·)|`. -/
noncomputable def combMatrixOdd (L Tsharp : ℝ) (n m : ℕ) : ℝ :=
  (1 / Real.pi) * ∫ t in (0 : ℝ)..Tsharp,
    (weilSymbol L t - betaStar L Tsharp) * (legendreModeFTs L n t * legendreModeFTs L m t)

/-- Zhu's ODD-sector reduced matrix `β* I - 2 s sᵀ + C` on the odd modes `1, 3, 5, …`, indexed by
    `k ↦ 2k + 1` (Section 6: the pole sign is reversed). -/
noncomputable def reducedMatOdd (L Tsharp : ℝ) (k j : ℕ) : ℝ :=
  (if k = j then betaStar L Tsharp else 0)
    - 2 * poleVecOdd L (2 * k + 1) * poleVecOdd L (2 * j + 1)
    + combMatrixOdd L Tsharp (2 * k + 1) (2 * j + 1)

/-- The eq. (13) tail data of the ODD sector, the same shape as `LegendreLocalization` on
    `reducedMatOdd` (Zhu Section 6: "the tail and coupling bounds of Section 4 are unchanged"). -/
def LegendreLocalizationOdd (L Tsharp : ℝ) (N : ℕ) (epsD epsB : ℝ) : Prop :=
  (∀ k, N ≤ k →
    Summable (fun j : ℕ => if N ≤ j then
      |reducedMatOdd L Tsharp k j - (if k = j then betaStar L Tsharp else 0)| else 0) ∧
    ∑' j : ℕ, (if N ≤ j then
      |reducedMatOdd L Tsharp k j - (if k = j then betaStar L Tsharp else 0)| else 0) ≤ epsD) ∧
  (∀ j, j < N →
    Summable (fun k : ℕ => if N ≤ k then |reducedMatOdd L Tsharp k j| else 0) ∧
    ∑' k : ℕ, (if N ≤ k then |reducedMatOdd L Tsharp k j| else 0) ≤ epsB) ∧
  (∀ k, N ≤ k → ∑ j ∈ Finset.range N, |reducedMatOdd L Tsharp k j| ≤ epsB)

-- ===== 2026-09-23 (second pass): the PROVED tail constants of ZhuTail.lean, closed forms in
-- L, T#, N, mirrored verbatim; `open scoped Nat` above supplies the `‼` notation. =====

/-- A crude explicit bound for `sup_{0 ≤ t ≤ T#} |Ψ_L(t) - β*|`: `Re ψ(1/4 + it/2)` lies between
    `ψ(1/4) ≥ -4.2315` and its Stirling upper bound at `T#`, `|P_L| ≤ A_L`. -/
noncomputable def symbolSup (L Tsharp : ℝ) : ℝ :=
  8463 / 2000 + (Real.log (Tsharp / 2) + 13 / Tsharp ^ 2) + Real.log Real.pi + combMass L
    + |betaStar L Tsharp|

/-- The tail majorant of the even modes: `b_j = 2 sqrt L (j+1) (T# L)^{2j} / (4j+1)!!` bounds
    `|T̂_{2j}(t)|` on `[0, T#]` and `|p_{2j}| / cosh(L/2)`. -/
noncomputable def tailMajorant (L Tsharp : ℝ) (j : ℕ) : ℝ :=
  2 * Real.sqrt L * ((j : ℝ) + 1) * ((Tsharp * L) ^ (2 * j) / ((2 * (2 * j) + 1)‼ : ℕ))

/-- The tail majorant of the odd modes: `2 sqrt L (j+2) (T# L)^{2j+1} / (4j+3)!!`. -/
noncomputable def tailMajorantOdd (L Tsharp : ℝ) (j : ℕ) : ℝ :=
  2 * Real.sqrt L * ((j : ℝ) + 2) * ((Tsharp * L) ^ (2 * j + 1) / ((2 * (2 * j + 1) + 1)‼ : ℕ))

/-- The entry constant `K = 2 cosh(L/2)² + T# S / π`: `|M_R(k,j) - β* δ_kj| ≤ K B_k B_j`. -/
noncomputable def entryConst (L Tsharp : ℝ) : ℝ :=
  2 * Real.cosh (L / 2) ^ 2 + Tsharp * symbolSup L Tsharp / Real.pi

/-- The proved tail-block deviation, even sector: `eps_D = (10/7) K b_N²`. -/
noncomputable def epsDfun (L Tsharp : ℝ) (N : ℕ) : ℝ :=
  (10 / 7) * entryConst L Tsharp * tailMajorant L Tsharp N ^ 2

/-- The proved coupling norm, even sector: `eps_B = (10/7 + N) K ((1+2L)/2) b_N`. -/
noncomputable def epsBfun (L Tsharp : ℝ) (N : ℕ) : ℝ :=
  (10 / 7 + (N : ℝ)) * entryConst L Tsharp * ((1 + 2 * L) / 2) * tailMajorant L Tsharp N

/-- The proved tail-block deviation, odd sector. -/
noncomputable def epsDfunOdd (L Tsharp : ℝ) (N : ℕ) : ℝ :=
  (10 / 7) * entryConst L Tsharp * tailMajorantOdd L Tsharp N ^ 2

/-- The proved coupling norm, odd sector. -/
noncomputable def epsBfunOdd (L Tsharp : ℝ) (N : ℕ) : ℝ :=
  (10 / 7 + (N : ℝ)) * entryConst L Tsharp * ((1 + 2 * L) / 2) * tailMajorantOdd L Tsharp N

/-- The ODD-sector window floor (Zhu Section 6, eq. (14)): the Weil form of every real ODD smooth
    test function supported in `[-L, L]` is at least `lam ‖f‖₂²`.  Together with the real even
    sector this yields `WindowFloor L lam` for complex `f` (Zhu Lemma 6.1, Corollary 6.3). -/
def OddSectorFloor (L lam : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, WeilExplicit.IsWeilTest f → (∀ x, (f x).im = 0) → (∀ x, f (-x) = -f x) →
    tsupport f ⊆ Set.Icc (-L) L →
    lam * (∫ x : ℝ, ‖f x‖ ^ 2) ≤ (WeilForm.weilForm (WeilForm.autocorr f)).re

/-- The real EVEN-sector window floor, the sector Zhu Theorem 1.1 certifies. -/
def EvenSectorFloor (L lam : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, WeilExplicit.IsWeilTest f → (∀ x, (f x).im = 0) → (∀ x, f (-x) = f x) →
    tsupport f ⊆ Set.Icc (-L) L →
    lam * (∫ x : ℝ, ‖f x‖ ^ 2) ≤ (WeilForm.weilForm (WeilForm.autocorr f)).re

/-- The ARB / MPMATH TRUST SEAM, OPAQUE: the leading `N × N` Legendre block of Zhu's reduced form
    `R` has least eigenvalue at least `lam0`.  In the certified run this is a verified Cholesky
    residual at 50 digits (Zhu Lemma 5.2 and Section 5.4).  The kernel NEVER asserts it; it enters
    every statement as a hypothesis, exactly as the zero-localization ladder's enclosures do. -/
opaque ReducedHeadFloor (L Tsharp lam0 : ℝ) (N : ℕ) : Prop

/-- The ODD-sector ARB / MPMATH TRUST SEAM, OPAQUE (added 2026-09-23 on the lead's instruction):
    the leading `N × N` ODD-mode Legendre block of Zhu's reduced form (`reducedMatOdd`, pole sign
    reversed, Zhu Section 6.2) has least eigenvalue at least `lam0`.  In the certified run this is
    the verified Cholesky residual at shift `8.2065e-15` (eq. 14).  A numeric seam of exactly the
    same kind as `ReducedHeadFloor`: the kernel NEVER asserts it; it enters every statement as a
    hypothesis, and the complex-`f` window floor is the min over both sectors (Corollary 6.3). -/
opaque ReducedHeadFloorOdd (L Tsharp lam0 : ℝ) (N : ℕ) : Prop

end WeilWindow

/-
  ===== CROSS-ISLAND VOCABULARY MIRROR (2026-09-21, the Weil-to-Li dictionary) =====
  VERBATIM from telperion/examples/rvm_bridge/lean/E6Bridge15.lean (namespace RvMBridge15, v4.33
  island), source lines cited: liPaired (155-157), liLimit (159-160), LiValue (437-443), with
  docstrings.  The block sits in a `noncomputable section` because the island file does, so the
  def texts stay byte-identical.  `liKernel`, `liZeroSum`, `archSide`, `finiteSide` are the
  registry's own BombieriLagarias block above (the island re-declares them in
  RvMBridge15.BombieriLagarias).  Vocabulary for RH_li_zero_sums_converge,
  RH_bl_explicit_formula_of_livalue, RH_li_forward_half.  conjecture1_proved = False.
-/
noncomputable section

namespace RvMBridge15
open Complex Filter Topology
open scoped ComplexConjugate
open BombieriLagarias

-- ===== E6Bridge15.lean:155-157 =====
/-- The paired (real) family: m(rho) Re K_n(rho), as a complex number. -/
def liPaired (n : ℕ) (ρ : ℂ) : ℂ :=
  (WeilExplicit.zeroMult ρ : ℂ) * ((liKernel n ρ).re : ℂ)

-- ===== E6Bridge15.lean:159-160 =====
/-- The limit of the symmetric window sums (a genuine absolutely convergent sum, section C). -/
def liLimit (n : ℕ) : ℂ := ∑' ρ : ℂ, liPaired n ρ

-- ===== E6Bridge15.lean:437-443 =====
/-- **Obligation (Bombieri-Lagarias 1999, Theorem 2; the value half of B7).**  The absolutely
convergent paired sum equals the closed form: Sum_rho m(rho) Re (1 - (1 - 1/rho)^n) =
S_inf(n) + S_f(n).  Content: the Hadamard / xi'/xi partial fraction at s = 1, i.e. the symmetric
power sums Sum_rho rho^{-j} (j = 1..n) in terms of the Laurent coefficients eta_{j-1} and the
digamma tower at 1/2.  Not in Zeta23 (whose partial fraction is Landau's local form).  Stated for
0 < n; at n = 0 both sides are computable (0 vs 1) and the node excludes it. -/
def LiValue (n : ℕ) : Prop := liLimit n = BombieriLagarias.archSide n + finiteSide n

end RvMBridge15

end

/-
  ===== CROSS-ISLAND VOCABULARY MIRROR (2026-09-21, the xi partial fraction) =====
  VERBATIM, source lines cited: Zeta23.IsNontrivialZero (vendored Zeta23 package,
  Zeta23/Statement.lean:38, commit fbdc36bbf17d20af3fd0447c6d1a8a02773c9844);
  RvMBridge18.xi (E6Bridge18.lean:56-57), xiDiffReg (188-190), XiLogDerivDerivEq (192-195),
  XiDiffRegular (197-204), XiLogDerivDerivDecay (206-211); RvMBridge20.xiDiffExt
  (E6Bridge20.lean:418-421, with its `open scoped Classical in` prefix), XiDiffExtGrowth (545-547),
  XiDiffExtGrowthRight (549-551).  The blocks sit in a `noncomputable section` because the island
  files do.  Vocabulary for RH_xi_derivative_partial_fraction_of, RH_xi_diff_entire_extension,
  RH_xi_diff_regular_of_growth.  The obligations are `def ... : Prop` consumed only as hypotheses;
  nothing here proves anything about RH.  conjecture1_proved = False.
-/
noncomputable section

namespace Zeta23
open Complex Set

-- ===== Zeta23/Statement.lean:38 (Zeta23 @ fbdc36b) =====
def IsNontrivialZero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

end Zeta23

namespace RvMBridge18
open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate
open WeilExplicit

-- ===== E6Bridge18.lean:56-57 =====
/-- xi(s) = s (s - 1)/2 * Lambda_0(s) + 1/2 (Riemann's xi; = s(s-1)/2 * Lambda(s) off {0,1}). -/
def xi (s : ℂ) : ℂ := s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2

-- ===== E6Bridge18.lean:188-190 =====
/-- xiDiffReg s = deriv (logDeriv xi) s + Sum'_rho m(rho)/(s - rho)^2 (junk at the zeros). -/
def xiDiffReg (s : ℂ) : ℂ :=
  deriv (logDeriv xi) s + ∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2

-- ===== E6Bridge18.lean:192-195 =====
/-- **The interface identity** (the derivative partial fraction of xi'/xi, no constant). -/
def XiLogDerivDerivEq : Prop :=
  ∀ s : ℂ, ¬ IsNontrivialZero s →
    deriv (logDeriv xi) s = -∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2

-- ===== E6Bridge18.lean:197-204 =====
/-- **Obligation 1 (removable singularities + logarithmic growth).**  xiDiffReg extends across
the zeros to an entire function G (at a zero of order m, deriv (logDeriv xi) = -m/(s-rho)^2 +
analytic and the sum contributes exactly +m/(s-rho)^2) with |G(s)| <= C (1 + log (2 + |s|))
(Landau's local partial fraction and Cauchy's estimate on |Re s| <= 2; Dirichlet series and
Stirling on Re s >= 2; the functional equation on Re s <= -1). -/
def XiDiffRegular : Prop :=
  ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ s : ℂ, ¬ IsNontrivialZero s → G s = xiDiffReg s) ∧
    ∃ C : ℝ, ∀ s : ℂ, ‖G s‖ ≤ C * (1 + Real.log (2 + ‖s‖))

-- ===== E6Bridge18.lean:206-211 =====
/-- **Obligation 2 (decay of the logarithmic-derivative part along the real axis).**
deriv (logDeriv xi)(sigma) = -1/sigma^2 - 1/(sigma-1)^2 + (1/4) psi'(sigma/2) + (zeta'/zeta)'(sigma)
tends to 0 as sigma -> +infinity (psi' = O(1/sigma); the Dirichlet series of (zeta'/zeta)' is
O(2^{-sigma})). -/
def XiLogDerivDerivDecay : Prop :=
  Tendsto (fun σ : ℝ => deriv (logDeriv xi) (σ : ℂ)) atTop (𝓝 0)

end RvMBridge18

namespace RvMBridge20
open Zeta23 Complex MeasureTheory Filter Topology Metric
open scoped ComplexConjugate
open WeilExplicit RvMBridge18

-- ===== E6Bridge20.lean:418-421 =====
open scoped Classical in
/-- The extension of xiDiffReg across the zeros: the punctured limit at a zero, xiDiffReg elsewhere. -/
def xiDiffExt (s : ℂ) : ℂ :=
  if IsNontrivialZero s then limUnder (𝓝[≠] s) xiDiffReg else xiDiffReg s

-- ===== E6Bridge20.lean:545-547 =====
/-- **Obligation (growth).**  The entire extension has logarithmic growth. -/
def XiDiffExtGrowth : Prop :=
  ∃ C : ℝ, ∀ s : ℂ, ‖xiDiffExt s‖ ≤ C * (1 + Real.log (2 + ‖s‖))

-- ===== E6Bridge20.lean:549-551 =====
/-- The same on the half-plane Re s >= 1/2 only (the functional equation supplies the rest). -/
def XiDiffExtGrowthRight : Prop :=
  ∃ C : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → ‖xiDiffExt s‖ ≤ C * (1 + Real.log (2 + ‖s‖))

end RvMBridge20

end

/-
  ===== CROSS-ISLAND VOCABULARY MIRROR (2026-09-21, the growth bound of the entire extension) =====
  VERBATIM from telperion/examples/rvm_bridge/lean/E6Bridge22.lean (namespace RvMBridge22, v4.33
  island), source lines cited: lcTerm (48-49), LocalCountSum (71-75), windowSet (79-80), window
  (89-90), StripDerivBound (166-175), RightDerivBound (177-181).  The finiteness lemma
  windowSet_finite (82-88) is carried as a `sorry` scaffold, flagged below.  The block sits in a
  `noncomputable section` because the island file does.  Vocabulary for RH_xi_right_deriv_bound,
  RH_xi_growth_of_two, RH_xi_derivative_partial_fraction_of_two.  The obligations are
  `def ... : Prop` consumed only as hypotheses; nothing here proves anything about RH.
  conjecture1_proved = False.
-/
noncomputable section

namespace RvMBridge22
open Zeta23 Complex MeasureTheory Filter Topology Metric
open scoped ComplexConjugate
open WeilExplicit RvMBridge18 RvMBridge20

-- ===== E6Bridge22.lean:48-49 =====
/-- The local-count term m(rho) / (1 + (Im rho - a)^2). -/
def lcTerm (a : ℝ) (ρ : ℂ) : ℝ := (WeilExplicit.zeroMult ρ : ℝ) / (1 + (ρ.im - a) ^ 2)

-- ===== E6Bridge22.lean:71-75 =====
/-- **Obligation (local zero count).**  Sum_rho m(rho)/(1 + (Im rho - a)^2) = O(log (2 + |a|)):
O(log(|a| + k)) zeros in each unit window [a + k, a + k + 1) (Zeta23.RvM.zeta_local_zero_count)
against the weights 1/(1 + k^2). -/
def LocalCountSum : Prop :=
  ∃ C : ℝ, ∀ a : ℝ, ∑' ρ : ℂ, lcTerm a ρ ≤ C * (1 + Real.log (2 + |a|))

-- ===== E6Bridge22.lean:79-80 =====
/-- The nontrivial zeros within ordinate distance 2 of s. -/
def windowSet (s : ℂ) : Set ℂ := {ρ : ℂ | IsNontrivialZero ρ} ∩ {ρ : ℂ | |ρ.im - s.im| ≤ 2}

-- ===== E6Bridge22.lean:82-88 (rvm_bridge island, v4.33).  SUPPORT LEMMA carried as `sorry`
-- HERE ONLY so that `window` elaborates: it is PROVED on the rvm_bridge island (same file, via
-- Zeta23.zetaSeam.finite_window) and is NOT a registry node; the sorry is vocabulary scaffolding
-- in the statement package, the same trust class as the node statements themselves, and never
-- enters an axiom guard (same precedent as RHInBoxAnalytic.divisor_ball_support_finite_of_one_notMem
-- in MMDefs and RvMBridge12.zeroWindowSet_finite there). =====
lemma windowSet_finite (s : ℂ) : (windowSet s).Finite := by sorry

-- ===== E6Bridge22.lean:89-90 =====
/-- The window as a Finset. -/
def window (s : ℂ) : Finset ℂ := (windowSet_finite s).toFinset

-- ===== E6Bridge22.lean:166-175 =====
/-- **Obligation (strip, Landau-Cauchy).**  On the strip 1/4 ≤ Re s ≤ 9/4, |Im s| ≥ 5, off the
zeros, the derivative of logDeriv xi with the window double poles removed is O(log|Im s|):
Zeta23.WeilEF.zeta_logDeriv_partial_fraction (Landau) for zeta'/zeta on the disc D(s, 1/2), the
Stirling bound for logDeriv Gamma_R, the rational factors, and Cauchy's estimate for the derivative
of the O(log t) remainder.  Stated on a slightly larger closed region than (B) so that (B) is in
its interior and the bound passes to the zeros by continuity. -/
def StripDerivBound : Prop :=
  ∃ C : ℝ, ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 9 / 4 → 5 ≤ |s.im| → ¬ IsNontrivialZero s →
    ‖deriv (logDeriv xi) s + ∑ ρ ∈ window s, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2‖
      ≤ C * (1 + Real.log (2 + |s.im|))

-- ===== E6Bridge22.lean:177-181 =====
/-- **Obligation (right half-plane).**  deriv (logDeriv xi) is bounded on Re s ≥ 2:
-1/s^2 - 1/(s-1)^2 + (1/4) psi'(s/2) + (zeta'/zeta)'(s), with psi' the trigamma series and
(zeta'/zeta)' = L(log * Lambda) absolutely convergent. -/
def RightDerivBound : Prop :=
  ∃ C : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖deriv (logDeriv xi) s‖ ≤ C

end RvMBridge22

end

/-
  ===== CROSS-ISLAND VOCABULARY MIRROR (2026-09-21, the Bombieri-Lagarias value identity) =====
  VERBATIM from telperion/examples/rvm_bridge/lean/E6Bridge19.lean (namespace RvMBridge19, v4.33
  island): NoRealZeroInUnitInterval (96-97), the only definition its two node statements need
  beyond what is already mirrored.  NOTE: E6Bridge19 declares NO `xi` and NO
  `XiDerivPartialFraction`; it consumes RvMBridge18.xi through `open RvMBridge18 (xi ...)` and
  takes RvMBridge18.XiLogDerivDerivEq (mirrored above) as its partial-fraction hypothesis, and
  RvMBridge15.LiValue (mirrored above) as its conclusion.  Vocabulary for
  RH_livalue_of_partial_fraction and RH_bl_explicit_formula_of_partial_fraction.
  conjecture1_proved = False.
-/
namespace RvMBridge19
open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate

-- ===== E6Bridge19.lean:96-97 =====
/-- zeta has no zero on the real segment (0, 1). -/
def NoRealZeroInUnitInterval : Prop := ∀ σ : ℝ, 0 < σ → σ < 1 → riemannZeta (σ : ℂ) ≠ 0

end RvMBridge19

/-
  ===== CROSS-ISLAND NAME RE-EXPORT (2026-09-21, B7 last mile) =====
  On the rvm_bridge island the Bombieri-Lagarias vocabulary is declared INSIDE
  `namespace RvMBridge15` as `RvMBridge15.BombieriLagarias.liKernel / liZeroSum / archSide /
  zetaLogDerivReg / eta / finiteSide` (E6Bridge15.lean:61-93), and E6Bridge26 states
  bl_explicit_formula_of_strip with those fully qualified names.  The registry's own copy is the
  top-level `BombieriLagarias` block above (a VERBATIM mirror of the same six definitions, B7
  authoring 2026-09-18).  So that the E6Bridge26 statement elaborates here with its text
  unchanged (the containment gate matches text), the three names it uses are RE-EXPORTED under
  the island's qualification as ALIASES of the registry definitions: no second copy, one source.
  Vocabulary for RH_bl_explicit_formula_of_strip.  conjecture1_proved = False.
-/
namespace RvMBridge15.BombieriLagarias
export _root_.BombieriLagarias (liZeroSum archSide finiteSide)
end RvMBridge15.BombieriLagarias
