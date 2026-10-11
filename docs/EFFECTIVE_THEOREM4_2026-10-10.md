# Effective Theorem 4 (Dobner) on the dbn island: explicit constants, explicit height, and what an effective Newman statement would still need (2026-10-10)

Programme item 4 of the RH direction note (2026-10-10), one-session bounded exploration. Companion to
NEWMAN_LAMBDA_NONNEG_SCOPING_2026-10-10.md sections 6-7, which describe the qualitative modules.

Nothing here is about Lambda = 0. An explicit height for a non-real zero of `H_t` at `t < 0` says nothing
about `t >= 0`, where "all zeros real" is RH. conjecture1_proved = False.

## 0. Summary and verdict

* **Done (Lean, axiom-clean).** `DBNTheorem4Effective.lean` (408 lines, namespace `DBNSaddle`,
  `import DBNTheorem4`) proves `theorem4_explicit`: the statement of `DBNTheorem4.theorem4` with the
  existential `Y` replaced by the explicit
  `Yeff(c, x0, eps) = max {2, 8c, 64 pi c, 2 S1/eps, 8 sqrt(c log+(2 S2/eps))}`,
  where `S1 = C1 * sum_n T1(n)`, `S2 = C2 * sum_n T2(n)` are the constants of `DBNSaddleSum`; and
  `theorem4_fully_explicit` with `Yexp`, the same expression with `S1, S2` replaced by closed-form
  majorants (`C1_eq`, `C2_eq` evaluate `C1, C2`; `T1sum_le`, `T2sum_le` bound the two Gaussian
  Dirichlet series by domination with `sum 1/n^2 = pi^2/6`). `#print axioms`:
  `[propext, Classical.choice, Quot.sound]` for all four. Compiled with
  `ARDA_LEAN_SLOTS=1 ~/hodge-engine/leanlock.sh lake env lean DBNTheorem4Effective.lean` (about 30 s,
  swap used 715 MB throughout). Wired into `lakefile.toml` (defaultTargets) and `AxiomGuardDBN` on branch `rh/selberg-newman`.
* **The rate.** `log Yexp = A(x0)/c + O(log(1/eps)) + O(1)` as `c = |t| -> 0`, with
  `A(x0) = (11/3)(3 - x0)^2 + 7/16` (`A(1/2) = 23.35`); for `c -> infinity`, `log Yexp ~ (20/3) c`. The
  constants are crude by many orders of magnitude (section 2.6) but every loss is labelled and none is
  structural except the `e^{Theta(1/c)}` growth itself, which is intrinsic (the Gaussian Dirichlet
  series on the strip really has that much mass).
* **Verdict on "effective Newman".** Theorem 4 was the cheap part. The three remaining non-effective
  steps are (a) the zero `s0` of `F_{c/4}` (Hadamard, no bound on `Re s0` at all; a lower bound on
  `Re s0` is what the constants need and nothing cheap gives it), (b) Bohr's shifts (sequential
  compactness; the effective replacement is simultaneous Dirichlet approximation, 200-400 lines,
  Mathlib has only the 1-dimensional theorem), (c) Hurwitz (contradiction; a quantitative version is
  100 lines but needs an explicit minimum modulus of `F` on a circle around `s0`, again local
  information about `s0`). The resulting height is `T(t) = exp(exp(C/|t|))` with `C ~ 4(3 - x0)`,
  driven entirely by (b), against a dynamics heuristic of `exp(O(|t|^{-1/2}))`.
  **Stopping rule: GO (done) for item 4 proper; NO-GO for an effective Newman theorem as `t -> 0^-`
  (research-level gap (a), and the Bohr route's double exponential is far from the truth);
  bounded-continue is defensible only for the reusable pieces (b) and (c), about 500-700 lines of
  Mathlib-only Lean, and for a fully effective statement in the uninteresting regime `t <= -c1`
  (large `c`), about 1000-1200 lines total.** Details in section 5.

## 1. What is in `DBNTheorem4Effective.lean`

| Declaration | Statement |
|---|---|
| `T1sum c x0`, `T2sum c x0` | `sum' n : PNat, T1 c x0 n`, same for `T2` (finite by `summable_T1/T2`) |
| `S1 c x0`, `S2 c x0` | `C1 * T1sum`, `C2 * T2sum` |
| `errBound c x0 y` | `S1 / y + S2 * exp(-y^2/(32c) + pi y)` |
| `error_sum_le_errBound` | for `abs(Re s - x0) <= 1`, `Im s >= 2`, `Im s >= 8c`: the error series is summable and its norm is `<= errBound c x0 (Im s)`. This is `error_sum_small` minus the limit step. |
| `Yeff c x0 eps` | `max (max 2 (8c)) (max (64 pi c) (max (2 S1/eps) (8 sqrt(c * max 0 (log(2 S2/eps))))))` |
| `errBound_le_of_Yeff_le` | `Yeff <= y -> errBound c x0 y <= eps` |
| `error_sum_small_explicit`, `theorem4_explicit` | the two qualitative theorems with `Y := Yeff` |
| `theorem4_of_explicit` | recovers `theorem4` |
| `neg_sq_add_le_sq_div` | `-a L^2 + b L <= b^2/(4a)` |
| `hasSum_pnat_inv_sq` | `sum_{n : PNat} 1/n^2 = pi^2/6` (from `hasSum_zeta_two`, `hasSum_pnat_iff`) |
| `T1_le`, `T2_le` | `T1(n) <= e^{8(3-x0+c)^2/(3c)} / n^2`, `T2(n) <= 4 e^{96(3-x0+c/2)^2/(59c)} / n^2` |
| `T1sum_le`, `T2sum_le` | the summed versions with `pi^2/6` |
| `C1_eq` | `C1 = 96 e^{(3-x0)^2/c + 7/(16c) + 4c + 1}` |
| `C2_eq` | `C2 = 3 sqrt(8/3) e^{(3-x0)^2/c + 1 + 15/(64c) + (4c/3)(pi+2)^2}` |
| `S1b`, `S2b`, `S1_le_S1b`, `S2_le_S2b` | closed-form majorants of `S1, S2` |
| `Yexp c x0 eps`, `Yeff_le_Yexp` | `Yeff` with `S1b, S2b`; monotonicity |
| `theorem4_fully_explicit` | `theorem4` with `Y := Yexp` |

Hypotheses `Im s >= 2` and `Im s >= 8c` come from the island's lemmas (section 2, steps 3, 4, 8, 9);
`Im s >= 64 pi c` is new here (step 11). The file ends with four `#print axioms` lines (several island
modules do the same; remove if preferred).

## 2. Trace of the constants (checkable derivation)

### 2.1 Setup (DBNSaddleAlg)

`c = -t > 0`; strip centre `x0`; `M0 = 3 - x0`; `b = s + M0`, so `2 <= Re b <= 4` on the strip
`abs(Re s - x0) <= 1`; `y = Im s = Im b`. `h_n = (c/2) log n` (`hh`), `a_n = e^{-h_n^2/c} =
e^{-(c/4) log^2 n}` (`coef`). `delta = h + i sigma`. `rho(delta) = (b+delta)(b+delta-1)/(b(b-1))`,
`Q(delta) = L((b+delta)/2) - L(b/2) - (delta/2) Log(b/2)` with Stirling's `L` (`Gamma = exp L`),
`K_n(sigma) = rho e^Q`,
`E_n(s) = e^{M0^2/c} (pi c)^{-1/2} int_R (K_n(sigma) - 1) e^{-sigma^2/c + 2 i M0 sigma/c} dsigma`.
Exact identity (`xi_J_eq`, given summability):
`xi_c(J(s)) = gamma_t(s) ( F_{c/4}(s) + sum_n a_n n^{-s} E_n(s) )`, `J(s) = s + (c/4) Log(b/(2 pi))`.
So Theorem 4's error is exactly `sum_n a_n n^{-s} E_n(s)`, and everything below bounds that series.

### 2.2 Pointwise bounds (DBNSaddleBounds, DBNSaddleSum)

Write `P(delta) = norm(delta)^2 + norm(delta) + 1`, `Pt(h, sigma) = (h + abs sigma)^2 + (h + abs sigma) + 1 >= P(delta)`.

1. Near field, `norm_K_sub_one_le` (hyp. `Re b >= 1`, `norm b >= 2`, `Im b > 0`, `Re delta >= 0`,
   `Im(b + delta) > 0`, `norm delta <= norm b / 2`):
   `norm(K - 1) <= 8 P/norm(b) * e^{2P/norm(b)}`.
   Inputs: `norm_Q_le_near` (`norm Q <= 2P/norm b`), `norm_rho_sub_one_le` (`norm(rho - 1) <= 6P/norm b`),
   `norm_exp_sub_one_le_mul_exp` (`norm(e^Q - 1) <= norm Q e^{norm Q}`).
2. Global, `norm_K_le` (hyp. `Re b >= 1`, `norm b >= 2`, `Re delta >= 0`):
   `norm K <= 2 (norm b + norm delta + 1)^2 / norm(b)^2 * exp( (Re b + Re delta - 1) norm(delta)/(2 norm b) + pi (abs(Im b) + abs(Im delta)) + 1 )`.
   Inputs: `norm_rho_le`, `re_Q_le`.
3. Unified, `norm_K_sub_one_le_unified` (hyp. `2 <= Re b <= 4`, `y >= 2`, `h >= 0`):
   `norm(K - 1) <= Nb + e^{((h + abs sigma)^2 - y^2/4)/(8c)} (1 + Gb)`,
   `Nb = (8 Pt/y) e^{2Pt/y}`, `Gb = 2 (2 + h + abs sigma)^2 e^{(3+h)(h + abs sigma)/(2y) + pi (y + abs sigma) + 1}`.
   (Near region `h + abs sigma <= y/2`: step 1 with `norm b >= y`; far region: step 2 plus
   `norm(K - 1) <= norm K + 1`, and the Gaussian factor is `>= 1` there.)

### 2.3 Integration in sigma (DBNSaddleSum)

4. `near_majorant` (hyp. `y >= 8c`): `e^{-sigma^2/c} Nb <= A1 (1 + abs sigma)^2 e^{-sigma^2/(2c) + abs(sigma)/(4c)}`,
   `A1 = 48 (h^2 + h + 1)/y * e^{(4h^2 + 2h + 2)/y}`.
   (Uses `Pt <= 6(h^2+h+1)(1 + abs sigma)^2`, `4 sigma^2/y <= sigma^2/(2c)`, `2 abs(sigma)/y <= abs(sigma)/(4c)`.)
5. `far_majorant`: `e^{-sigma^2/c} e^{((h + abs sigma)^2 - y^2/4)/(8c)} (1 + Gb) <= A2 (1 + abs sigma)^2 e^{-3 sigma^2/(4c) + aFar abs sigma}`,
   `A2 = e^{-y^2/(32c)} e^{h^2/(4c)} * 3 (2+h)^2 e^{(3+h)h/(2y) + pi y + 1}`, `aFar = (3+h)/(2y) + pi`.
6. `integral_gauss_poly_two_le`: `int_R (1 + abs sigma)^2 e^{-b sigma^2 + a abs sigma} dsigma <= Ig(b, a) := e^{(a+2)^2/(2b)} sqrt(2 pi / b)`.
   (`(1 + abs sigma)^2 e^{a abs sigma} <= e^{(a+2) abs sigma}`, complete the square, `integral_gaussian`.)
7. `norm_E_le` (hyp. `2 <= Re b <= 4`, `y >= 2`, `y >= 8c`):
   `norm(E_n(s)) <= K0 ( A1 Ig(1/(2c), 1/(4c)) + A2 Ig(3/(4c), aFar) )`, `K0 = e^{M0^2/c}/sqrt(pi c)`.

### 2.4 Absorbing `a_n` and the strip (DBNSaddleSum)

8. `coef_A1_le` (hyp. `y >= 8c`): `a_n A1 <= (48 e^{3/(8c)}/y) (h^2 + h + 1) e^{-3h^2/(8c)}`.
   (`(4h^2 + 2h + 2)/y <= (5h^2 + 3)/(8c)`.)
9. `coef_A2_le` (hyp. `y >= 8c`): `a_n A2 Ig(3/(4c), aFar) <= D2(c) (2+h)^2 e^{-59 h^2/(96c)} e^{-y^2/(32c) + pi y}`,
   `D2(c) = 3 e^{1 + 9/(64c) + 3/(32c) + (4c/3)(pi + 2)^2} sqrt(8 pi c / 3)`.
10. `norm_term_le_weights` (hyp. `abs(Re s - x0) <= 1`, `y >= 2`, `y >= 8c`), using `norm(n^{-s}) = n^{-x} <= n^{1 - x0}`:
    `norm(a_n n^{-s} E_n(s)) <= C1 T1(n)/y + C2 T2(n) e^{-y^2/(32c) + pi y}`, with
    `C1 = K0 * 48 e^{3/(8c)} Ig(1/(2c), 1/(4c))`, `C2 = K0 D2(c)`,
    `T1(n) = (h^2 + h + 1) e^{-3h^2/(8c)} n^{1-x0}`, `T2(n) = (2+h)^2 e^{-59h^2/(96c)} n^{1-x0}`.
11. `error_sum_small`: sum over `n` (`summable_T1`, `summable_T2` from the everywhere-convergent
    Gaussian Dirichlet series of `DBNFtZero`), `S1 = C1 sum T1`, `S2 = C2 sum T2`, then
    `S1/y + S2 e^{-y^2/(32c) + pi y} -> 0` and `Filter.eventually_atTop` produces a non-explicit `Y`.
    **Replaced** by `errBound_le_of_Yeff_le`: `S1/y <= eps/2` iff `y >= 2 S1/eps`; for `y >= 64 pi c`,
    `y^2/(32c) - pi y >= y^2/(64c)`, so `S2 e^{-y^2/(32c) + pi y} <= eps/2` once `y^2 >= 64 c log(2 S2/eps)`.
12. `theorem4`: `Y := max Y0 1`; replaced by `Yeff` (which is `>= 2`).

### 2.5 Closed forms

`Ig(1/(2c), 1/(4c)) = e^{c (2 + 1/(4c))^2} sqrt(4 pi c) = e^{4c + 1 + 1/(16c)} * 2 sqrt(pi c)`, hence
(`C1_eq`) `C1 = 96 e^{(3-x0)^2/c + 7/(16c) + 4c + 1}`.
`sqrt(8 pi c/3) = sqrt(8/3) sqrt(pi c)`, hence (`C2_eq`)
`C2 = 3 sqrt(8/3) e^{(3-x0)^2/c + 1 + 15/(64c) + (4c/3)(pi+2)^2}` (`3 sqrt(8/3) = 2 sqrt 6 = 4.899`).
Both checked numerically against the Lean definitions at eight `(c, x0)` pairs (agreement to all printed digits).

In `L = log n`: `T1(n) = ((c^2/4) L^2 + (c/2) L + 1) e^{-(3c/32) L^2 + (1 - x0) L}`,
`T2(n) = (2 + (c/2) L)^2 e^{-(59c/384) L^2 + (1 - x0) L}`. The mode of `T1` is at `L = 16(2 - x0)/(3c)`,
i.e. `n ~ e^{8.5/c}` for `x0 = 1/2`, so the series carries `e^{Theta(1/c)}` mass; this is intrinsic.

Two bounds for the sums:

* Route A, formalized (`T1_le`, `T2_le`, `T1sum_le`, `T2sum_le`): `h^2 + h + 1 <= (1+h)^2 <= e^{2h} = n^{c}`,
  `(2+h)^2 <= 4 e^{h} = 4 n^{c/2}`, then `T1(n) <= n^{-2} e^{-(3c/32) L^2 + (3 - x0 + c) L} <= n^{-2} e^{8(3-x0+c)^2/(3c)}`
  by completing the square, and `sum 1/n^2 = pi^2/6`:
  `sum T1 <= (pi^2/6) e^{8(3-x0+c)^2/(3c)}`, `sum T2 <= 4 (pi^2/6) e^{96(3-x0+c/2)^2/(59c)}`.
* Route B, not formalized (sharper by `e^{(8/3)((3-x0+c)^2-(2-x0+c)^2)/c}`): for `f(x) = e^{-alpha log^2 x + beta log x}`
  unimodal, `sum_{n>=1} f(n) <= max f + int_1^infty f <= (1 + sqrt(pi/alpha)) e^{(beta+1)^2/(4 alpha)}`, giving
  `sum T1 <= (1 + sqrt(32 pi/(3c))) e^{8(2-x0+c)^2/(3c)}`, `sum T2 <= 4 (1 + sqrt(384 pi/(59c))) e^{96(2-x0+c/2)^2/(59c)}`.
  Formalization: `AntitoneOn.sum_le_integral` / `MonotoneOn.sum_le_integral` on the two sides of the mode,
  150-250 lines. Not worth it unless the constants matter.

Numerical sanity (log of the sums; direct summation only feasible for `c >= 2`, the mode is too far out below that):

| `(c, x0)` | `log sum T1`: actual / B / A | `log sum T2`: actual / B / A |
|---|---|---|
| (4, 1/2) | 5.83 / 21.5 / 28.7 | 4.87 / 7.6 / 10.1 |
| (2, 1/2) | 7.57 / 18.0 / 27.5 | 6.05 / 7.9 / 11.9 |
| (1, 2) | 2.30 / 4.6 / 11.2 | 2.97 / 3.5 / 5.6 |

### 2.6 The explicit height and its size

`Yexp(c, x0, eps) = max {2, 8c, 64 pi c, 2 S1b/eps, 8 sqrt(c log+(2 S2b/eps))}` with
`log S1b = log 96 + (3-x0)^2/c + 7/(16c) + 4c + 1 + 8(3-x0+c)^2/(3c) + log(pi^2/6)`,
`log S2b = log(2 sqrt 6) + (3-x0)^2/c + 1 + 15/(64c) + (4c/3)(pi+2)^2 + log 4 + 96(3-x0+c/2)^2/(59c) + log(pi^2/6)`.

The `2 S1b/eps` term dominates for every `c` (the Gaussian term enters only through a square root of a log).
Asymptotics: `log Yexp = A(x0)/c + log(2/eps) + O(1)` as `c -> 0`, `A(x0) = (11/3)(3-x0)^2 + 7/16`;
`log Yexp ~ (20/3) c` as `c -> infinity`. With `x0 = 1/2`, `eps = 1/2`:

| `c` | 8 | 4 | 2 | 1 | 0.5 | 0.25 | 0.1 | 0.05 | 0.01 |
|---|---|---|---|---|---|---|---|---|---|
| `log10 Yexp` | 33.5 | 23.1 | 19.9 | 22.1 | 30.8 | 50.3 | 110.7 | 212.0 | 1023.3 |

Where the loss sits, in decreasing order: `e^{M0^2/c}` with `M0 = 3 - x0` (the Gaussian weight at the
shifted contour `Re v = Re s + M0 + h_n`; `M0 = 3 - x0` was chosen so that `Re b in [2, 4]` for every `x0`,
and a smaller `M0` would need `x0 > 1`, which the zero of `F` does not satisfy); the two completing-the-square
constants `e^{beta^2/(4 alpha)}` (intrinsic, see 2.5); the `(3 - x0)` in place of `(2 - x0)` from route A;
`n^{1 - x0} >= n^{-x}` on the whole strip; and the generous numerical constants (`48`, `3`, `e^{...+1}`) of the
pointwise lemmas. Dobner's own Theorem 4 has `O(y^{-1/5} e^{(10/|t|) min(x, -2)^2})`, the same
exponential-in-`1/|t|` shape; the `y^{-1/5}` is not reproduced here (the island's bound is `O(1/y)` in `y`,
which is better in `y`, but on a strip of width 2 rather than in `|x| <= C y^{1/4}`).

## 3. What an effective Newman statement needs beyond Theorem 4

The island proof (`DBNNewman.dbn_newman_of_neg`) has three further non-effective steps. For each: what the Lean
proof does, what an effective version needs, what Mathlib (de5ce8a9) and the island offer, and a line estimate.

### (a) An explicit zero `s0` of `F_{c/4}`, and in particular a lower bound on `x0 = Re s0`

* Lean: `DBNFtZero.exists_zero` is by contradiction via `Hadamard.entire_no_zeros_is_exp_polynomial`
  (LiCriterion), then `Classical.choose`. No information on `Re s0` or `Im s0`. `DBNFtZeroHigh.exists_zero_im_ge`
  (zeros at arbitrary height) is Hurwitz-by-contradiction on top of Bohr: also no information.
* What the constants need: the height `Yexp` grows like `e^{(11/3)(3 - x0)^2/c}`, so an **upper bound on
  `(3 - x0)^2`, i.e. a lower bound on `x0`**, is what matters; `abs(Im s0)` only enters additively.
* Cheap and explicit: `F_{c/4}` is zero-free for `Re s >= 2`, uniformly in `c` (`norm(F - 1) <= sum_{n >= 2} n^{-2}
  = pi^2/6 - 1 = 0.645 < 1`); 30-50 lines with `hasSum_zeta_two`. So `x0 < 2`, `M0 > 1`. This is the wrong
  direction for the constants.
* Lower bound on `x0`: nothing cheap. For `Re s` very negative the terms `a_n n^{-x}` peak at `log n = 2|x|/c`
  with value `e^{x^2/c}` and many are comparable, so there is no dominant-term zero-free region on the left.
  Representation: for `Re s > 1`, `F_{c/4}(s) = (pi c)^{-1/2} int_R zeta(s + i tau) e^{-tau^2/c} dtau` (vertical
  Gaussian average of `zeta`, width `sqrt c`); continuing to `Re s < 1` adds the pole term, a multiple of
  `e^{(1-s)^2/c}` with modulus `e^{((1-x)^2 - y^2)/c}`, negligible for `y > abs(1-x) + O(sqrt c)`. Consequently,
  for small `c` and moderate height, `F = zeta - (c/4) zeta'' + O(c^2)`, and `F_{c/4}` has a zero within `O(c)`
  of `rho_1 = 1/2 + 14.1347 i` for all `c <= c0`: an explicit `s0` with `x0 = 1/2 + O(c)`. Proving this needs
  verified bounds for `zeta, zeta', zeta''` on a disc around `rho_1` and the quantitative Hurwitz of (c). The
  island has Euler-Maclaurin for `zeta` in the strip (`M6gapEMZeta*`, `M6gapHeightFloorBoxes` for the
  verified-numerics pattern), so this is a finite computation, but a large one: 1-2k lines, verified-numerics
  style. For `c` large the series is `1 + a_2 2^{-s} + (small)` on the relevant strip and the two-term model has
  the explicit zero `-(c/4) log 2 + i pi/log 2` with `F'` of modulus about `log 2`; elementary, 300-500 lines,
  valid for `c >= c1` with an explicit `c1`. For intermediate `c` there is no route I can see short of
  per-`c` numerics, and no `c`-uniform explicit `s0` at all.
* Jensen: Mathlib at this pin has `Mathlib/Analysis/Complex/JensenFormula.lean` (`MeromorphicOn.circleAverage_log_norm`,
  `AnalyticOnNhd.circleAverage_log_norm`, `AnalyticOnNhd.sum_divisor_le`; the island already uses the last in
  `DBNHadamardCount`). With `F(x) >= 1` on the real axis and `log norm(F(s)) <= norm(s)^2/(2c) + log K`
  (`norm_F_le`), Jensen gives an explicit **upper** bound on the number of zeros in a disc around a real
  centre. A **lower** bound (existence in a prescribed disc) needs the argument principle or Rouche, both
  absent from Mathlib at this pin (`DBNHurwitz` header), or a mean-value argument. Jensen alone does not
  locate a zero.
* Note also: de Bruijn monotonicity (`dbn_real_zeros_upset`) transfers "non-real zero at `t'`" to all
  `t < t'`, but not its location, so an effective statement at one `c` does not give one at larger `c`.

### (b) Quantitative Bohr: an explicit shift `tau`

* Lean: `DBNBohr.exists_twist_close` is sequential compactness of the twist vectors `(n^{-ik})_{n <= N}` in the
  closed unit ball of `Fin N -> C`; `shift` is `Classical.choose` over it. No rate. The surrounding estimate
  `norm_LSeries_shift_sub_le` is already explicit in `(k, m)`:
  `norm(F(s + ik) - F(s)) <= sum_{n < m} norm(term(-R, n)) norm(n^{-ik} - 1) + 2 tail(R, m)` for `Re s >= -R`.
* Needed: for `N`, `Q >= 1`, `T0 >= 1`: `tau in [T0, T0 Q^N]` with `dist(tau log n/(2 pi), Z) <= 1/Q` for all
  `n <= N`, hence `norm(n^{-i tau} - 1) <= 2 pi/Q`. This is **simultaneous Dirichlet approximation** for the
  vector `(T0 log n/(2 pi))_{n <= N}`: pigeonhole on the `Q^N + 1` points `m * alpha mod 1`, `0 <= m <= Q^N`, in
  `[0,1)^N` cut into `Q^N` boxes of side `1/Q`; the difference of two points in one box is `tau = (m - m') T0`
  with `1 <= m - m' <= Q^N`. (Using primes `p <= N` only, via multiplicativity of `n^{-i tau}`, reduces the
  dimension to `pi(N)`; same shape.)
* Mathlib (de5ce8a9) inventory: `Real.exists_int_int_abs_mul_sub_le` (Dirichlet, dimension 1, 41 lines, pigeonhole
  through `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` with `m -> floor(fract(xi m)(n+1))`);
  `Real.exists_nat_abs_mul_sub_round_le`, `Real.exists_rat_abs_sub_le_and_den_le`; nothing simultaneous, no
  Kronecker (`grep -ri simultaneous|kronecker Mathlib/NumberTheory` is empty); `Int.Matrix.exists_ne_zero_int_vec_norm_le`
  (Siegel's lemma, same pigeonhole pattern in dimension `m x n`, a good template); Minkowski
  `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` (would also do it, with the box
  `abs q <= Q^N`, `abs(q alpha_j - p_j) <= 1/Q`, but the volume is borderline-equal and the strict inequality
  needs an enlargement; heavier); `AddCircle/DenseSubgroup` is 1-dimensional density only; `ZSpan` exists.
  Estimate for `exists_simultaneous_approx`: 200-400 lines (map `m -> (j -> floor(fract(m T0 alpha_j) Q))` into
  `Fin N -> Fin Q`, cardinality `Q^N < Q^N + 1`, then unwind). Making `DBNBohr` explicit on top: explicit cutoff
  `m` (tail via the `n^{-2}` trick: `log m >= 4(3 - x0)/c + 2 sqrt(log(4/eta)/c)` suffices for
  `2 tail <= eta/2` on `Re s >= x0 - 1`) and explicit head mass (`<= (pi^2/6) e^{(3-x0)^2/c}` by the same trick):
  another 150-250 lines. Total 400-600 lines, Mathlib-only, reusable.
* Resulting size: `log tau <= log T0 + N log Q` with `N ~ e^{4(3 - x0)/c}` and
  `log Q ~ (3 - x0)^2/c + log(2 pi/eta)`, so `log log tau ~ 4(3 - x0)/c + O(log(1/c))`:
  **doubly exponential in `1/|t|`**, driven by the number `N` of Dirichlet terms that must be controlled on the
  strip (the Gaussian decay `e^{-(c/4) log^2 n}` only beats `n^{1 - x0}` from `log n ~ 4(1-x0)/c` on). This is
  not a proof artifact: approximating `N` generic phases to accuracy `1/Q` simultaneously needs `tau ~ Q^N` (the
  good `tau <= X` have measure about `X Q^{-N}`). Avoiding it means abandoning almost periodicity for a zero-density
  statement for `F` in tall rectangles (Bohr-Jessen / Jessen-Tornehave mean motion), which is far heavier.
  Numbers for `x0 = 1/2`: `c = 1`: `log10 log10 tau ~ 4.7`; `c = 0.25`: `~ 18`; `c = 0.1`: `~ 44`.

### (c) The Hurwitz transfer

* Lean: `DBN.hurwitz_ne_zero` is used twice (`DBNFtZeroHigh`, `DBNNewman`) by contradiction, with the limit along
  the Bohr sequence; the proof inside `DBNHurwitz` is already the maximum-modulus argument on `1/F_i`.
* Quantitative version (a Rouche with a factor 2, from the same argument): if `norm F >= m` on the circle
  `abs(s - s0) = r`, `F(s0) = 0`, `G` analytic on the closed disc and `sup norm(G - F) < m/2` on it, then `G` has
  a zero in the open disc (`Complex.norm_le_of_forall_mem_frontier_norm_le` applied to `1/G`). About 100 lines,
  Mathlib-only. Not in Mathlib, not on the island.
* Missing input: `m(c) = min_{circle} norm(F_{c/4})`. From a simple zero with `norm(F'(s0)) >= kappa` and
  `norm F'' <= M` on the disc, take `r = kappa/M`, `m = kappa^2/(2M)`. `M` is explicit
  (`sum log^2 n a_n n^{-x}`, a Gaussian Dirichlet series, same bounds as section 2.5); `kappa` is explicit only
  where `s0` is (large `c`: `kappa ~ log 2`; small `c` near `rho_1`: `kappa ~ norm(zeta'(rho_1)) = 0.78`, needing the
  verified numerics of (a)). Theorem 4 and Bohr are then invoked with `eps = m/4` each (the Lean proof uses
  `eps/2 + eps/2` on the disc `abs(s - s0) < 1`, inside the strip `abs(Re s - x0) <= 1`).

## 4. Shape of the effective theorem

Assume (a), (b), (c) supplied: explicit `s0 = x0 + i y0`, radius `r`, minimum modulus `m`. Then for `t = -c < 0`
there is `z` with `H_t(z) = 0`, `Im z <= -delta(t)`, `abs(Re z) <= T(t)`, where (with `w = s0 + i tau + O(r)` the
zero of `h = xi_c o J / gamma_t` found by (c), and `z = -i(2J(w) - 1)`):

* `Re z = 2 Im J(w) = 2 tau + O(1)`, so `T(t) ~ 2 tau`;
* `Im z = 1 - 2 Re J(w) = 1 - 2 Re w - (c/2) log(norm(w + M0)/(2 pi)) <= 1 - 2(x0 - r) - (c/2) log((tau - abs y0 - r)/(2 pi))`
  (`DBNNewman.re_J`, `im_Z`);
* `tau >= T0 := max { Yexp(c, x0, m/4) + abs y0 + r, 2 pi e^{2(1 - 2x0 + 2r + delta)/c} }` (the first so that
  Theorem 4 applies on the shifted disc, the second for `Im z <= -delta`; `DBNNewman` uses the cruder
  `2 pi e^{4(2 + abs x0)/c}`);
* (b) delivers `tau in [T0, T0 Q^N]`.

Hence `log T(t) ~ A(x0)/c + N log Q` and `log log T(t) ~ 4(3 - x0)/c`: **`T(t) = exp(exp(C/|t|))`, `C ~ 4(3 - x0(t))`**
(about 10 if `x0 ~ 1/2`), with the Theorem 4 contribution only single-exponential, `exp(A(x0)/|t|)`, `A(1/2) = 23.4`.
The zero found has `Im z ~ -(c/2) log tau ~ -(c/2) e^{4(3-x0)/c}`, very far from the axis: the Bohr route finds
a zero at a height where `J` has shifted the real part enormously, not the first non-real zero.
In the large-`c` regime the picture inverts: `x0 ~ -(c/4) log 2`, `N ~ 2 e^{12/c} ~ 2`, and `T(t)` is
`e^{O(c)}` times a polynomial in `Q`; cheap, and uninteresting.

Comparison with the Rodgers-Tao dynamics (a heuristic, not a theorem): under the backward heat flow the
zeros obey `d/dt x_k = 2 sum_{j != k} 1/(x_k - x_j)`; an isolated pair with gap `g` collides at `t ~ -g^2/8` and then
leaves the axis. Zeros of `H_0` sit at `2 gamma_n`, mean gap `4 pi / log(gamma/(2 pi))`, so the first non-real zeros of
`H_{-c}` are expected at heights `abs(Re z) ~ 4 pi e^{pi sqrt(2/c)}`, i.e. **`exp(O(|t|^{-1/2}))`**, with `delta(t) = O(sqrt c)`;
small gaps lower this further. Numbers (`x0 = 1/2`):

| `c` | dynamics heuristic `log10 T` | Theorem 4 alone `log10 Yexp` | Dobner route `log10 log10 T` |
|---|---|---|---|
| 1 | 3.0 | 22 | 4.7 |
| 0.25 | 5.0 | 50 | 18 |
| 0.1 | 7.2 | 111 | 44 |

So the Dobner route, made effective, is doubly exponential where the truth is (heuristically) singly exponential in
`|t|^{-1/2}`; the gap is the Bohr step, and it is intrinsic to that step. None of this concerns `Lambda = 0`.

## 5. Stopping-rule verdict and estimates

| Piece | Status | Lines | Value |
|---|---|---|---|
| Theorem 4 with explicit `Y` (closed form) | **done, axiom-clean** | 408 (this module) | item 4 complete |
| Sharper sum bounds (route B) | not done | 150-250 | cosmetic |
| `F_{c/4}` zero-free for `Re s >= 2` | not done | 30-50 | gives `x0 < 2` only |
| Simultaneous Dirichlet approximation | not done | 200-400 | reusable, Mathlib gap |
| Explicit Bohr (cutoff, head, shift) on top | not done | 150-250 | reusable |
| Quantitative Hurwitz (Rouche/2) | not done | ~100 | reusable |
| Explicit `s0`, `kappa`, `m` for `c >= c1` (two-term regime) | not done | 300-500 | effective Newman for `t <= -c1` only |
| Explicit `s0` near `rho_1` for `c <= c0` (verified `zeta` numerics via island Euler-Maclaurin) | not done | 1-2k | effective Newman for small `|t|`, `T = exp(exp(C/|t|))` |
| `c`-uniform explicit `s0` | no route | - | research gap |

**GO** on item 4 as specified (delivered). **NO-GO** on "effective Newman as `t -> 0^-`" as a formalization target:
the explicit zero `s0` is a research-level gap for intermediate `c`, and even granting it the route yields
`exp(exp(C/|t|))`, qualitatively wrong against the dynamics heuristic, so the theorem would be effective but not
informative. **Bounded-continue** is defensible only for the Mathlib-level infrastructure (simultaneous
Dirichlet + explicit Bohr + quantitative Hurwitz, 500-700 lines, all reusable and independent of `H_t`), and, if a
complete effective statement in some regime is wanted for the record, the large-`c` package (another 300-500 lines,
total about 1000-1200, inside the 3k rule) giving an unconditional effective Newman theorem for `t <= -c1`.
Recommendation: do not continue on this item now; log the Dirichlet-approximation gap as a Mathlib contribution
candidate.

## 6. Provenance and wiring

* Module: `~/arda-e9-audit/telperion/examples/dbn/lean/DBNTheorem4Effective.lean` (new file only; no existing file
  touched, `lakefile.toml` not edited). Built with the slot wrapper only, never `lake build`. Swap used 715 MB
  before and after every build.
* Numerics: `scratchpad/consts2.py` and inline scripts (constant cross-checks and the tables above); not part of
  the deliverable.
* To wire: add `DBNTheorem4Effective` to `defaultTargets` in `lakefile.toml` and
  `#print axioms DBNSaddle.theorem4_fully_explicit` to `AxiomGuardDBN`; the four `#print axioms` lines at the end
  of the module can then be removed.
* Not claimed: any rate for `dbn_newman`; any statement about `Lambda = 0`. conjecture1_proved = False.
