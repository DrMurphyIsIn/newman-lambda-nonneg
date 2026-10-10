/-
  DBNBohr -- Bohr almost periodicity for everywhere absolutely convergent Dirichlet series.

  Step 1 of the Lambda >= 0 (Newman's conjecture) formalization, following Dobner
  (arXiv:2005.05142, Theorem 5 in its qualitative form; Bohr 1922).  See
  telperion/docs/NEWMAN_LAMBDA_NONNEG_SCOPING_2026-10-10.md.

  Statement.  If `LSeriesSummable f s` holds for every `s : ℂ` (the Dirichlet series
  `∑ f n / n^s` converges absolutely everywhere), then there is a strictly increasing sequence of
  natural-number shifts `τ k` such that `s ↦ LSeries f (s + τ k * I)` converges to `LSeries f`
  locally uniformly on `ℂ`.

  Method.  The vector of unit twists `n ↦ n^{-k i}`, `1 ≤ n ≤ N`, lives in a compact set, so some
  subsequence converges; differences of far-apart members of that subsequence give integer shifts
  `k`, as large as desired, with every twist within `ε` of `1`.  A tail estimate uniform on
  `Re s ≥ -R` plus a diagonal choice of `(N, ε, k)` along `R = j` gives locally uniform convergence.
  No Diophantine approximation theorem is needed, only sequential compactness.

  Nothing here is RH.  conjecture1_proved = False.
-/
import Mathlib

open Complex Filter Topology Metric

namespace DBNBohr

/-! ### Unit twists and their recurrence -/

/-- The unit-modulus twist `n^{-k i}` of the `n`-th Dirichlet term under the vertical shift by `k`. -/
noncomputable def twist (k : ℕ) (n : ℕ) : ℂ := (n : ℂ) ^ (-((k : ℂ) * I))

lemma norm_twist {n : ℕ} (hn : 0 < n) (k : ℕ) : ‖twist k n‖ = 1 := by
  unfold twist
  have hre : (-((k : ℂ) * I)).re = 0 := by simp
  rw [norm_natCast_cpow_of_pos hn, hre, Real.rpow_zero]

/-- The twist is within `2` of `1`, weighted by any Dirichlet term (the `n = 0` term vanishes). -/
lemma norm_term_mul_twist_sub_one_le (f : ℕ → ℂ) (s : ℂ) (k n : ℕ) :
    ‖LSeries.term f s n‖ * ‖twist k n - 1‖ ≤ 2 * ‖LSeries.term f s n‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  · have : ‖twist k n - 1‖ ≤ 2 := by
      calc ‖twist k n - 1‖ ≤ ‖twist k n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_twist hn, norm_one]; norm_num
    nlinarith [norm_nonneg (LSeries.term f s n)]

lemma twist_add {n : ℕ} (hn : 0 < n) (a b : ℕ) :
    twist (a + b) n = twist a n * twist b n := by
  unfold twist
  have h0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← cpow_add _ _ h0]
  congr 1
  push_cast
  ring

/-- The twist vector on `1 ≤ n ≤ N`, indexed by `Fin N` with `n = i + 1`. -/
noncomputable def twistVec (N : ℕ) (k : ℕ) : Fin N → ℂ := fun i => twist k (i.1 + 1)

lemma twistVec_mem_closedBall (N k : ℕ) : twistVec N k ∈ closedBall (0 : Fin N → ℂ) 1 := by
  rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  exact (norm_twist (Nat.succ_pos _) k).le

/-- **Recurrence of the twists** (the only Diophantine input of the whole argument).  For every
`N`, `ε > 0` and `T`, there is a natural number `k ≥ T` with `‖n^{-k i} - 1‖ < ε` for all
`1 ≤ n ≤ N`.  Proof: the twist vectors lie in a compact set, a subsequence converges, and the
difference of two far-apart members of the subsequence is such a `k`. -/
theorem exists_twist_close (N : ℕ) {ε : ℝ} (hε : 0 < ε) (T : ℕ) :
    ∃ k : ℕ, T ≤ k ∧ ∀ n : ℕ, 1 ≤ n → n ≤ N → ‖twist k n - 1‖ < ε := by
  obtain ⟨L, -, φ, hφ, hlim⟩ :=
    (isCompact_closedBall (0 : Fin N → ℂ) 1).tendsto_subseq (twistVec_mem_closedBall N)
  have hclose : ∀ᶠ j in atTop, dist (twistVec N (φ j)) L < ε / 2 :=
    (Metric.tendsto_nhds.mp hlim) (ε / 2) (by positivity)
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp hclose
  have hfar : ∀ᶠ j in atTop, φ j₀ + T ≤ φ j := hφ.tendsto_atTop.eventually_ge_atTop _
  obtain ⟨j₁, hj₁⟩ := eventually_atTop.mp ((eventually_ge_atTop j₀).and hfar)
  obtain ⟨hj₁₀, hφj₁⟩ := hj₁ j₁ le_rfl
  refine ⟨φ j₁ - φ j₀, by omega, ?_⟩
  intro n hn1 hnN
  have hle : φ j₀ ≤ φ j₁ := by omega
  -- the two twist vectors are within ε of each other
  have hd : dist (twistVec N (φ j₁)) (twistVec N (φ j₀)) < ε := by
    calc dist (twistVec N (φ j₁)) (twistVec N (φ j₀))
        ≤ dist (twistVec N (φ j₁)) L + dist (twistVec N (φ j₀)) L := dist_triangle_right _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hj₀ j₁ hj₁₀) (hj₀ j₀ le_rfl)
      _ = ε := by ring
  -- read off the n-th coordinate
  set i : Fin N := ⟨n - 1, by omega⟩ with hi
  have hcoord : dist (twistVec N (φ j₁) i) (twistVec N (φ j₀) i) < ε :=
    lt_of_le_of_lt (dist_le_pi_dist _ _ i) hd
  have hn0 : 0 < n := hn1
  have hni : i.1 + 1 = n := by simp [hi]; omega
  simp only [twistVec, hni, dist_eq_norm] at hcoord
  -- factor the shift: twist (φ j₁) n = twist (φ j₀) n * twist (φ j₁ - φ j₀) n
  have hsplit : twist (φ j₁) n = twist (φ j₀) n * twist (φ j₁ - φ j₀) n := by
    rw [← twist_add hn0]
    congr 1
    omega
  rw [hsplit] at hcoord
  have hunit : ‖twist (φ j₀) n‖ = 1 := norm_twist hn0 _
  calc ‖twist (φ j₁ - φ j₀) n - 1‖
      = ‖twist (φ j₀) n‖ * ‖twist (φ j₁ - φ j₀) n - 1‖ := by rw [hunit, one_mul]
    _ = ‖twist (φ j₀) n * twist (φ j₁ - φ j₀) n - twist (φ j₀) n‖ := by
        rw [← norm_mul, mul_sub, mul_one]
    _ < ε := hcoord

/-! ### The Dirichlet series under a vertical shift -/

/-- The `n`-th term of the series at `s + k i` is the term at `s` times the twist. -/
lemma term_add_mul_I (f : ℕ → ℂ) (s : ℂ) (k n : ℕ) :
    LSeries.term f (s + (k : ℂ) * I) n = LSeries.term f s n * twist k n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  · have h0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne', twist, cpow_add _ _ h0,
      cpow_neg]
    field_simp

/-- The tail `∑_{i} ‖f (i + m)‖ (i + m)^R`, a bound for the tail of the series uniformly on
`Re s ≥ -R`. -/
noncomputable def tail (f : ℕ → ℂ) (R : ℝ) (m : ℕ) : ℝ :=
  ∑' i, ‖LSeries.term f (-(R : ℂ)) (i + m)‖

lemma summable_norm_term (f : ℕ → ℂ) {s : ℂ} (hf : LSeriesSummable f s) :
    Summable fun n => ‖LSeries.term f s n‖ :=
  hf.norm

lemma tail_tendsto_zero (f : ℕ → ℂ) (R : ℝ) :
    Tendsto (tail f R) atTop (𝓝 0) :=
  tendsto_sum_nat_add fun n => ‖LSeries.term f (-(R : ℂ)) n‖

lemma tail_nonneg (f : ℕ → ℂ) (R : ℝ) (m : ℕ) : 0 ≤ tail f R m :=
  tsum_nonneg fun _ => norm_nonneg _

/-- The basic estimate: on `Re s ≥ -R`, with the first `m` terms controlled by the twists and the
rest by the tail. -/
theorem norm_LSeries_shift_sub_le (f : ℕ → ℂ) (hf : ∀ s : ℂ, LSeriesSummable f s) {R : ℝ}
    {s : ℂ} (hs : -R ≤ s.re) (k m : ℕ) :
    ‖LSeries f (s + (k : ℂ) * I) - LSeries f s‖ ≤
      (∑ n ∈ Finset.range m, ‖LSeries.term f (-(R : ℂ)) n‖ * ‖twist k n - 1‖) + 2 * tail f R m := by
  have hsum_s : Summable (LSeries.term f s) := hf s
  have hsum_sk : Summable (LSeries.term f (s + (k : ℂ) * I)) := hf _
  -- the difference as one absolutely convergent series
  have hdiff : LSeries f (s + (k : ℂ) * I) - LSeries f s =
      ∑' n, LSeries.term f s n * (twist k n - 1) := by
    unfold LSeries
    rw [← hsum_sk.tsum_sub hsum_s]
    congr 1
    funext n
    rw [term_add_mul_I, mul_sub, mul_one]
  -- termwise domination on `Re s ≥ -R`
  have hdom : ∀ n, ‖LSeries.term f s n * (twist k n - 1)‖ ≤
      ‖LSeries.term f (-(R : ℂ)) n‖ * ‖twist k n - 1‖ := by
    intro n
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (LSeries.norm_term_le_of_re_le_re f (by simpa using hs) n) (norm_nonneg _)
  have hsumR : Summable fun n => ‖LSeries.term f (-(R : ℂ)) n‖ := summable_norm_term f (hf _)
  have hsumg : Summable fun n => ‖LSeries.term f s n * (twist k n - 1)‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) hdom ?_
    exact Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => norm_term_mul_twist_sub_one_le f _ k n) (hsumR.mul_left 2)
  have hsumG : Summable fun n => LSeries.term f s n * (twist k n - 1) := hsumg.of_norm
  rw [hdiff]
  -- split at m
  rw [← hsumG.sum_add_tsum_nat_add m]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum fun n _ => hdom n
  · refine (norm_tsum_le_tsum_norm (hsumg.comp_injective (add_left_injective m))).trans ?_
    unfold tail
    rw [← tsum_mul_left]
    exact (hsumg.comp_injective (add_left_injective m)).tsum_le_tsum
      (fun i => (hdom _).trans (norm_term_mul_twist_sub_one_le f _ k _))
      ((hsumR.comp_injective (add_left_injective m)).mul_left 2)

/-! ### The diagonal choice of shifts -/

/-- `ε j = 1 / (j + 1)`. -/
noncomputable def eps (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

lemma eps_pos (j : ℕ) : 0 < eps j := by unfold eps; positivity

/-- A cutoff `m` at level `j` with `2 * tail f j m < eps j / 2`. -/
lemma exists_cutoff (f : ℕ → ℂ) (_hf : ∀ s : ℂ, LSeriesSummable f s) (j : ℕ) :
    ∃ m : ℕ, 2 * tail f j m < eps j / 2 := by
  have ht := tail_tendsto_zero f j
  have : ∀ᶠ m in atTop, dist (tail f j m) 0 < eps j / 4 :=
    (Metric.tendsto_nhds.mp ht) (eps j / 4) (by have := eps_pos j; positivity)
  obtain ⟨m, hm⟩ := eventually_atTop.mp this
  refine ⟨m, ?_⟩
  have h := hm m le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (tail_nonneg f j m)] at h
  linarith

noncomputable def cutoff (f : ℕ → ℂ) (hf : ∀ s : ℂ, LSeriesSummable f s) (j : ℕ) : ℕ :=
  Classical.choose (exists_cutoff f hf j)

lemma cutoff_spec (f : ℕ → ℂ) (hf : ∀ s : ℂ, LSeriesSummable f s) (j : ℕ) :
    2 * tail f j (cutoff f hf j) < eps j / 2 :=
  Classical.choose_spec (exists_cutoff f hf j)

/-- The finite head mass `∑_{n < m} ‖f n‖ n^j` at level `j`. -/
noncomputable def headMass (f : ℕ → ℂ) (hf : ∀ s : ℂ, LSeriesSummable f s) (j : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (cutoff f hf j), ‖LSeries.term f (-((j : ℝ) : ℂ)) n‖

lemma headMass_nonneg (f : ℕ → ℂ) (hf : ∀ s : ℂ, LSeriesSummable f s) (j : ℕ) :
    0 ≤ headMass f hf j :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- The twist tolerance at level `j`: `δ j = eps j / (2 (headMass j + 1))`. -/
noncomputable def delta (f : ℕ → ℂ) (hf : ∀ s : ℂ, LSeriesSummable f s) (j : ℕ) : ℝ :=
  eps j / (2 * (headMass f hf j + 1))

lemma delta_pos (f : ℕ → ℂ) (hf : ∀ s : ℂ, LSeriesSummable f s) (j : ℕ) : 0 < delta f hf j := by
  unfold delta
  have := eps_pos j
  have := headMass_nonneg f hf j
  positivity

/-- The shifts, chosen recursively: `shift (j+1) > shift j`, and at level `j` every twist of
index `n ≤ cutoff j` is within `delta j` of `1`. -/
noncomputable def shift (f : ℕ → ℂ) (hf : ∀ s : ℂ, LSeriesSummable f s) : ℕ → ℕ
  | 0 => Classical.choose (exists_twist_close (cutoff f hf 0) (delta_pos f hf 0) 0)
  | j + 1 => Classical.choose
      (exists_twist_close (cutoff f hf (j + 1)) (delta_pos f hf (j + 1)) (shift f hf j + 1))

lemma shift_spec (f : ℕ → ℂ) (hf : ∀ s : ℂ, LSeriesSummable f s) (j : ℕ) :
    ∀ n : ℕ, 1 ≤ n → n ≤ cutoff f hf j → ‖twist (shift f hf j) n - 1‖ < delta f hf j := by
  cases j with
  | zero => exact (Classical.choose_spec (exists_twist_close (cutoff f hf 0) (delta_pos f hf 0) 0)).2
  | succ j => exact (Classical.choose_spec (exists_twist_close (cutoff f hf (j + 1))
      (delta_pos f hf (j + 1)) (shift f hf j + 1))).2

lemma shift_lt_succ (f : ℕ → ℂ) (hf : ∀ s : ℂ, LSeriesSummable f s) (j : ℕ) :
    shift f hf j < shift f hf (j + 1) := by
  have := (Classical.choose_spec (exists_twist_close (cutoff f hf (j + 1))
      (delta_pos f hf (j + 1)) (shift f hf j + 1))).1
  show shift f hf j < Classical.choose _
  omega

lemma shift_strictMono (f : ℕ → ℂ) (hf : ∀ s : ℂ, LSeriesSummable f s) :
    StrictMono (shift f hf) :=
  strictMono_nat_of_lt_succ (shift_lt_succ f hf)

/-- At level `j`, on `Re s ≥ -j`, the shifted series is within `eps j` of the series. -/
theorem norm_shift_sub_lt (f : ℕ → ℂ) (hf : ∀ s : ℂ, LSeriesSummable f s) (j : ℕ) {s : ℂ}
    (hs : -(j : ℝ) ≤ s.re) :
    ‖LSeries f (s + (shift f hf j : ℂ) * I) - LSeries f s‖ < eps j := by
  refine (norm_LSeries_shift_sub_le f hf hs (shift f hf j) (cutoff f hf j)).trans_lt ?_
  have hhead : (∑ n ∈ Finset.range (cutoff f hf j),
      ‖LSeries.term f (-((j : ℝ) : ℂ)) n‖ * ‖twist (shift f hf j) n - 1‖) ≤
      headMass f hf j * delta f hf j := by
    unfold headMass
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun n hn => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp [LSeries.term_zero]
    · exact mul_le_mul_of_nonneg_left
        (shift_spec f hf j n hn0 (Finset.mem_range.mp hn).le).le (norm_nonneg _)
  have hδ : headMass f hf j * delta f hf j ≤ eps j / 2 := by
    unfold delta
    have h1 := headMass_nonneg f hf j
    have h2 := eps_pos j
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have htail := cutoff_spec f hf j
  -- the tail at level j was bounded for R = j; the hypothesis gives Re s ≥ -j
  linarith

/-! ### The theorem -/

/-- **Bohr almost periodicity, qualitative form.**  For an everywhere absolutely convergent
Dirichlet series there is a strictly increasing sequence of natural-number vertical shifts along
which the shifted series converges to the series locally uniformly on `ℂ`. -/
theorem exists_shifts_tendstoLocallyUniformly (f : ℕ → ℂ) (hf : ∀ s : ℂ, LSeriesSummable f s) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧
      TendstoLocallyUniformly (fun j s => LSeries f (s + (τ j : ℂ) * I)) (LSeries f) atTop := by
  refine ⟨shift f hf, shift_strictMono f hf, ?_⟩
  rw [← tendstoLocallyUniformlyOn_univ, tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro K _ hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- K is bounded: Re s ≥ -R on K
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  -- choose the level j ≥ R with eps j < ε
  obtain ⟨j₀, hj₀⟩ := exists_nat_gt (max R (1 / ε))
  filter_upwards [eventually_ge_atTop j₀] with j hj s hsK
  have hsR : ‖s‖ ≤ R := by simpa using hR hsK
  have hre : -(j : ℝ) ≤ s.re := by
    have h1 : -‖s‖ ≤ s.re := by
      have := abs_re_le_norm s
      linarith [neg_abs_le s.re]
    have h2 : R < j₀ := lt_of_le_of_lt (le_max_left _ _) hj₀
    have h3 : (j₀ : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  have hεj : eps j < ε := by
    unfold eps
    have h2 : 1 / ε < j₀ := lt_of_le_of_lt (le_max_right _ _) hj₀
    have h3 : (j₀ : ℝ) ≤ j := by exact_mod_cast hj
    rw [div_lt_iff₀ (by positivity)]
    have : 1 / ε * ε = 1 := by field_simp
    nlinarith [this, hε]
  rw [dist_comm, dist_eq_norm]
  exact (norm_shift_sub_lt f hf j hre).trans hεj

end DBNBohr
