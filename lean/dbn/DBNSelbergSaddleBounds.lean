/-
  DBNSelbergSaddleBounds -- the pointwise saddle-point estimates of Dobner's Theorem 4 for an
  element `F` of the extended Selberg class (`DBNSelberg.ExtSelbergData`).

  This generalizes DBNSaddleBounds (zeta: one Gamma factor `Gamma(b/2)`, `P(v) = v(v-1)/16`) and the
  unified pointwise bound of DBNSaddleSum (`norm_K_sub_one_le_unified`) to
  `gamma_F(v) = P(v) Q^v prod_j Gamma(lam_j v + mu_j)`.  With `K = rho_F(delta) exp(Q_F(delta))`,
  `rho_F = P(b+delta)/P(b)`, `Q_F = sum_j [L(w_j + lam_j delta) - L(w_j) - lam_j delta Log w_j]`,
  `w_j = lam_j b + mu_j`, on the strip `2 <= Re b <= 4`, `Im b = y >= Y_0(F)`:

  * polynomial ratio: `|P(b)| >= |lead| |b|^d / 2` once `|b| >= R_P = 2 sum|coeff| / |lead|`;
        ‖rho_F - 1‖ <= C_P ‖delta‖ / ‖b‖  (‖delta‖ <= ‖b‖),   ‖rho_F‖ <= R_P (1 + ‖delta‖)^d;
  * one Gamma factor, near field (`‖v‖ <= (2/3)‖w‖`, `Im w > 0`, `Im (w+v) > 0`):
        Q_j = w (Log(1+u) - u) + (v - 1/2) Log(1+u) + R(w+v) - R(w),  u = v/w,
        ‖Q_j‖ <= 4 (1 + ‖v‖)^2 / ‖w‖,
    with the branch-free split `Log(w+v) = Log w + Log(1 + v/w)` (both arguments in the open upper
    half-plane, so the two determinations differ by less than `2 pi`);
  * one Gamma factor, global (`Re w > 0`, `Re (w+v) > 0`, `Im w > 0`):
        Re Q_j <= Re(w+v) ‖v‖/‖w‖ + (pi/2)|Im(w+v)| + (1/2) log(‖w‖/‖w+v‖) - Re v + ‖R(w+v)‖ + ‖R w‖,
    the `pi/2` because both arguments lie in the open right half-plane, and the `(1/2) log` term
    (absent for zeta, where `Re(w+v) - 1/2 >= 0`) absorbed into `exp(lam_j y / 4)` through
    `log x <= x - 1`;
  * the sum over `j` and the unified bound
        ‖K - 1‖ <= NbF(y,h,sigma) + e^{((h+|sigma|)^2 - y^2/4)/(8c)} (1 + GbF(y,h,sigma)),
    near field for `h + |sigma| <= y/2`, global elsewhere, with the Gaussian factor `>= 1` as the
    indicator of the far region.

  All constants (`CN`, `CG`, `Y_0`) are explicit functions of the data.  Nothing here is RH.
  conjecture1_proved = False.
-/
import Mathlib
import DBNSelbergData
import DBNSaddleBounds
import DBNSaddleSum

open Complex Filter Topology MeasureTheory Set
open scoped Real

namespace DBNSelberg

open DBNGaussConv DBNStirling DBNSaddle

/-! ### Generic lemmas -/

/-- `‖(x+y)^k − x^k‖ (‖x‖+‖y‖) ≤ k ‖y‖ (‖x‖+‖y‖)^k`. -/
lemma norm_add_pow_sub_pow_mul_le (x y : ℂ) (k : ℕ) :
    ‖(x + y) ^ k - x ^ k‖ * (‖x‖ + ‖y‖) ≤ k * ‖y‖ * (‖x‖ + ‖y‖) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hM0 : 0 ≤ ‖x‖ + ‖y‖ := by positivity
    have hxy : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le _ _
    have hxk : ‖x‖ ^ k ≤ (‖x‖ + ‖y‖) ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) (by linarith [norm_nonneg y]) k
    have heq : (x + y) ^ (k + 1) - x ^ (k + 1) = ((x + y) ^ k - x ^ k) * (x + y) + x ^ k * y := by
      ring
    have h1 : ‖(x + y) ^ (k + 1) - x ^ (k + 1)‖ ≤
        ‖(x + y) ^ k - x ^ k‖ * (‖x‖ + ‖y‖) + (‖x‖ + ‖y‖) ^ k * ‖y‖ := by
      rw [heq]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_pow]
      gcongr
    have hy0 := norm_nonneg y
    have hD0 := norm_nonneg ((x + y) ^ k - x ^ k)
    calc ‖(x + y) ^ (k + 1) - x ^ (k + 1)‖ * (‖x‖ + ‖y‖)
        ≤ (‖(x + y) ^ k - x ^ k‖ * (‖x‖ + ‖y‖) + (‖x‖ + ‖y‖) ^ k * ‖y‖) * (‖x‖ + ‖y‖) := by
          gcongr
      _ = (‖(x + y) ^ k - x ^ k‖ * (‖x‖ + ‖y‖)) * (‖x‖ + ‖y‖) + (‖x‖ + ‖y‖) ^ (k + 1) * ‖y‖ := by
          ring
      _ ≤ (k * ‖y‖ * (‖x‖ + ‖y‖) ^ k) * (‖x‖ + ‖y‖) + (‖x‖ + ‖y‖) ^ (k + 1) * ‖y‖ := by
          gcongr
      _ = ((k + 1 : ℕ) : ℝ) * ‖y‖ * (‖x‖ + ‖y‖) ^ (k + 1) := by push_cast; ring

/-! ### The branch-free logarithm split in the upper half-plane -/

/-- `Log (w + u) = Log w + Log (1 + u/w)` whenever `Im w > 0` and `Im (w + u) > 0`: the two
determinations of `arg` differ by less than `2π`, so the integer in `exp_eq_exp_iff_exists_int`
is `0`. -/
theorem log_add_eq {w u : ℂ} (hw : 0 < w.im) (hwu : 0 < (w + u).im) :
    log (w + u) = log w + log (1 + u / w) := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hwu0 : w + u ≠ 0 := fun h => by simp [h] at hwu
  have hu1 : (1 : ℂ) + u / w ≠ 0 := by
    intro h
    have h2 : (1 + u / w) * w = w + u := by field_simp
    rw [h, zero_mul] at h2
    exact hwu0 h2.symm
  have hexp : cexp (log (w + u)) = cexp (log w + log (1 + u / w)) := by
    rw [Complex.exp_add, Complex.exp_log hwu0, Complex.exp_log hw0, Complex.exp_log hu1]
    field_simp
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have him : arg (w + u) = arg w + arg (1 + u / w) + n * (2 * π) := by
    have := congrArg Complex.im hn
    simp only [Complex.add_im, Complex.log_im, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im] at this
    rw [this]
    ring
  have h1 : 0 ≤ arg (w + u) := Complex.arg_nonneg_iff.mpr hwu.le
  have h2 : arg (w + u) < π := Complex.arg_lt_pi_iff.mpr (Or.inr hwu.ne')
  have h3 : 0 ≤ arg w := Complex.arg_nonneg_iff.mpr hw.le
  have h4 : arg w < π := Complex.arg_lt_pi_iff.mpr (Or.inr hw.ne')
  have h5 : |arg (1 + u / w)| ≤ π := Complex.abs_arg_le_pi _
  have hn0 : n = 0 := by
    have hpi := Real.pi_pos
    have h6 := abs_le.mp h5
    have key : (n : ℝ) * (2 * π) = arg (w + u) - arg w - arg (1 + u / w) := by
      linarith [him]
    have h7 : |(n : ℝ) * (2 * π)| < 2 * π := by
      rw [key, abs_lt]
      constructor <;> linarith
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at h7
    have h8 : |(n : ℝ)| < 1 := (mul_lt_iff_lt_one_left (by positivity)).mp h7
    exact_mod_cast Int.abs_lt_one_iff.mp (by exact_mod_cast h8)
  rw [hn0] at hn
  simpa using hn

/-! ### One Gamma factor: near field -/

/-- `L(w+v) − L(w) − v Log w = w (Log(1+u) − u) + (v − 1/2) Log(1+u) + R(w+v) − R(w)`, `u = v/w`. -/
theorem Qj_eq_near {w v : ℂ} (hw : 0 < w.im) (hwv : 0 < (w + v).im) :
    L (w + v) - L w - v * log w =
      w * (log (1 + v / w) - v / w) + (v - 1 / 2) * log (1 + v / w) + (R (w + v) - R w) := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  rw [L, L, log_add_eq hw hwv]
  field_simp
  ring

/-- Near-field bound for one Gamma factor: `‖Q_j‖ ≤ 4 (1 + ‖v‖)² / ‖w‖` when `‖v‖ ≤ (2/3)‖w‖`. -/
theorem norm_Qj_le_near {w v : ℂ} (hwre : 0 < w.re) (hwvre : 0 < (w + v).re) (hw : 0 < w.im)
    (hwv : 0 < (w + v).im) (hv : ‖v‖ ≤ 2 / 3 * ‖w‖) :
    ‖L (w + v) - L w - v * log w‖ ≤ 4 * (1 + ‖v‖) ^ 2 / ‖w‖ := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hu' : ‖v / w‖ = ‖v‖ / ‖w‖ := norm_div _ _
  have hu : ‖v / w‖ ≤ 2 / 3 := by rw [hu', div_le_iff₀ hwpos]; linarith
  have hu0 := norm_nonneg (v / w)
  have hv0 := norm_nonneg v
  have hwvn : ‖w‖ / 3 ≤ ‖w + v‖ := by
    have := norm_sub_norm_le w (-v)
    simp at this
    linarith
  have hwvpos : 0 < ‖w + v‖ := by linarith
  have hls : ‖log (1 + v / w) - v / w‖ ≤ 3 / 2 * ‖v / w‖ ^ 2 := by
    have := Complex.norm_log_one_add_sub_self_le (z := v / w) (by linarith)
    have hinv : (1 - ‖v / w‖)⁻¹ ≤ 3 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    calc ‖log (1 + v / w) - v / w‖ ≤ ‖v / w‖ ^ 2 * (1 - ‖v / w‖)⁻¹ / 2 := this
      _ ≤ ‖v / w‖ ^ 2 * 3 / 2 := by gcongr
      _ = 3 / 2 * ‖v / w‖ ^ 2 := by ring
  have hl : ‖log (1 + v / w)‖ ≤ 2 * ‖v / w‖ := by
    calc ‖log (1 + v / w)‖ = ‖(log (1 + v / w) - v / w) + v / w‖ := by ring_nf
      _ ≤ ‖log (1 + v / w) - v / w‖ + ‖v / w‖ := norm_add_le _ _
      _ ≤ 3 / 2 * ‖v / w‖ ^ 2 + ‖v / w‖ := by linarith
      _ ≤ 2 * ‖v / w‖ := by nlinarith
  rw [Qj_eq_near hw hwv]
  have hA : ‖w * (log (1 + v / w) - v / w)‖ ≤ 3 / 2 * ‖v‖ ^ 2 / ‖w‖ := by
    rw [norm_mul]
    calc ‖w‖ * ‖log (1 + v / w) - v / w‖ ≤ ‖w‖ * (3 / 2 * ‖v / w‖ ^ 2) := by gcongr
      _ = 3 / 2 * ‖v‖ ^ 2 / ‖w‖ := by rw [hu']; field_simp
  have hB : ‖(v - 1 / 2) * log (1 + v / w)‖ ≤ (2 * ‖v‖ ^ 2 + ‖v‖) / ‖w‖ := by
    rw [norm_mul]
    have h1 : ‖v - 1 / 2‖ ≤ ‖v‖ + 1 / 2 := by
      calc ‖v - 1 / 2‖ ≤ ‖v‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le _ _
        _ = ‖v‖ + 1 / 2 := by rw [norm_div, norm_one, Complex.norm_ofNat]
    calc ‖v - 1 / 2‖ * ‖log (1 + v / w)‖ ≤ (‖v‖ + 1 / 2) * (2 * ‖v / w‖) := by gcongr
      _ = (2 * ‖v‖ ^ 2 + ‖v‖) / ‖w‖ := by rw [hu']; field_simp
  have hC : ‖R (w + v) - R w‖ ≤ 1 / ‖w‖ := by
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖R (w + v)‖ ≤ 3 / (4 * ‖w‖) := by
      refine (norm_R_le hwvre).trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h2 : ‖R w‖ ≤ 1 / (4 * ‖w‖) := norm_R_le hwre
    calc ‖R (w + v)‖ + ‖R w‖ ≤ 3 / (4 * ‖w‖) + 1 / (4 * ‖w‖) := add_le_add h1 h2
      _ = 1 / ‖w‖ := by field_simp; norm_num
  calc ‖w * (log (1 + v / w) - v / w) + (v - 1 / 2) * log (1 + v / w) + (R (w + v) - R w)‖
      ≤ ‖w * (log (1 + v / w) - v / w)‖ + ‖(v - 1 / 2) * log (1 + v / w)‖ +
        ‖R (w + v) - R w‖ := norm_add₃_le
    _ ≤ 3 / 2 * ‖v‖ ^ 2 / ‖w‖ + (2 * ‖v‖ ^ 2 + ‖v‖) / ‖w‖ + 1 / ‖w‖ :=
        add_le_add (add_le_add hA hB) hC
    _ = (3 / 2 * ‖v‖ ^ 2 + (2 * ‖v‖ ^ 2 + ‖v‖) + 1) / ‖w‖ := by field_simp
    _ ≤ 4 * (1 + ‖v‖) ^ 2 / ‖w‖ := by
        refine div_le_div_of_nonneg_right ?_ hwpos.le
        nlinarith

/-! ### One Gamma factor: global -/

/-- Global bound for one Gamma factor (raw form). -/
theorem re_Qj_le_raw {w v : ℂ} (hwre : 0 < w.re) (hwvre : 0 < (w + v).re) (hwim : 0 < w.im) :
    (L (w + v) - L w - v * log w).re ≤
      (w + v).re * (‖v‖ / ‖w‖) + π / 2 * |(w + v).im| + 1 / 2 * Real.log (‖w‖ / ‖w + v‖) -
        v.re + 1 / (4 * ‖w + v‖) + 1 / (4 * ‖w‖) := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hwre
  have hwv0 : w + v ≠ 0 := fun h => by simp [h] at hwvre
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hwvpos : 0 < ‖w + v‖ := norm_pos_iff.mpr hwv0
  have hQ : L (w + v) - L w - v * log w =
      (w + v) * (log (w + v) - log w) - (log (w + v) - log w) / 2 - v + (R (w + v) - R w) := by
    rw [L, L]; ring
  rw [hQ]
  set A : ℂ := log (w + v) - log w with hA
  have hAre : A.re = Real.log ‖w + v‖ - Real.log ‖w‖ := by
    rw [hA, Complex.sub_re, Complex.log_re, Complex.log_re]
  have hAre_le : A.re ≤ ‖v‖ / ‖w‖ := by
    rw [hAre, ← Real.log_div hwvpos.ne' hwpos.ne']
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [div_sub_one hwpos.ne', div_le_div_iff_of_pos_right hwpos]
    linarith [norm_add_le w v]
  have hAim : A.im = arg (w + v) - arg w := by
    rw [hA, Complex.sub_im, Complex.log_im, Complex.log_im]
  have hargw : |arg w| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hwre)
  have hargwv : |arg (w + v)| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hwvre)
  have hargw0 : 0 ≤ arg w := Complex.arg_nonneg_iff.mpr hwim.le
  have hcross : -((w + v).im * A.im) ≤ π / 2 * |(w + v).im| := by
    rw [hAim]
    rcases le_or_gt 0 (w + v).im with him | him
    · have h0 : 0 ≤ arg (w + v) := Complex.arg_nonneg_iff.mpr him
      rw [abs_of_nonneg him]
      have h1 := abs_lt.mp hargw
      have h2 := abs_lt.mp hargwv
      nlinarith [mul_nonneg him (by linarith : (0 : ℝ) ≤ arg (w + v) - arg w + π / 2)]
    · have h0 : arg (w + v) < 0 := Complex.arg_neg_iff.mpr him
      rw [abs_of_neg him]
      have hpi := Real.pi_pos
      nlinarith [mul_pos_of_neg_of_neg him (by linarith : arg (w + v) - arg w < 0)]
  have hprod : ((w + v) * A).re ≤ (w + v).re * (‖v‖ / ‖w‖) + π / 2 * |(w + v).im| := by
    rw [Complex.mul_re]
    have h1 : (w + v).re * A.re ≤ (w + v).re * (‖v‖ / ‖w‖) :=
      mul_le_mul_of_nonneg_left hAre_le hwvre.le
    linarith
  have hR : (R (w + v) - R w).re ≤ 1 / (4 * ‖w + v‖) + 1 / (4 * ‖w‖) := by
    calc (R (w + v) - R w).re ≤ ‖R (w + v) - R w‖ := Complex.re_le_norm _
      _ ≤ ‖R (w + v)‖ + ‖R w‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add (norm_R_le hwvre) (norm_R_le hwre)
  have hlog : -(A.re / 2) = 1 / 2 * Real.log (‖w‖ / ‖w + v‖) := by
    rw [hAre, Real.log_div hwpos.ne' hwvpos.ne']; ring
  rw [Complex.add_re, Complex.sub_re, Complex.sub_re, Complex.div_ofNat_re]
  linarith [hprod, hR, hlog]

namespace ExtSelbergData

variable (F : ExtSelbergData)

/-! ### Constants -/

/-- Sum of the coefficient norms of `P`. -/
noncomputable def SP : ℝ := ∑ k ∈ Finset.range (F.P.natDegree + 1), ‖F.P.coeff k‖

/-- `R_P = 2 ∑‖coeff‖ / ‖lead‖`: beyond this radius `‖P(z)‖ ≥ ‖lead‖ ‖z‖^d / 2`. -/
noncomputable def RP : ℝ := 2 * F.SP / ‖F.P.leadingCoeff‖

/-- The near-field polynomial constant: `‖ρ_F − 1‖ ≤ C_P ‖δ‖ / ‖b‖`. -/
noncomputable def CP : ℝ :=
  2 ^ (F.P.natDegree + 1) * F.P.natDegree * F.SP / ‖F.P.leadingCoeff‖

/-- The near-field Gamma constant: `‖Q_F‖ ≤ C_Q (1 + ‖δ‖)² / y`. -/
noncomputable def CQ : ℝ := ∑ j, 6 * (1 + F.lam j) ^ 2 / F.lam j

/-- The near-field constant. -/
noncomputable def CN : ℝ := 1 + F.CP + F.CQ

/-- The global Gamma coefficient of `(1 + Re δ) ‖δ‖ / y`. -/
noncomputable def AG : ℝ := ∑ j, 4 / 3 * (5 * F.lam j + (F.mu j).re)

/-- The global Gamma additive constant. -/
noncomputable def BG : ℝ :=
  ∑ j, (π / 2 * |(F.mu j).im| + F.lam j + ‖F.mu j‖ / 4 + |Real.log (F.lam j)| / 2 +
    1 / (4 * F.lam j))

/-- The global constant. -/
noncomputable def CG : ℝ := 1 + F.RP + F.AG + F.BG

/-- `∑_j 4 |Im μ_j| / λ_j`: above this height every `Im (λ_j b + μ_j) ≥ (3/4) λ_j Im b`. -/
noncomputable def Ymu : ℝ := ∑ j, 4 * |(F.mu j).im| / F.lam j

/-- The height threshold. -/
noncomputable def Y₀ : ℝ := 2 + F.RP + F.Ymu

lemma leadingCoeff_norm_pos : 0 < ‖F.P.leadingCoeff‖ :=
  norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr F.P_ne_zero)

lemma SP_nonneg : 0 ≤ F.SP := Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma leadingCoeff_norm_le_SP : ‖F.P.leadingCoeff‖ ≤ F.SP := by
  unfold SP
  rw [← Polynomial.coeff_natDegree]
  exact Finset.single_le_sum (f := fun k => ‖F.P.coeff k‖) (fun k _ => norm_nonneg _)
    (Finset.mem_range.mpr (Nat.lt_succ_self _))

lemma two_le_RP : 2 ≤ F.RP := by
  unfold RP
  rw [le_div_iff₀ F.leadingCoeff_norm_pos]
  linarith [F.leadingCoeff_norm_le_SP]

lemma CP_nonneg : 0 ≤ F.CP := by
  unfold CP
  have := F.SP_nonneg
  have := F.leadingCoeff_norm_pos
  positivity

lemma CQ_nonneg : 0 ≤ F.CQ :=
  Finset.sum_nonneg fun j _ => by have := F.lam_pos j; positivity

theorem one_le_CN : 1 ≤ F.CN := by
  unfold CN; linarith [F.CP_nonneg, F.CQ_nonneg]

lemma CN_nonneg : 0 ≤ F.CN := by linarith [F.one_le_CN]

lemma AG_nonneg : 0 ≤ F.AG :=
  Finset.sum_nonneg fun j _ => by have := F.lam_pos j; have := F.mu_re_nonneg j; positivity

lemma BG_nonneg : 0 ≤ F.BG :=
  Finset.sum_nonneg fun j _ => by have := F.lam_pos j; positivity

theorem one_le_CG : 1 ≤ F.CG := by
  unfold CG; linarith [F.two_le_RP, F.AG_nonneg, F.BG_nonneg]

lemma CG_nonneg : 0 ≤ F.CG := by linarith [F.one_le_CG]

lemma Ymu_nonneg : 0 ≤ F.Ymu :=
  Finset.sum_nonneg fun j _ => by have := F.lam_pos j; positivity

theorem two_le_Y₀ : 2 ≤ F.Y₀ := by
  unfold Y₀; linarith [F.two_le_RP, F.Ymu_nonneg]

lemma RP_le_Y₀ : F.RP ≤ F.Y₀ := by
  unfold Y₀; linarith [F.Ymu_nonneg]

lemma four_abs_im_mu_le {b : ℂ} (hy : F.Y₀ ≤ b.im) (j : Fin F.r) :
    4 * |(F.mu j).im| ≤ F.lam j * b.im := by
  have hl := F.lam_pos j
  have h1 : 4 * |(F.mu j).im| / F.lam j ≤ F.Ymu :=
    Finset.single_le_sum (f := fun j => 4 * |(F.mu j).im| / F.lam j)
      (fun j _ => by have := F.lam_pos j; positivity) (Finset.mem_univ j)
  have h2 : F.Ymu ≤ b.im := by unfold Y₀ at hy; linarith [F.two_le_RP]
  rw [div_le_iff₀ hl] at h1
  nlinarith [mul_le_mul_of_nonneg_right h2 hl.le]

/-! ### The polynomial -/

/-- `‖P(z)‖ ≤ (∑‖coeff‖) M^d` for `M ≥ max(1, ‖z‖)`. -/
lemma norm_P_eval_le {z : ℂ} {M : ℝ} (hM1 : 1 ≤ M) (hzM : ‖z‖ ≤ M) :
    ‖F.P.eval z‖ ≤ F.SP * M ^ F.P.natDegree := by
  rw [Polynomial.eval_eq_sum_range, SP, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [norm_mul, norm_pow]
  have hk' : k ≤ F.P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖z‖ ^ k ≤ M ^ k := pow_le_pow_left₀ (norm_nonneg _) hzM k
    _ ≤ M ^ F.P.natDegree := pow_le_pow_right₀ hM1 hk'

/-- `‖P(z)‖ ≥ ‖lead‖ ‖z‖^d / 2` for `‖z‖ ≥ max(1, R_P)`. -/
lemma norm_P_eval_ge {z : ℂ} (hz1 : 1 ≤ ‖z‖) (hzR : F.RP ≤ ‖z‖) :
    ‖F.P.leadingCoeff‖ * ‖z‖ ^ F.P.natDegree / 2 ≤ ‖F.P.eval z‖ := by
  have hzpos : 0 < ‖z‖ := by linarith
  have hlead := F.leadingCoeff_norm_pos
  have hRP : 2 * F.SP ≤ ‖F.P.leadingCoeff‖ * ‖z‖ := by
    have : F.RP * ‖F.P.leadingCoeff‖ = 2 * F.SP := by unfold RP; field_simp
    nlinarith
  have hsplit : F.P.eval z =
      (∑ k ∈ Finset.range F.P.natDegree, F.P.coeff k * z ^ k) +
        F.P.leadingCoeff * z ^ F.P.natDegree := by
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, Polynomial.coeff_natDegree]
  have hT : ‖∑ k ∈ Finset.range F.P.natDegree, F.P.coeff k * z ^ k‖ * ‖z‖ ≤
      F.SP * ‖z‖ ^ F.P.natDegree := by
    calc ‖∑ k ∈ Finset.range F.P.natDegree, F.P.coeff k * z ^ k‖ * ‖z‖
        ≤ (∑ k ∈ Finset.range F.P.natDegree, ‖F.P.coeff k‖ * ‖z‖ ^ k) * ‖z‖ := by
          gcongr
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
          rw [norm_mul, norm_pow]
      _ = ∑ k ∈ Finset.range F.P.natDegree, ‖F.P.coeff k‖ * ‖z‖ ^ (k + 1) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
      _ ≤ ∑ k ∈ Finset.range F.P.natDegree, ‖F.P.coeff k‖ * ‖z‖ ^ F.P.natDegree := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk : k + 1 ≤ F.P.natDegree := Finset.mem_range.mp hk
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz1 hk) (norm_nonneg _)
      _ ≤ ∑ k ∈ Finset.range (F.P.natDegree + 1), ‖F.P.coeff k‖ * ‖z‖ ^ F.P.natDegree := by
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.mpr (Nat.le_succ _)) fun _ _ _ => by positivity
      _ = F.SP * ‖z‖ ^ F.P.natDegree := by rw [SP, Finset.sum_mul]
  have hlow : ‖F.P.leadingCoeff‖ * ‖z‖ ^ F.P.natDegree -
      ‖∑ k ∈ Finset.range F.P.natDegree, F.P.coeff k * z ^ k‖ ≤ ‖F.P.eval z‖ := by
    rw [hsplit, add_comm]
    have := norm_sub_norm_le (F.P.leadingCoeff * z ^ F.P.natDegree)
      (-(∑ k ∈ Finset.range F.P.natDegree, F.P.coeff k * z ^ k))
    rw [norm_neg, sub_neg_eq_add, norm_mul, norm_pow] at this
    exact this
  have hzd : 0 ≤ ‖z‖ ^ F.P.natDegree := by positivity
  have key : ‖F.P.leadingCoeff‖ * ‖z‖ ^ F.P.natDegree / 2 * ‖z‖ ≤ ‖F.P.eval z‖ * ‖z‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hlow hzpos.le,
      mul_nonneg hzd (by linarith : (0 : ℝ) ≤ ‖F.P.leadingCoeff‖ * ‖z‖ - 2 * F.SP)]
  exact le_of_mul_le_mul_right key hzpos

/-- `‖P(z+u) − P(z)‖ (‖z‖+‖u‖) ≤ (∑‖coeff‖) d ‖u‖ (‖z‖+‖u‖)^d`. -/
lemma norm_P_eval_sub_le (z u : ℂ) (hM : 1 ≤ ‖z‖ + ‖u‖) :
    ‖F.P.eval (z + u) - F.P.eval z‖ * (‖z‖ + ‖u‖) ≤
      F.SP * F.P.natDegree * ‖u‖ * (‖z‖ + ‖u‖) ^ F.P.natDegree := by
  have hM0 : 0 ≤ ‖z‖ + ‖u‖ := by positivity
  have hdiff : F.P.eval (z + u) - F.P.eval z =
      ∑ k ∈ Finset.range (F.P.natDegree + 1), F.P.coeff k * ((z + u) ^ k - z ^ k) := by
    rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hdiff]
  calc ‖∑ k ∈ Finset.range (F.P.natDegree + 1), F.P.coeff k * ((z + u) ^ k - z ^ k)‖ *
        (‖z‖ + ‖u‖)
      ≤ (∑ k ∈ Finset.range (F.P.natDegree + 1), ‖F.P.coeff k‖ * ‖(z + u) ^ k - z ^ k‖) *
        (‖z‖ + ‖u‖) := by
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [norm_mul]
    _ = ∑ k ∈ Finset.range (F.P.natDegree + 1),
        ‖F.P.coeff k‖ * (‖(z + u) ^ k - z ^ k‖ * (‖z‖ + ‖u‖)) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ ∑ k ∈ Finset.range (F.P.natDegree + 1),
        ‖F.P.coeff k‖ * (F.P.natDegree * ‖u‖ * (‖z‖ + ‖u‖) ^ F.P.natDegree) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' : k ≤ F.P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        refine mul_le_mul_of_nonneg_left ((norm_add_pow_sub_pow_mul_le z u k).trans ?_)
          (norm_nonneg _)
        have h1 : (k : ℝ) ≤ F.P.natDegree := by exact_mod_cast hk'
        have h2 : (‖z‖ + ‖u‖) ^ k ≤ (‖z‖ + ‖u‖) ^ F.P.natDegree := pow_le_pow_right₀ hM hk'
        have hu0 := norm_nonneg u
        exact mul_le_mul (mul_le_mul h1 le_rfl hu0 (Nat.cast_nonneg _)) h2 (by positivity)
          (by positivity)
    _ = F.SP * F.P.natDegree * ‖u‖ * (‖z‖ + ‖u‖) ^ F.P.natDegree := by
        rw [SP, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring

lemma P_eval_ne_zero_of_norm {z : ℂ} (hz1 : 1 ≤ ‖z‖) (hzR : F.RP ≤ ‖z‖) : F.P.eval z ≠ 0 := by
  have h := F.norm_P_eval_ge hz1 hzR
  have : 0 < ‖F.P.leadingCoeff‖ * ‖z‖ ^ F.P.natDegree / 2 := by
    have := F.leadingCoeff_norm_pos
    have : 0 < ‖z‖ := by linarith
    positivity
  exact norm_pos_iff.mp (lt_of_lt_of_le this h)

lemma Y₀_le_norm {b : ℂ} (hy : F.Y₀ ≤ b.im) : F.Y₀ ≤ ‖b‖ :=
  hy.trans ((le_abs_self _).trans (Complex.abs_im_le_norm b))

/-- `P(b) ≠ 0` for `Im b ≥ Y₀`. -/
theorem P_eval_ne_zero {b : ℂ} (hy : F.Y₀ ≤ b.im) : F.P.eval b ≠ 0 :=
  F.P_eval_ne_zero_of_norm (by linarith [F.Y₀_le_norm hy, F.two_le_Y₀])
    (F.RP_le_Y₀.trans (F.Y₀_le_norm hy))

/-- Near-field polynomial ratio: `‖ρ_F − 1‖ ≤ C_P ‖δ‖ / ‖b‖` for `‖δ‖ ≤ ‖b‖`, `‖b‖ ≥ max(1, R_P)`. -/
theorem norm_ρF_sub_one_le {b δ : ℂ} (hb1 : 1 ≤ ‖b‖) (hbR : F.RP ≤ ‖b‖) (hδ : ‖δ‖ ≤ ‖b‖) :
    ‖F.ρF b δ - 1‖ ≤ F.CP * ‖δ‖ / ‖b‖ := by
  have hP := F.P_eval_ne_zero_of_norm hb1 hbR
  have hPpos : 0 < ‖F.P.eval b‖ := norm_pos_iff.mpr hP
  have hbpos : 0 < ‖b‖ := by linarith
  have hlead := F.leadingCoeff_norm_pos
  have heq : F.ρF b δ - 1 = (F.P.eval (b + δ) - F.P.eval b) / F.P.eval b := by
    rw [ρF]; field_simp
  rw [heq, norm_div, div_le_div_iff₀ hPpos hbpos]
  have hδ0 := norm_nonneg δ
  have hM : 1 ≤ ‖b‖ + ‖δ‖ := by linarith
  have hdiff := F.norm_P_eval_sub_le b δ hM
  have hlow := F.norm_P_eval_ge hb1 hbR
  have hMle : (‖b‖ + ‖δ‖) ^ F.P.natDegree ≤ 2 ^ F.P.natDegree * ‖b‖ ^ F.P.natDegree := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hCP : F.CP * ‖F.P.leadingCoeff‖ / 2 = 2 ^ F.P.natDegree * F.P.natDegree * F.SP := by
    unfold CP; field_simp; ring
  have hN0 := norm_nonneg (F.P.eval (b + δ) - F.P.eval b)
  have hSP := F.SP_nonneg
  have hCP0 := F.CP_nonneg
  have hd0 : (0 : ℝ) ≤ F.P.natDegree := Nat.cast_nonneg _
  calc ‖F.P.eval (b + δ) - F.P.eval b‖ * ‖b‖
      ≤ ‖F.P.eval (b + δ) - F.P.eval b‖ * (‖b‖ + ‖δ‖) := by gcongr; linarith
    _ ≤ F.SP * F.P.natDegree * ‖δ‖ * (‖b‖ + ‖δ‖) ^ F.P.natDegree := hdiff
    _ ≤ F.SP * F.P.natDegree * ‖δ‖ * (2 ^ F.P.natDegree * ‖b‖ ^ F.P.natDegree) := by gcongr
    _ = F.CP * ‖δ‖ * (‖F.P.leadingCoeff‖ * ‖b‖ ^ F.P.natDegree / 2) := by
        rw [show F.CP * ‖δ‖ * (‖F.P.leadingCoeff‖ * ‖b‖ ^ F.P.natDegree / 2) =
          (F.CP * ‖F.P.leadingCoeff‖ / 2) * ‖δ‖ * ‖b‖ ^ F.P.natDegree by ring, hCP]
        ring
    _ ≤ F.CP * ‖δ‖ * ‖F.P.eval b‖ := by gcongr

/-- Global polynomial ratio: `‖ρ_F‖ ≤ R_P (1 + ‖δ‖)^d` for `‖b‖ ≥ max(1, R_P)`. -/
theorem norm_ρF_le {b δ : ℂ} (hb1 : 1 ≤ ‖b‖) (hbR : F.RP ≤ ‖b‖) :
    ‖F.ρF b δ‖ ≤ F.RP * (1 + ‖δ‖) ^ F.P.natDegree := by
  have hP := F.P_eval_ne_zero_of_norm hb1 hbR
  have hPpos : 0 < ‖F.P.eval b‖ := norm_pos_iff.mpr hP
  have hlead := F.leadingCoeff_norm_pos
  have hδ0 := norm_nonneg δ
  rw [ρF, norm_div, div_le_iff₀ hPpos]
  have hup := F.norm_P_eval_le (z := b + δ) (M := ‖b‖ + ‖δ‖) (by linarith) (norm_add_le _ _)
  have hlow := F.norm_P_eval_ge hb1 hbR
  have hMle : (‖b‖ + ‖δ‖) ^ F.P.natDegree ≤
      ‖b‖ ^ F.P.natDegree * (1 + ‖δ‖) ^ F.P.natDegree := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by nlinarith) _
  have hRP : F.RP * ‖F.P.leadingCoeff‖ / 2 = F.SP := by unfold RP; field_simp
  have hSP := F.SP_nonneg
  have hRP2 := F.two_le_RP
  calc ‖F.P.eval (b + δ)‖ ≤ F.SP * (‖b‖ + ‖δ‖) ^ F.P.natDegree := hup
    _ ≤ F.SP * (‖b‖ ^ F.P.natDegree * (1 + ‖δ‖) ^ F.P.natDegree) := by gcongr
    _ = F.RP * (1 + ‖δ‖) ^ F.P.natDegree * (‖F.P.leadingCoeff‖ * ‖b‖ ^ F.P.natDegree / 2) := by
        rw [← hRP]; ring
    _ ≤ F.RP * (1 + ‖δ‖) ^ F.P.natDegree * ‖F.P.eval b‖ := by gcongr

/-! ### The Gamma arguments `w_j = λ_j b + μ_j` and increments `v_j = λ_j δ` -/

lemma w_add_eq (b δ : ℂ) (j : Fin F.r) :
    F.lam j * (b + δ) + F.mu j = (F.lam j * b + F.mu j) + F.lam j * δ := by ring

lemma norm_v_eq (δ : ℂ) (j : Fin F.r) : ‖(F.lam j : ℂ) * δ‖ = F.lam j * ‖δ‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (F.lam_pos j)]

lemma re_w_ge {b : ℂ} (hb2 : 2 ≤ b.re) (j : Fin F.r) :
    2 * F.lam j ≤ (F.lam j * b + F.mu j).re := by
  have h1 : (F.lam j * b + F.mu j).re = F.lam j * b.re + (F.mu j).re := by simp
  rw [h1]
  have := F.lam_pos j
  have := F.mu_re_nonneg j
  nlinarith

lemma re_w_add_ge {b δ : ℂ} (hb2 : 2 ≤ b.re) (hδre : 0 ≤ δ.re) (j : Fin F.r) :
    2 * F.lam j ≤ (F.lam j * b + F.mu j + F.lam j * δ).re := by
  have h1 : (F.lam j * b + F.mu j + F.lam j * δ).re =
      F.lam j * b.re + (F.mu j).re + F.lam j * δ.re := by simp
  rw [h1]
  have := F.lam_pos j
  have := F.mu_re_nonneg j
  nlinarith

lemma re_w_add_le {b δ : ℂ} (hb4 : b.re ≤ 4) (j : Fin F.r) :
    (F.lam j * b + F.mu j + F.lam j * δ).re ≤ F.lam j * (4 + δ.re) + (F.mu j).re := by
  have h1 : (F.lam j * b + F.mu j + F.lam j * δ).re =
      F.lam j * b.re + (F.mu j).re + F.lam j * δ.re := by simp
  rw [h1]
  have := F.lam_pos j
  nlinarith

lemma im_w_ge {b : ℂ} (hy : F.Y₀ ≤ b.im) (j : Fin F.r) :
    3 / 4 * (F.lam j * b.im) ≤ (F.lam j * b + F.mu j).im := by
  have h1 : (F.lam j * b + F.mu j).im = F.lam j * b.im + (F.mu j).im := by simp
  rw [h1]
  have := F.four_abs_im_mu_le hy j
  have := neg_abs_le (F.mu j).im
  linarith

lemma im_w_pos {b : ℂ} (hy : F.Y₀ ≤ b.im) (j : Fin F.r) : 0 < (F.lam j * b + F.mu j).im := by
  have := F.im_w_ge hy j
  have := F.lam_pos j
  have hy2 : 0 < b.im := by linarith [F.two_le_Y₀]
  nlinarith

lemma norm_w_ge {b : ℂ} (hy : F.Y₀ ≤ b.im) (j : Fin F.r) :
    3 / 4 * (F.lam j * b.im) ≤ ‖F.lam j * b + F.mu j‖ :=
  (F.im_w_ge hy j).trans ((le_abs_self _).trans (Complex.abs_im_le_norm _))

lemma norm_w_le {b : ℂ} (hb2 : 2 ≤ b.re) (hb4 : b.re ≤ 4) (hy : F.Y₀ ≤ b.im) (j : Fin F.r) :
    ‖F.lam j * b + F.mu j‖ ≤ F.lam j * (4 + b.im) + ‖F.mu j‖ := by
  have hl := F.lam_pos j
  have hb : ‖b‖ ≤ 4 + b.im := by
    have := Complex.norm_le_abs_re_add_abs_im b
    rw [abs_of_pos (by linarith : 0 < b.re),
      abs_of_pos (by linarith [F.two_le_Y₀] : 0 < b.im)] at this
    linarith
  calc ‖F.lam j * b + F.mu j‖ ≤ ‖(F.lam j : ℂ) * b‖ + ‖F.mu j‖ := norm_add_le _ _
    _ = F.lam j * ‖b‖ + ‖F.mu j‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl]
    _ ≤ F.lam j * (4 + b.im) + ‖F.mu j‖ := by gcongr

lemma im_w_add_ge {b δ : ℂ} (hy : F.Y₀ ≤ b.im) (hδim : -(b.im / 2) ≤ δ.im) (j : Fin F.r) :
    F.lam j * b.im / 4 ≤ (F.lam j * b + F.mu j + F.lam j * δ).im := by
  have h1 : (F.lam j * b + F.mu j + F.lam j * δ).im =
      F.lam j * b.im + (F.mu j).im + F.lam j * δ.im := by simp
  rw [h1]
  have := F.four_abs_im_mu_le hy j
  have := neg_abs_le (F.mu j).im
  have hl := F.lam_pos j
  nlinarith

lemma abs_im_w_add_le (b δ : ℂ) (j : Fin F.r) :
    |(F.lam j * b + F.mu j + F.lam j * δ).im| ≤ F.lam j * (|b.im| + |δ.im|) + |(F.mu j).im| := by
  have hl := F.lam_pos j
  have h1 : (F.lam j * b + F.mu j + F.lam j * δ).im =
      F.lam j * (b.im + δ.im) + (F.mu j).im := by simp; ring
  rw [h1]
  calc |F.lam j * (b.im + δ.im) + (F.mu j).im|
      ≤ |F.lam j * (b.im + δ.im)| + |(F.mu j).im| := abs_add_le _ _
    _ = F.lam j * |b.im + δ.im| + |(F.mu j).im| := by rw [abs_mul, abs_of_pos hl]
    _ ≤ F.lam j * (|b.im| + |δ.im|) + |(F.mu j).im| := by gcongr; exact abs_add_le _ _

/-! ### Near field -/

/-- `‖Q_F(δ)‖ ≤ C_Q (1 + ‖δ‖)² / Im b` for `‖δ‖ ≤ Im b / 2`, `Re δ ≥ 0`. -/
theorem norm_QF_le_near {b δ : ℂ} (hb2 : 2 ≤ b.re) (hy : F.Y₀ ≤ b.im) (hδre : 0 ≤ δ.re)
    (hδn : ‖δ‖ ≤ b.im / 2) : ‖F.QF b δ‖ ≤ F.CQ * (1 + ‖δ‖) ^ 2 / b.im := by
  have hypos : 0 < b.im := by linarith [F.two_le_Y₀]
  have hδim : -(b.im / 2) ≤ δ.im := by
    have := neg_abs_le δ.im
    have := Complex.abs_im_le_norm δ
    linarith
  have hδ0 := norm_nonneg δ
  rw [QF, CQ, Finset.sum_mul, Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hl := F.lam_pos j
  have hwre : 0 < (F.lam j * b + F.mu j).re := by linarith [F.re_w_ge hb2 j]
  have hwvre : 0 < (F.lam j * b + F.mu j + F.lam j * δ).re := by
    linarith [F.re_w_add_ge hb2 hδre j]
  have hwim := F.im_w_pos hy j
  have hwvim : 0 < (F.lam j * b + F.mu j + F.lam j * δ).im := by
    have := F.im_w_add_ge hy hδim j
    have : 0 < F.lam j * b.im / 4 := by positivity
    linarith
  have hwn := F.norm_w_ge hy j
  have hwpos : 0 < ‖F.lam j * b + F.mu j‖ := lt_of_lt_of_le (by positivity) hwn
  have hvn := F.norm_v_eq δ j
  have hv : ‖(F.lam j : ℂ) * δ‖ ≤ 2 / 3 * ‖F.lam j * b + F.mu j‖ := by
    rw [hvn]; nlinarith
  rw [F.w_add_eq b δ j]
  refine (norm_Qj_le_near hwre hwvre hwim hwvim hv).trans ?_
  rw [hvn, div_mul_eq_mul_div, div_div, div_le_div_iff₀ hwpos (by positivity)]
  have hsq : (1 + F.lam j * ‖δ‖) ^ 2 ≤ (1 + F.lam j) ^ 2 * (1 + ‖δ‖) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by nlinarith) 2
  nlinarith [mul_le_mul_of_nonneg_left hwn (by positivity : (0 : ℝ) ≤ 6 * (1 + F.lam j) ^ 2 * (1 + ‖δ‖) ^ 2),
    mul_le_mul_of_nonneg_right hsq (by positivity : (0 : ℝ) ≤ F.lam j * b.im)]

/-- **Near-field estimate**: for `‖δ‖ ≤ Im b / 2`, `Re δ ≥ 0`, `Re b ≥ 2`, `Im b ≥ Y₀`,
`‖K − 1‖ ≤ C_N (1+‖δ‖)²/y · exp(C_N (1+‖δ‖)²/y)`. -/
theorem norm_KF_sub_one_le {b δ : ℂ} (hb2 : 2 ≤ b.re) (hy : F.Y₀ ≤ b.im) (hδre : 0 ≤ δ.re)
    (hδn : ‖δ‖ ≤ b.im / 2) :
    ‖F.ρF b δ * cexp (F.QF b δ) - 1‖ ≤
      F.CN * (1 + ‖δ‖) ^ 2 / b.im * Real.exp (F.CN * (1 + ‖δ‖) ^ 2 / b.im) := by
  have hypos : 0 < b.im := by linarith [F.two_le_Y₀]
  have hbn : b.im ≤ ‖b‖ := (le_abs_self _).trans (Complex.abs_im_le_norm b)
  have hb1 : 1 ≤ ‖b‖ := by linarith [F.two_le_Y₀]
  have hbR : F.RP ≤ ‖b‖ := F.RP_le_Y₀.trans (hy.trans hbn)
  have hbpos : 0 < ‖b‖ := by linarith
  have hδ0 := norm_nonneg δ
  have hCP := F.CP_nonneg
  have hCQ := F.CQ_nonneg
  have hCN : F.CN = 1 + F.CP + F.CQ := rfl
  set Y : ℝ := (1 + ‖δ‖) ^ 2 / b.im with hY
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hQ : ‖F.QF b δ‖ ≤ F.CQ * Y := by
    refine (F.norm_QF_le_near hb2 hy hδre hδn).trans (le_of_eq ?_)
    rw [hY]; ring
  have hρ : ‖F.ρF b δ - 1‖ ≤ F.CP * Y := by
    refine (F.norm_ρF_sub_one_le hb1 hbR (by linarith)).trans ?_
    rw [hY]
    calc F.CP * ‖δ‖ / ‖b‖ ≤ F.CP * ‖δ‖ / b.im := by gcongr
      _ ≤ F.CP * ((1 + ‖δ‖) ^ 2 / b.im) := by
          rw [← mul_div_assoc]
          refine div_le_div_of_nonneg_right ?_ hypos.le
          exact mul_le_mul_of_nonneg_left (by nlinarith) hCP
  have hQX : ‖F.QF b δ‖ ≤ F.CN * Y := by
    refine hQ.trans ?_
    rw [hCN]; nlinarith
  have hexpQ : ‖cexp (F.QF b δ)‖ ≤ Real.exp (F.CN * Y) := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hQX)
  have hE : ‖cexp (F.QF b δ) - 1‖ ≤ F.CQ * Y * Real.exp (F.CN * Y) := by
    refine (norm_exp_sub_one_le_mul_exp _).trans ?_
    exact mul_le_mul hQ (Real.exp_le_exp.mpr hQX) (Real.exp_pos _).le (by positivity)
  have hfinal : F.CP * Y * Real.exp (F.CN * Y) + F.CQ * Y * Real.exp (F.CN * Y) ≤
      F.CN * Y * Real.exp (F.CN * Y) := by
    have hE0 : 0 ≤ Y * Real.exp (F.CN * Y) := mul_nonneg hY0 (Real.exp_pos _).le
    have hle : F.CP + F.CQ ≤ F.CN := by rw [hCN]; linarith
    nlinarith [mul_le_mul_of_nonneg_right hle hE0]
  calc ‖F.ρF b δ * cexp (F.QF b δ) - 1‖
      = ‖(F.ρF b δ - 1) * cexp (F.QF b δ) + (cexp (F.QF b δ) - 1)‖ := by ring_nf
    _ ≤ ‖(F.ρF b δ - 1) * cexp (F.QF b δ)‖ + ‖cexp (F.QF b δ) - 1‖ := norm_add_le _ _
    _ ≤ F.CP * Y * Real.exp (F.CN * Y) + F.CQ * Y * Real.exp (F.CN * Y) := by
        rw [norm_mul]
        exact add_le_add (mul_le_mul hρ hexpQ (norm_nonneg _) (by positivity)) hE
    _ ≤ F.CN * Y * Real.exp (F.CN * Y) := hfinal
    _ = F.CN * (1 + ‖δ‖) ^ 2 / b.im * Real.exp (F.CN * (1 + ‖δ‖) ^ 2 / b.im) := by
        rw [hY]; ring_nf

/-! ### Global -/

/-- Global bound for the `j`-th summand of `Q_F`. -/
theorem re_Qj_le {b δ : ℂ} (hb2 : 2 ≤ b.re) (hb4 : b.re ≤ 4) (hy : F.Y₀ ≤ b.im) (hδre : 0 ≤ δ.re)
    (j : Fin F.r) :
    (L (F.lam j * (b + δ) + F.mu j) - L (F.lam j * b + F.mu j) -
        (F.lam j : ℂ) * δ * log (F.lam j * b + F.mu j)).re ≤
      4 / 3 * (5 * F.lam j + (F.mu j).re) * (1 + δ.re) * ‖δ‖ / b.im +
        π * F.lam j * (b.im + |δ.im|) +
        (π / 2 * |(F.mu j).im| + F.lam j + ‖F.mu j‖ / 4 + |Real.log (F.lam j)| / 2 +
          1 / (4 * F.lam j)) := by
  have hl := F.lam_pos j
  have hmu := F.mu_re_nonneg j
  have hypos : 0 < b.im := by linarith [F.two_le_Y₀]
  have hδ0 := norm_nonneg δ
  have hwre2 := F.re_w_ge hb2 j
  have hwre : 0 < (F.lam j * b + F.mu j).re := by linarith
  have hwvre2 := F.re_w_add_ge hb2 hδre j
  have hwvre : 0 < (F.lam j * b + F.mu j + F.lam j * δ).re := by linarith
  have hwvre_le := F.re_w_add_le (δ := δ) hb4 j
  have hwim := F.im_w_pos hy j
  have hwn := F.norm_w_ge hy j
  have hwpos : 0 < ‖F.lam j * b + F.mu j‖ := lt_of_lt_of_le (by positivity) hwn
  have hwle := F.norm_w_le hb2 hb4 hy j
  have hwvn : 2 * F.lam j ≤ ‖F.lam j * b + F.mu j + F.lam j * δ‖ :=
    hwvre2.trans (Complex.re_le_norm _)
  have hwvpos : 0 < ‖F.lam j * b + F.mu j + F.lam j * δ‖ := by linarith
  have hvn := F.norm_v_eq δ j
  have hvre : ((F.lam j : ℂ) * δ).re = F.lam j * δ.re := by simp
  have habs := F.abs_im_w_add_le b δ j
  rw [abs_of_pos hypos] at habs
  rw [F.w_add_eq b δ j]
  refine (re_Qj_le_raw hwre hwvre hwim).trans ?_
  -- the `Re(w+v) ‖v‖/‖w‖` term
  have hvw : ‖(F.lam j : ℂ) * δ‖ / ‖F.lam j * b + F.mu j‖ ≤ 4 / 3 * ‖δ‖ / b.im := by
    rw [hvn, div_le_div_iff₀ hwpos hypos]
    nlinarith [mul_le_mul_of_nonneg_left hwn hδ0]
  have hP1 : (F.lam j * b + F.mu j + F.lam j * δ).re *
      (‖(F.lam j : ℂ) * δ‖ / ‖F.lam j * b + F.mu j‖) ≤
      4 / 3 * (5 * F.lam j + (F.mu j).re) * (1 + δ.re) * ‖δ‖ / b.im := by
    calc (F.lam j * b + F.mu j + F.lam j * δ).re *
          (‖(F.lam j : ℂ) * δ‖ / ‖F.lam j * b + F.mu j‖)
        ≤ (F.lam j * (4 + δ.re) + (F.mu j).re) * (4 / 3 * ‖δ‖ / b.im) :=
          mul_le_mul hwvre_le hvw (by positivity) (by positivity)
      _ ≤ ((5 * F.lam j + (F.mu j).re) * (1 + δ.re)) * (4 / 3 * ‖δ‖ / b.im) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          nlinarith
      _ = 4 / 3 * (5 * F.lam j + (F.mu j).re) * (1 + δ.re) * ‖δ‖ / b.im := by ring
  -- the `(π/2) |Im(w+v)|` term
  have hP2 : π / 2 * |(F.lam j * b + F.mu j + F.lam j * δ).im| ≤
      π / 2 * (F.lam j * (b.im + |δ.im|) + |(F.mu j).im|) :=
    mul_le_mul_of_nonneg_left habs (by positivity)
  -- the `(1/2) log(‖w‖/‖w+v‖)` term
  have hratio : F.lam j * (‖F.lam j * b + F.mu j‖ / ‖F.lam j * b + F.mu j + F.lam j * δ‖) ≤
      (F.lam j * (4 + b.im) + ‖F.mu j‖) / 2 := by
    rw [← mul_div_assoc, div_le_div_iff₀ hwvpos two_pos]
    nlinarith [mul_le_mul hwle hwvn (by positivity) (by positivity)]
  have hlog : Real.log (‖F.lam j * b + F.mu j‖ / ‖F.lam j * b + F.mu j + F.lam j * δ‖) ≤
      F.lam j * (‖F.lam j * b + F.mu j‖ / ‖F.lam j * b + F.mu j + F.lam j * δ‖) - 1 -
        Real.log (F.lam j) := by
    have hq : 0 < ‖F.lam j * b + F.mu j‖ / ‖F.lam j * b + F.mu j + F.lam j * δ‖ :=
      div_pos hwpos hwvpos
    have h := Real.log_le_sub_one_of_pos (mul_pos hl hq)
    rw [Real.log_mul hl.ne' hq.ne'] at h
    linarith
  have hP3 : 1 / 2 * Real.log (‖F.lam j * b + F.mu j‖ / ‖F.lam j * b + F.mu j + F.lam j * δ‖) ≤
      F.lam j + F.lam j * b.im / 4 + ‖F.mu j‖ / 4 + |Real.log (F.lam j)| / 2 := by
    have := neg_le_abs (Real.log (F.lam j))
    linarith
  -- `−Re v ≤ 0`
  have hP4 : 0 ≤ ((F.lam j : ℂ) * δ).re := by rw [hvre]; positivity
  -- the Stirling remainders
  have hP5a : 1 / (4 * ‖F.lam j * b + F.mu j + F.lam j * δ‖) ≤ 1 / (8 * F.lam j) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hP5b : 1 / (4 * ‖F.lam j * b + F.mu j‖) ≤ 1 / (8 * F.lam j) :=
    one_div_le_one_div_of_le (by positivity)
      (by linarith [hwre2.trans (Complex.re_le_norm _)])
  have hP5 : 1 / (8 * F.lam j) + 1 / (8 * F.lam j) = 1 / (4 * F.lam j) := by
    field_simp; ring
  -- slack between `(π/2 + 1/4) λ y` and `π λ y`
  have hslack : 0 ≤ (π / 2 - 1 / 4) * (F.lam j * b.im) :=
    mul_nonneg (by linarith [Real.pi_gt_three]) (by positivity)
  have hslack2 : 0 ≤ π / 2 * (F.lam j * |δ.im|) := by positivity
  linarith [hP1, hP2, hP3, hP4, hP5a, hP5b, hP5, hslack, hslack2]

/-- **Global estimate for `Re Q_F`**. -/
theorem re_QF_le {b δ : ℂ} (hb2 : 2 ≤ b.re) (hb4 : b.re ≤ 4) (hy : F.Y₀ ≤ b.im)
    (hδre : 0 ≤ δ.re) :
    (F.QF b δ).re ≤
      F.AG * (1 + δ.re) * ‖δ‖ / b.im + π * (∑ j, F.lam j) * (b.im + |δ.im|) + F.BG := by
  have hR : F.AG * (1 + δ.re) * ‖δ‖ / b.im + π * (∑ j, F.lam j) * (b.im + |δ.im|) + F.BG =
      ∑ j, (4 / 3 * (5 * F.lam j + (F.mu j).re) * (1 + δ.re) * ‖δ‖ / b.im +
        π * F.lam j * (b.im + |δ.im|) +
        (π / 2 * |(F.mu j).im| + F.lam j + ‖F.mu j‖ / 4 + |Real.log (F.lam j)| / 2 +
          1 / (4 * F.lam j))) := by
    simp only [AG, BG, Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_div, Finset.mul_sum]
  rw [hR, QF, Complex.re_sum]
  exact Finset.sum_le_sum fun j _ => F.re_Qj_le hb2 hb4 hy hδre j

/-- **Global estimate for `K`**. -/
theorem norm_KF_le {b δ : ℂ} (hb2 : 2 ≤ b.re) (hb4 : b.re ≤ 4) (hy : F.Y₀ ≤ b.im)
    (hδre : 0 ≤ δ.re) :
    ‖F.ρF b δ * cexp (F.QF b δ)‖ ≤ F.RP * (1 + ‖δ‖) ^ F.P.natDegree *
      Real.exp (F.AG * (1 + δ.re) * ‖δ‖ / b.im + π * (∑ j, F.lam j) * (b.im + |δ.im|) + F.BG) := by
  have hbn : b.im ≤ ‖b‖ := (le_abs_self _).trans (Complex.abs_im_le_norm b)
  have hb1 : 1 ≤ ‖b‖ := by linarith [F.two_le_Y₀]
  have hbR : F.RP ≤ ‖b‖ := F.RP_le_Y₀.trans (hy.trans hbn)
  have hRP := F.two_le_RP
  rw [norm_mul, Complex.norm_exp]
  exact mul_le_mul (F.norm_ρF_le hb1 hbR) (Real.exp_le_exp.mpr (F.re_QF_le hb2 hb4 hy hδre))
    (Real.exp_pos _).le (by positivity)

/-! ### The majorants and the unified pointwise bound -/

/-- The near-field majorant. -/
noncomputable def NbF (y h σ : ℝ) : ℝ :=
  F.CN * (1 + h + |σ|) ^ (F.P.natDegree + 2) / y * Real.exp (F.CN * (1 + h + |σ|) ^ 2 / y)

/-- The far-field majorant. -/
noncomputable def GbF (y h σ : ℝ) : ℝ :=
  F.CG * (1 + h + |σ|) ^ (F.P.natDegree + 2) *
    Real.exp (F.CG * (1 + h) * (h + |σ|) / y + π * (∑ j, F.lam j) * (y + |σ|) + F.CG)

lemma NbF_nonneg {y : ℝ} (hy : 0 ≤ y) {h : ℝ} (hh0 : 0 ≤ h) (σ : ℝ) : 0 ≤ F.NbF y h σ := by
  unfold NbF
  have := F.CN_nonneg
  positivity

lemma GbF_nonneg (y : ℝ) {h : ℝ} (hh0 : 0 ≤ h) (σ : ℝ) : 0 ≤ F.GbF y h σ := by
  unfold GbF
  have := F.CG_nonneg
  positivity

/-- **Unified pointwise bound**: for `2 ≤ Re b ≤ 4`, `y = Im b ≥ Y₀`, `δ = h + iσ` with `h ≥ 0`,
    `‖ρ_F e^{Q_F} − 1‖ ≤ NbF y h σ + e^{((h+|σ|)² − y²/4)/(8c)} (1 + GbF y h σ)`. -/
theorem norm_KF_sub_one_le_unified {c : ℝ} (hc : 0 < c) {b : ℂ} (hb2 : 2 ≤ b.re) (hb4 : b.re ≤ 4)
    (hy : F.Y₀ ≤ b.im) {h : ℝ} (hh0 : 0 ≤ h) (σ : ℝ) :
    ‖F.ρF b (((h : ℝ) : ℂ) + σ * I) * cexp (F.QF b (((h : ℝ) : ℂ) + σ * I)) - 1‖ ≤
      F.NbF b.im h σ + Real.exp (((h + |σ|) ^ 2 - b.im ^ 2 / 4) / (8 * c)) *
        (1 + F.GbF b.im h σ) := by
  set δ : ℂ := ((h : ℝ) : ℂ) + σ * I with hδdef
  have hypos : 0 < b.im := by linarith [F.two_le_Y₀]
  have hδn : ‖δ‖ ≤ h + |σ| := norm_hδ_le hh0 σ
  have hδre : 0 ≤ δ.re := by simp [hδdef, hh0]
  have hδre' : δ.re = h := by simp [hδdef]
  have hδim : δ.im = σ := by simp [hδdef]
  have hNb := F.NbF_nonneg hypos.le hh0 σ
  have hGb := F.GbF_nonneg b.im hh0 σ
  have hbase : 1 ≤ 1 + h + |σ| := by linarith [abs_nonneg σ]
  have hδ0 := norm_nonneg δ
  have hCN := F.CN_nonneg
  by_cases hreg : h + |σ| ≤ b.im / 2
  · -- near field
    have hδb : ‖δ‖ ≤ b.im / 2 := hδn.trans hreg
    have hnear := F.norm_KF_sub_one_le hb2 hy hδre hδb
    have hsq2 : (1 + ‖δ‖) ^ 2 ≤ (1 + h + |σ|) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have hsq : (1 + ‖δ‖) ^ 2 ≤ (1 + h + |σ|) ^ (F.P.natDegree + 2) :=
      hsq2.trans (pow_le_pow_right₀ hbase (by omega))
    have hmono : F.CN * (1 + ‖δ‖) ^ 2 / b.im * Real.exp (F.CN * (1 + ‖δ‖) ^ 2 / b.im) ≤
        F.NbF b.im h σ := by
      unfold NbF
      refine mul_le_mul ?_ (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (by positivity)
      · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hCN) hypos.le
      · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq2 hCN) hypos.le
    calc _ ≤ _ := hnear
      _ ≤ F.NbF b.im h σ := hmono
      _ ≤ _ := le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le (by linarith))
  · -- far field
    push Not at hreg
    have hK := F.norm_KF_le hb2 hb4 hy hδre
    have hG : F.RP * (1 + ‖δ‖) ^ F.P.natDegree *
        Real.exp (F.AG * (1 + δ.re) * ‖δ‖ / b.im + π * (∑ j, F.lam j) * (b.im + |δ.im|) + F.BG) ≤
        F.GbF b.im h σ := by
      unfold GbF
      have hCG := F.CG_nonneg
      have hRP := F.two_le_RP
      have hAG := F.AG_nonneg
      have hBG := F.BG_nonneg
      have hCGdef : F.CG = 1 + F.RP + F.AG + F.BG := rfl
      refine mul_le_mul ?_ (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (by positivity)
      · refine mul_le_mul (by linarith) ?_ (by positivity) (by linarith)
        calc (1 + ‖δ‖) ^ F.P.natDegree ≤ (1 + h + |σ|) ^ F.P.natDegree :=
              pow_le_pow_left₀ (by positivity) (by linarith) _
          _ ≤ (1 + h + |σ|) ^ (F.P.natDegree + 2) := pow_le_pow_right₀ hbase (by omega)
      · rw [hδre', hδim]
        have h1 : F.AG * (1 + h) * ‖δ‖ / b.im ≤ F.CG * (1 + h) * (h + |σ|) / b.im := by
          refine div_le_div_of_nonneg_right ?_ hypos.le
          have : F.AG * (1 + h) ≤ F.CG * (1 + h) := by nlinarith
          exact mul_le_mul this hδn hδ0 (by positivity)
        linarith
    have hone : 1 ≤ Real.exp (((h + |σ|) ^ 2 - b.im ^ 2 / 4) / (8 * c)) := by
      rw [Real.one_le_exp_iff]
      have : b.im / 2 < h + |σ| := hreg
      have h0 : 0 ≤ b.im / 2 := by positivity
      apply div_nonneg _ (by positivity)
      nlinarith
    calc ‖F.ρF b δ * cexp (F.QF b δ) - 1‖ ≤ ‖F.ρF b δ * cexp (F.QF b δ)‖ + 1 := by
          have := norm_sub_le (F.ρF b δ * cexp (F.QF b δ)) 1
          rwa [norm_one] at this
      _ ≤ F.GbF b.im h σ + 1 := by linarith [hK.trans hG]
      _ ≤ Real.exp (((h + |σ|) ^ 2 - b.im ^ 2 / 4) / (8 * c)) * (1 + F.GbF b.im h σ) := by
          nlinarith
      _ ≤ _ := le_add_of_nonneg_left hNb

end ExtSelbergData

end DBNSelberg
