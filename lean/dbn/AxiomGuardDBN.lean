/-
  AxiomGuardDBN -- CI axiom guard for the Route C (de Bruijn-Newman) foundations island.

  Run as `lake env lean AxiomGuardDBN.lean | tee axioms.out; ! grep -q sorryAx axioms.out`.
  Every theorem/lemma of every island module gets a `#print axioms` line; the expected closure
  is `[propext, Classical.choice, Quot.sound]` (definitions like `thetaMoment`/`Φ`/`H`/`g`/`psi`
  are noncomputable and are covered through the theorems that mention them).

  Scope reminder.  The C2 representation theorem H_0 = ξ/8 (registry node RH.dbn_H0_eq_xi) IS an
  island theorem: `dbn_H0_eq_xi` in DBNXi (module E), assembled from DBNXiRiemann (module A:
  Riemann's symmetric integral for Mathlib's entire completedRiemannZeta₀), DBNXiCos (module B:
  the substitution x = e^{4u}), DBNGKernel (module C: the kernel g(u) = e^u psi(e^{4u}),
  g'' - g = 8 Phi, g'(0) = -1/2, decay and integration-by-parts side conditions) and DBNXiIBP
  (module D: two integrations by parts).  It is an identity between two entire functions, NOT
  RH-equivalent, and says nothing about where any zero lies.  DBNRealZerosIff proves the C4
  bridge RH <-> (all zeros of H_0 real) conditionally on C2 (explicit hypothesis / the named Prop
  obligation DBN.H0EqXi); DBNRealZerosIffFinal specialises it at `dbn_H0_eq_xi`, which gives the
  registry statement of RH.dbn_rh_iff_H0_real_zeros unconditionally.  That is an equivalence
  between two restatements of the same OPEN conjecture: it proves neither side.  NOTHING here is
  de Bruijn's t ≥ 1/2 theorem (registry node RH.dbn_debruijn_real_zeros, a registry STATEMENT,
  not an island theorem) or RH.  conjecture1_proved = False.
-/
import DBNDefs
import DBNRealZerosIff
import DBNXiRiemann
import DBNGKernel
import DBNXiCos
import DBNXiIBP
import DBNXi
import DBNRealZerosIffFinal
import DBNStrip
import DBNStep
import DBNStepControls
import DBNHurwitz
import DBNHeatApprox
import DBNDeBruijnReduction
import DBNHadamardCount
import DBNHadamardProduct
import DBNHadamardMean
import DBNHadamardLinear
import DBNHadamard
import DBNHadamardApprox
import DBNM1Approx
import DBNM1Parametric
import DBNM1RHIff
import DBNM1Controls
import DBNM4P15Defs
import DBNM4LocalStep
import DBNM4HeatUniform
import DBNM4P15Criterion
import M6gapEMZeta
import M6gapEMZetaComplex
import M6gapEMZetaTail
import M6gapZetaEMSum
import M6gapHeightFloorCheck
import M6gapHeightFloorTrig
import M6gapHeightFloorEM
import M6gapHeightFloorBoxes
import M6gapZetaZeroConfinement
import M6gapDlvpZetaSymmetry
import M6gapHeightFloor
import M6gapImAxis
import M6gapP15ZeroFree
import DBNM5Alpha
import DBNM5Target
import DBNP15Wired
import DBNZeroFreeHalfplane
import DBNBohr
import DBNFtZero
import DBNFtZeroHigh
import DBNStirling
import DBNGaussConv
import DBNSaddleAlg
import DBNSaddleBounds
import DBNSaddleSum
import DBNTheorem4
import DBNNewman
import DBNTheorem4Effective
import DBNSelbergData
import DBNSelbergGauss
import DBNSelbergSaddleAlg
import DBNSelbergSaddleBounds
import DBNSelbergFtZero
import DBNSelbergSaddleSum
import DBNSelbergNewman
import DBNSelbergZeta
import DBNGammaVertical
import DBNSelbergSharp
import DBNSelbergSharpXi
import DBNSelbergSharpStrip

-- theta moments
#print axioms DBN.summable_thetaTerm
#print axioms DBN.summable_thetaMoment
#print axioms DBN.hasDerivAt_thetaMoment
#print axioms DBN.continuous_thetaMoment
#print axioms DBN.ofReal_thetaMoment_zero
#print axioms DBN.thetaMoment_zero_fe
#print axioms DBN.thetaMoment_fe_deriv1
#print axioms DBN.thetaMoment_fe_deriv2

-- Φ
#print axioms DBN.summable_thetaTerm_pnat
#print axioms DBN.summable_Φ_term
#print axioms DBN.thetaMoment_eq_two_mul_pnat
#print axioms DBN.Φ_eq
#print axioms DBN.Φ_neg
#print axioms DBN.Φ_even
#print axioms DBN.continuous_Φ

-- decay
#print axioms DBN.ΦBoundConst_nonneg
#print axioms DBN.summable_ΦBoundConst_term
#print axioms DBN.abs_Φ_le

-- integrability of the heat-flow integrand
#print axioms DBN.integrableOn_exp_quad_mul_exp_neg_exp
#print axioms DBN.norm_cos_le_exp_norm
#print axioms DBN.continuous_HIntegrand
#print axioms DBN.integrableOn_HIntegrand

-- H_t
#print axioms DBN.H_neg
#print axioms DBN.H_ofReal
#print axioms DBN.H_ofReal_im

-- ξ vocabulary bridge
#print axioms DBN.riemannXi_eq_completedRiemannZeta

-- H_t is entire
#print axioms DBN.norm_sin_le_exp_norm
#print axioms DBN.hasDerivAt_HIntegrand
#print axioms DBN.continuous_HIntegrand'
#print axioms DBN.hasDerivAt_H
#print axioms DBN.differentiable_H

-- Route C / C4 bridge (DBNRealZerosIff): change of variables + upstream unpacking (unconditional)
#print axioms DBN.xiArg_re
#print axioms DBN.xiArg_re_eq_half_iff
#print axioms DBN.xiArg_surj
#print axioms DBN.xiArgInv_im
#print axioms DBN.riemannXi_eq_zero_iff_strip_zero

-- Route C / C4 bridge, CONDITIONAL on C2 (hypothesis hC2 / obligation DBN.H0EqXi); the
-- expected closure is still [propext, Classical.choice, Quot.sound] because C2 is a hypothesis,
-- not an axiom.  These are NOT the registry theorem dbn_rh_iff_H0_real_zeros.
#print axioms DBN.H_zero_eq_zero_iff_of_H0_eq_xi
#print axioms dbn_rh_iff_H0_real_zeros_of_H0_eq_xi
#print axioms dbn_rh_iff_H0_real_zeros_of_obligation

-- Route C / C2 module A (DBNXiRiemann): ψ, the theta-kernel vocabulary bridges (N5), the
-- two-`Ioi 1`-integral formula for an arbitrary weak FE-pair (N1, N2), and Riemann's symmetric
-- integral for completedRiemannZeta₀ at every s (unconditional; NOT C2, NOT RH)
#print axioms DBN.summable_psi_term
#print axioms DBN.tsum_int_exp_eq_one_add_two_mul_psi
#print axioms DBN.thetaMoment_zero_eq_one_add_two_mul_psi
#print axioms DBN.thetaMoment_zero_eq_one_add_two_mul_pnat
#print axioms DBN.psi_exp_eq_thetaMoment
#print axioms DBN.psi_nonneg
#print axioms DBN.evenKernel_zero_eq_tsum
#print axioms DBN.evenKernel_zero_eq_one_add_two_mul_psi
#print axioms DBN.evenKernel_zero_eq_thetaMoment
#print axioms DBN.psi_eq_evenKernel
#print axioms DBN.continuousOn_psi
#print axioms DBN.weakFEPair_mellinConvergent_f_modif
#print axioms DBN.weakFEPair_f_modif_of_one_lt
#print axioms DBN.weakFEPair_integrableOn_Ioi_one
#print axioms DBN.mellin_indicator_Ioi_one
#print axioms DBN.weakFEPair_Λ₀_eq
#print axioms DBN.hurwitzEvenFEPair_zero_integrand
#print axioms DBN.integrableOn_psi_mul_cpow
#print axioms DBN.integral_hurwitzEvenFEPair_zero
#print axioms DBN.completedRiemannZeta₀_eq_integral_psi

-- C2 module C (DBNGKernel): the kernel g(u) = e^u psi(e^{4u}) of Riemann's symmetric
-- integral.  Ingredients of the representation theorem H_0 = xi/8, NOT the theorem itself.

-- DBNGKernel: N5 and the shared theta-moment decay helper
#print axioms DBN.thetaMoment_zero_sub_one_eq_two_mul_pnat
#print axioms DBN.thetaMoment_nonneg
#print axioms DBN.one_le_thetaMoment_zero
#print axioms DBN.thetaPnatConst_nonneg
#print axioms DBN.abs_thetaMoment_pnat_le
#print axioms DBN.thetaMoment_le_decay
#print axioms DBN.thetaMoment_zero_sub_one_le_decay

-- DBNGKernel: the kernel g and its closed-form derivatives
#print axioms DBN.g_eq_exp_mul_tsum_pnat
#print axioms DBN.g_nonneg
#print axioms DBN.hasDerivAt_g
#print axioms DBN.hasDerivAt_g'
#print axioms DBN.deriv_g
#print axioms DBN.deriv_g'
#print axioms DBN.continuous_g
#print axioms DBN.continuous_g'
#print axioms DBN.continuous_g''

-- DBNGKernel: kernel identity g'' - g = 8 Phi and g'(0) = -1/2
#print axioms DBN.g''_sub_g_eq
#print axioms DBN.g'_zero

-- DBNGKernel: decay bounds on u >= 0
#print axioms DBN.gKernelConst_nonneg
#print axioms DBN.abs_g_le
#print axioms DBN.abs_g'_le
#print axioms DBN.abs_g''_le

-- DBNGKernel: the atTop limit behind the island majorant
#print axioms DBN.tendsto_exp_quad_mul_exp_neg_exp
#print axioms DBN.tendsto_exp_lin_mul_exp_neg_exp

-- DBNGKernel: generic integrability / vanishing against exponential weights
#print axioms DBN.integrableOn_superExp_mul
#print axioms DBN.tendsto_superExp_mul_atTop
#print axioms DBN.norm_cos_mul_ofReal_le
#print axioms DBN.norm_sin_mul_ofReal_le

-- DBNGKernel: complexified kernels
#print axioms DBN.hasDerivAt_ofReal_g
#print axioms DBN.hasDerivAt_ofReal_g'
#print axioms DBN.continuous_ofReal_g
#print axioms DBN.continuous_ofReal_g'
#print axioms DBN.continuous_ofReal_g''
#print axioms DBN.norm_ofReal_g_le
#print axioms DBN.norm_ofReal_g'_le
#print axioms DBN.norm_ofReal_g''_le

-- DBNGKernel: integrability (pointwise and Pi.mul shapes; cos / sin instances)
#print axioms DBN.integrableOn_g_mul
#print axioms DBN.integrableOn_g'_mul
#print axioms DBN.integrableOn_g''_mul
#print axioms DBN.integrableOn_ofReal_g_mul_pi
#print axioms DBN.integrableOn_ofReal_g'_mul_pi
#print axioms DBN.integrableOn_ofReal_g''_mul_pi
#print axioms DBN.integrableOn_g_mul_cos
#print axioms DBN.integrableOn_g_mul_sin
#print axioms DBN.integrableOn_g'_mul_cos
#print axioms DBN.integrableOn_g'_mul_sin
#print axioms DBN.integrableOn_g''_mul_cos

-- DBNGKernel: boundary limits at +infinity and 0+
#print axioms DBN.tendsto_ofReal_g_mul_atTop
#print axioms DBN.tendsto_ofReal_g'_mul_atTop
#print axioms DBN.tendsto_ofReal_g''_mul_atTop
#print axioms DBN.tendsto_ofReal_g_mul_nhdsGT
#print axioms DBN.tendsto_ofReal_g'_mul_nhdsGT

-- DBNGKernel: the side conditions of the two integrations by parts (module D consumes these)
#print axioms DBN.hasDerivAt_cos_mul_ofReal
#print axioms DBN.hasDerivAt_neg_sin_mul_ofReal_mul
#print axioms DBN.norm_neg_sin_mul_ofReal_mul_le
#print axioms DBN.norm_neg_cos_mul_ofReal_mul_mul_le
#print axioms DBN.integrableOn_ofReal_g_mul_cos_deriv2
#print axioms DBN.integrableOn_ofReal_g'_mul_cos_deriv
#print axioms DBN.integrableOn_ofReal_g''_mul_cos_pi
#print axioms DBN.tendsto_ofReal_g_mul_cos_deriv_nhdsGT
#print axioms DBN.tendsto_ofReal_g_mul_cos_deriv_atTop
#print axioms DBN.tendsto_ofReal_g'_mul_cos_nhdsGT
#print axioms DBN.tendsto_ofReal_g'_mul_cos_atTop

-- DBNGKernel: the bridge to H_0
#print axioms DBN.integral_g''_sub_g_mul_cos

-- DBNGKernel: registry-shaped summary (proposed lemma node RH_dbn_g_kernel_identities)
#print axioms dbn_g_kernel_identities

-- Route C / C2 module B (DBNXiCos): the substitution x = e^{4u} in Riemann's symmetric integral,
-- completedRiemannZeta₀ (1/2 + iz/2) = 8 ∫_0^∞ g(u) cos(zu) du (unconditional; NOT RH)
#print axioms DBN.g_eq_thetaMoment
#print axioms DBN.g_eq_exp_mul_psi
#print axioms DBN.image_exp_four_mul_Ioi
#print axioms DBN.hasDerivAt_exp_four_mul
#print axioms DBN.integral_Ioi_one_eq_integral_exp_four_mul
#print axioms DBN.ofReal_exp_cpow
#print axioms DBN.xiCos_integrand
#print axioms DBN.completedRiemannZeta₀_half_add_eq

-- Route C / C2 module D (DBNXiIBP): the two integrations by parts (unconditional; NOT RH)
#print axioms DBN.integral_g_cos_ibp
#print axioms DBN.integral_g_cos_eq

-- Route C / C2 module E (DBNXi): the representation theorem H_0 = ξ/8 (registry node
-- RH.dbn_H0_eq_xi, statement verbatim) and H_0(i) = 1/16.  An identity between two entire
-- functions, NOT RH-equivalent.
#print axioms dbn_H0_eq_xi
#print axioms DBN.H_zero_I

-- Route C / C4, unconditional (DBNRealZerosIffFinal): the named obligation DBN.H0EqXi
-- discharged, and the registry statement of RH.dbn_rh_iff_H0_real_zeros verbatim.  An
-- equivalence between two restatements of the same OPEN conjecture; it proves neither side.
#print axioms DBN.H0EqXi_holds
#print axioms dbn_rh_iff_H0_real_zeros

-- Route C / C3 input (DBNStrip): the zero strip of H_0, C2-free.  L1b Gamma integral on the line
#print axioms DBN.integral_exp_smul_comp_exp
#print axioms DBN.ofReal_exp_cpow_comm
#print axioms DBN.integral_cexp_mul_exp_neg_exp
#print axioms DBN.integral_exp_mul_exp_neg_exp
#print axioms DBN.integrable_cexp_mul_exp_neg_exp
#print axioms DBN.integrable_exp_mul_exp_neg_exp

-- DBNStrip L1a: two-sided fold and Schwarz reflection
#print axioms DBN.continuous_expIntegrand
#print axioms DBN.norm_cexp_mul_I_le
#print axioms DBN.expIntegrand_neg
#print axioms DBN.integrableOn_expIntegrand_Ioi
#print axioms DBN.integrableOn_expIntegrand_Iic
#print axioms DBN.integrable_expIntegrand
#print axioms DBN.H_zero_eq_half_integral
#print axioms DBN.H_conj

-- DBNStrip L1b termwise + L1c Tonelli/Fubini and the half-plane identity (Im z < -1 only)
#print axioms DBN.Φ_eq_tsum_ΦTerm
#print axioms DBN.expTerm_eq
#print axioms DBN.stripArg_re
#print axioms DBN.one_div_pi_mul_sq_cpow
#print axioms DBN.integral_expTerm
#print axioms DBN.integrable_expTerm
#print axioms DBN.norm_expTerm_le
#print axioms DBN.pnat_pow_mul_one_div_rpow
#print axioms DBN.summable_integral_norm_expTerm
#print axioms DBN.hasSum_integral_expTerm
#print axioms DBN.integral_expIntegrand_eq
#print axioms DBN.H_zero_eq_of_im_lt

-- DBNStrip L1d: nonvanishing off the strip, the zero strip, and the registry statement verbatim
#print axioms DBN.H_zero_ne_zero_of_im_lt
#print axioms DBN.H_zero_ne_zero_of_one_lt_im
#print axioms DBN.H0_zero_strip
#print axioms DBN.H0_ne_zero
#print axioms dbn_H0_zero_strip

-- Route C / C3 groundwork, L4 (DBNStep): the vertical-shift average and the discrete de Bruijn
-- step against abstract even Hadamard data (pure Mathlib)
#print axioms DBN.differentiable_shiftAvg
#print axioms DBN.shiftAvg_neg
#print axioms DBN.shiftAvg_conj
#print axioms DBN.eq_zero_of_tendsto_prod_of_eq_zero
#print axioms DBN.prod_ne_zero_of_tendsto
#print axioms DBN.EvenHadamardData.even
#print axioms DBN.EvenHadamardData.eq_zero_of_factor
#print axioms DBN.EvenHadamardData.apply_inv_eq_zero
#print axioms DBN.EvenHadamardData.eq_const
#print axioms DBN.EvenHadamardData.tendsto_prod_conj
#print axioms DBN.EvenHadamardData.eq_zero_of_conj_factor
#print axioms DBN.EvenHadamardData.ofHasProd
#print axioms DBN.EvenHadamardData.ofMultipliable
#print axioms DBN.hadQ_nonneg
#print axioms DBN.hadQ_zero
#print axioms DBN.EvenHadamardData.tendsto_sq_norm
#print axioms DBN.sq_norm_sub_mul_norm_sub_conj
#print axioms DBN.pair_lt
#print axioms DBN.hadQ_eq
#print axioms DBN.hadQ_lt
#print axioms DBN.norm_sub_lt_norm_add
#print axioms DBN.max_sub_max_zero
#print axioms DBN.EvenHadamardData.norm_lt_norm
#print axioms DBN.EvenHadamardData.shiftAvg_zero_im_sq_le
#print axioms DBN.EvenHadamardData.shiftAvg_real_zeros
#print axioms DBN.zero_im_sq_le_of_shiftAvg_iterate

-- DBNStepControls: positive control (1 + z^2; hypotheses met, bound attained) and negative
-- control (z^2 - 2i; not real, conclusion of the step lemma fails)
#print axioms DBN.evenHadamardData_one_add_sq
#print axioms DBN.one_add_sq_conj
#print axioms DBN.one_add_sq_zero_im_sq_le
#print axioms DBN.shiftAvg_one_add_sq
#print axioms DBN.step_one_add_sq
#print axioms DBN.step_bound_attained
#print axioms DBN.evenHadamardData_sq_sub_two_I
#print axioms DBN.sq_sub_two_I_zero_im_sq_le
#print axioms DBN.shiftAvg_sq_sub_two_I
#print axioms DBN.step_needs_reality

-- Route C / C3 groundwork, L2e (DBNHurwitz): Hurwitz, maximum-modulus form (pure Mathlib)
#print axioms DBN.hurwitz_ne_zero
#print axioms DBN.hurwitz_ne_zero_of_entire

-- Route C / C3 groundwork, L2a-d (DBNHeatApprox): the de Bruijn approximants
#print axioms DBN.norm_cos_le_exp_abs_im
#print axioms DBN.norm_cos_mul_le
#print axioms DBN.one_add_sq_div_two_le_cosh
#print axioms DBN.cosh_pow_le_exp
#print axioms DBN.integrableOn_exp_mul_abs_Φ
#print axioms DBN.continuous_GδIntegrand
#print axioms DBN.norm_GδIntegrand_le
#print axioms DBN.integrableOn_GδIntegrand
#print axioms DBN.GδIntegrand_succ
#print axioms DBN.Gδ_succ
#print axioms DBN.Gδ_zero
#print axioms DBN.Gδ_eq_iterate
#print axioms DBN.differentiable_Gδ
#print axioms DBN.Gδ_neg
#print axioms DBN.Gδ_conj
#print axioms DBN.Gδ_ofReal_im
#print axioms DBN.norm_Gδ_le
#print axioms DBN.cosh_le_exp_abs
#print axioms DBN.mul_le_rpow_add_cube
#print axioms DBN.cube_add_le_exp
#print axioms DBN.norm_GδIntegrand_le_rpow
#print axioms DBN.norm_Gδ_le_exp_rpow
#print axioms DBN.norm_Gδ_le_exp_rpow_norm
#print axioms DBN.cosh_sqrt_pow_le
#print axioms DBN.one_add_div_pow_le_cosh_sqrt_pow
#print axioms DBN.tendsto_cosh_sqrt_pow
#print axioms DBN.continuous_approxErrIntegrand
#print axioms DBN.approxErrIntegrand_nonneg
#print axioms DBN.approxErrIntegrand_le
#print axioms DBN.integrableOn_approxErrIntegrand
#print axioms DBN.tendsto_approxErr
#print axioms DBN.norm_H_sub_G_le
#print axioms DBN.tendstoUniformlyOn_G
#print axioms DBN.tendstoLocallyUniformly_G
#print axioms DBN.norm_G_le
#print axioms DBN.Φ_term_pos
#print axioms DBN.Φ_pos
#print axioms DBN.setIntegral_weight_mul_Φ_pos
#print axioms DBN.H_zero_re_pos
#print axioms DBN.H_zero_ne_zero
#print axioms DBN.Gδ_zero_re_pos
#print axioms DBN.H_ne_zero_of_approx_on
#print axioms DBN.H_ne_zero_of_approx

-- Route C / C3 REDUCED (DBNDeBruijnReduction), CONDITIONAL on the named obligations
-- H0ZeroFreeOffStrip (L1) and ApproxHadamard (L3); they enter as hypotheses, so the expected
-- closure is still [propext, Classical.choice, Quot.sound].  NOT the registry node.
#print axioms DBN.Gδ_zero_delta
#print axioms DBN.G_zero_im_sq_le_of_obligations
#print axioms DBN.H_zero_im_sq_le_of_obligations
#print axioms DBN.H_ne_zero_of_obligations

-- Route C / C3 obligation L3, the Hadamard factorisation (telperion/docs/HADAMARD_PLAN_2026-09-23.md):
-- Mathlib-only pieces (Count/Product/Mean/Linear), the even factorisation theorem (DBNHadamard),
-- and its instantiation on the approximants plus de Bruijn's theorem (DBNHadamardApprox).
-- Everything unconditional; expected closure [propext, Classical.choice, Quot.sound].
-- Classical, NOT RH: nothing about zeros of H_0 inside the strip.  conjecture1_proved = False.
-- DBNHadamardCount
#print axioms DBN.analyticOrderAt_ne_top_of_entire
#print axioms DBN.divisor_eq_analyticOrderNatAt
#print axioms DBN.one_le_analyticOrderNatAt
#print axioms DBN.sum_ord_le_zeroCount
#print axioms DBN.zeroCount_le
#print axioms DBN.two_pow_dyadicIdx_le
#print axioms DBN.lt_two_pow_dyadicIdx_succ
#print axioms DBN.two_pow_rpow_neg_mul
#print axioms DBN.two_pow_rpow_neg
#print axioms DBN.dyadic_group_sum_le
#print axioms DBN.summable_zero_multiplicity_rpow
-- DBNHadamardProduct
#print axioms DBN.factor_eq_one_add
#print axioms DBN.factor_fun_eq
#print axioms DBN.norm_neg_factor
#print axioms DBN.summable_norm_neg_factor
#print axioms DBN.multipliable_factor
#print axioms DBN.differentiable_finset_prod_factor
#print axioms DBN.differentiable_tprod_factor
#print axioms DBN.tprod_factor_ne_zero
#print axioms DBN.hasProd_evenProduct
#print axioms DBN.differentiable_evenProduct
#print axioms DBN.evenProduct_zero
#print axioms DBN.evenProduct_neg
#print axioms DBN.log_one_add_le_rpow
#print axioms DBN.mul_sq_rpow_half
#print axioms DBN.norm_factor_le_exp
#print axioms DBN.norm_evenProduct_le
#print axioms DBN.eq_zero_of_hasProd_of_eq_zero
#print axioms DBN.evenProduct_eq_zero_iff
#print axioms DBN.evenProduct_ne_zero
#print axioms DBN.finite_setOf_factor_eq_zero
#print axioms DBN.analyticOrderAt_factor
#print axioms DBN.analyticOrderAt_finset_prod_factor
#print axioms DBN.evenProduct_eq_finset_prod_mul
#print axioms DBN.analyticOrderNatAt_evenProduct
-- DBNHadamardMean
#print axioms DBN.exists_exp_eq_of_ne_zero
#print axioms DBN.abs_eq_two_mul_max_sub
#print axioms DBN.posLog_exp_of_nonneg
#print axioms DBN.circleAverage_re_eq
#print axioms DBN.circleAverage_log_norm_nonneg
#print axioms DBN.circleAverage_posLog_norm_le
#print axioms DBN.circleAverage_abs_re_le
-- DBNHadamardLinear
#print axioms DBN.poissonKernel_zero_le
#print axioms DBN.poissonKernel_zero_nonneg
#print axioms DBN.poissonKernel_zero_le_three
#print axioms DBN.continuousOn_poissonKernel_zero
#print axioms DBN.abs_re_le_three_mul_circleAverage
#print axioms DBN.norm_le_of_re_le
#print axioms DBN.norm_deriv_le_of_forall_sphere
#print axioms DBN.norm_deriv_deriv_le
#print axioms DBN.eq_linear_of_circleAverage_abs_re_le
-- DBNHadamard
#print axioms DBN.analyticOrderAt_neg_of_even
#print axioms DBN.analyticOrderNatAt_neg_of_even
#print axioms DBN.even_analyticOrderNatAt_zero
#print axioms DBN.isRep_or_isRep_neg
#print axioms DBN.not_isRep_neg_of_isRep
#print axioms DBN.summable_zeroIdx_rpow
#print axioms DBN.countable_zeroIdx_of_summable
#print axioms DBN.repSeq_apply
#print axioms DBN.repSeq_of_notMem_range
#print axioms DBN.summable_repSeq_rpow
#print axioms DBN.ncard_factor_eq_analyticOrderNatAt
#print axioms DBN.exists_quotient
#print axioms DBN.evenHadamardData_of_order_lt_two
-- DBNHadamardApprox
#print axioms DBN.norm_Gδ_le_growth
#print axioms DBN.Gδ_exists_ne_zero
#print axioms DBN.approxHadamard
#print axioms DBN.H0ZeroFreeOffStrip_holds
#print axioms DBN.H_zero_im_sq_le
#print axioms DBN.H_ne_zero_of_half_le
#print axioms dbn_debruijn_real_zeros
-- lane m1: DBNM1Approx
#print axioms DBN.m1_continuous_WIntegrand
#print axioms DBN.m1_norm_HIntegrand_le
#print axioms DBN.m1_norm_WIntegrand
#print axioms DBN.m1_integrableOn_WIntegrand
#print axioms DBN.m1_WIntegrand_succ
#print axioms DBN.m1W_succ
#print axioms DBN.m1W_zero
#print axioms DBN.m1W_zero_base
#print axioms DBN.m1W_eq_iterate
#print axioms DBN.m1_differentiable_W
#print axioms DBN.m1W_neg
#print axioms DBN.m1W_conj
#print axioms DBN.m1_W_zero_re_pos
#print axioms DBN.m1_W_zero_ne_zero
#print axioms DBN.m1_mul_sq_le_exp
#print axioms DBN.m1_cube_add_le_exp
#print axioms DBN.m1_norm_WIntegrand_le_rpow
#print axioms DBN.m1_norm_W_le_exp_rpow
#print axioms DBN.m1_norm_W_le_exp_rpow_norm
#print axioms DBN.m1_norm_W_le_growth
#print axioms DBN.m1_evenHadamardData_W
#print axioms DBN.m1_continuous_ErrIntegrand
#print axioms DBN.m1_ErrIntegrand_nonneg
#print axioms DBN.m1_ErrIntegrand_le
#print axioms DBN.m1_integrableOn_ErrIntegrand
#print axioms DBN.m1_tendsto_Err
#print axioms DBN.m1_HIntegrand_sub_WIntegrand
#print axioms DBN.m1_norm_H_sub_G_le
#print axioms DBN.m1_tendstoUniformlyOn_G
#print axioms DBN.m1_tendstoLocallyUniformly_G
-- lane m1: DBNM1Parametric
#print axioms DBN.m1_G_zero_im_sq_le
#print axioms DBN.m1_H_zero_im_sq_le
#print axioms DBN.m1_H_zero_im_sq_le_of_le
#print axioms DBN.m1_H_real_zeros_of_le
#print axioms DBN.m1_H_real_zeros_of_im_sq_le
#print axioms DBN.m1_im_sq_le_of_upper_zero_free
#print axioms DBN.m1_real_zeros_of_upper_zero_free
#print axioms dbn_debruijn_parametric
#print axioms dbn_real_zeros_upset
-- lane m1: DBNM1RHIff
#print axioms dbn_rh_iff_real_zeros_nonneg_t
-- lane m1: DBNM1Controls
#print axioms m1_control_contraction_via_parametric
#print axioms m1_control_debruijn_via_parametric

-- lane m4 (Route C M4): DBNM4LocalStep
#print axioms DBN.m4_pair_lt_local
#print axioms DBN.m4_hadQ_lt_local
#print axioms DBN.EvenHadamardData.m4_norm_lt_norm_local
#print axioms DBN.EvenHadamardData.m4_shiftAvg_ne_zero_local
#print axioms DBN.m4_zero_abs_of_zero
#print axioms DBN.m4_barrier_induction
#print axioms DBN.m4_compact_margin
-- lane m4: DBNM4HeatUniform
#print axioms DBN.m4_continuous_H_uncurry
#print axioms DBN.m4_exp_sub_cosh_pow_le
#print axioms DBN.m4_integrableOn_approxIntegrand
#print axioms DBN.m4ApproxConst_nonneg
#print axioms DBN.m4_norm_H_sub_Gδ_le
-- lane m4: DBNM4P15Criterion (Polymath15 Prop 3.3; Thm 1.2 conclusion conditional on M1aStep)
#print axioms DBN.m4_H_real
#print axioms DBN.m4_im_le_sqrt_of_H_eq_zero
#print axioms DBN.m4_re_add_im_mul_I
#print axioms DBN.m4_im_add_im_mul_I
#print axioms DBN.m4_barrier_margin
#print axioms DBN.m4_rect_margin
#print axioms DBN.m4_lowered_curve
#print axioms DBN.m4_path_zero_free
#print axioms DBN.m4_inner_zero_free
#print axioms DBN.m4_p15_prop33
#print axioms DBN.m4_p15_prop33_abs_im_lt
#print axioms DBN.m4_p15_prop33_upper
#print axioms DBN.m4_p15_criterion_of_M1aStep
#print axioms DBN.m4_P15Barrier_of_box
#print axioms DBN.m4_p15_hyps_satisfiable
#print axioms DBN.m4_p15_control_instance
#print axioms m4_dbn_p15_prop33
#print axioms m4_dbn_p15_criterion_of_parametric

example (H : ℝ) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ H → 55 / 16 ≤ |ρ.im| :=
  m6gap_height_floor H

example : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 55 / 16 < |ρ.im| :=
  m6gap_dbn_zeta_zero_free_low

example : ∀ X y0 : ℝ, X ≤ 55 / 8 → 0 ≤ y0 →
    ∀ σ T : ℝ, (1 + y0) / 2 ≤ σ → σ ≤ 1 → 0 ≤ T → T ≤ X / 2 →
      riemannZeta ((σ : ℂ) + (T : ℂ) * Complex.I) ≠ 0 :=
  m6gap_dbn_p15_thm12_i

example : ∀ t y : ℝ, DBN.H t ((y : ℂ) * Complex.I) ≠ 0 :=
  m6gap_dbn_H_imag_axis_ne_zero

example : ∀ σ : ℝ, 0 < σ → σ < 1 → riemannZeta (σ : ℂ) ≠ 0 :=
  m6gap_dbn_no_real_zero_in_unit_interval

example : ∀ z : ℂ, |z.re| ≤ 55 / 8 → DBN.H 0 z ≠ 0 :=
  m6gap_dbn_H0_zero_free_abs_re_le

example : ∀ X y0 t0 : ℝ, X ≤ 55 / 8 →
    ∀ x y : ℝ, 0 ≤ x → x ≤ X → Real.sqrt (y0 ^ 2 + 2 * t0) ≤ y → y ≤ 1 →
      DBN.H 0 ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0 :=
  m6gap_dbn_p15_prop33_i

example : ∀ X y0 t0 : ℝ, 0 ≤ t0 →
    (∀ σ T : ℝ, (1 + y0) / 2 ≤ σ → σ ≤ 1 → 0 ≤ T → T ≤ X / 2 →
      riemannZeta ((σ : ℂ) + (T : ℂ) * Complex.I) ≠ 0) →
    ∀ x y : ℝ, 0 ≤ x → x ≤ X → Real.sqrt (y0 ^ 2 + 2 * t0) ≤ y → y ≤ 1 →
      DBN.H 0 ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0 :=
  m6gap_dbn_p15_prop33_i_of_thm12_i

/-- m6gap NEGATIVE CONTROL 1: the whole rectangle `[1/2, 1] × [0, 55/16]` as ONE box is rejected. -/
example : M6gap.HeightFloor.DI.checkAB
    (M6gap.HeightFloor.DI.evalAB ⟨2, 4, 2⟩ ⟨0, 880, 8⟩ ⟨2147483648, 3037000500, 32⟩
      ⟨-3116411797, 4294967296, 32⟩ ⟨0, 4294967296, 32⟩).1
    (M6gap.HeightFloor.DI.evalAB ⟨2, 4, 2⟩ ⟨0, 880, 8⟩ ⟨2147483648, 3037000500, 32⟩
      ⟨-3116411797, 4294967296, 32⟩ ⟨0, 4294967296, 32⟩).2 = false := by decide

/-- m6gap NEGATIVE CONTROL 2: `σ ∈ [1/2, 3/4]`, `t ∈ [165/256, 330/256]` (three slabs) is rejected. -/
example : M6gap.HeightFloor.DI.checkAB
    (M6gap.HeightFloor.DI.evalAB ⟨2, 3, 2⟩ ⟨165, 330, 8⟩ ⟨2553802833, 3037000500, 32⟩
      ⟨2691572661, 3873432754, 32⟩ ⟨1855603165, 3346965925, 32⟩).1
    (M6gap.HeightFloor.DI.evalAB ⟨2, 3, 2⟩ ⟨165, 330, 8⟩ ⟨2553802833, 3037000500, 32⟩
      ⟨2691572661, 3873432754, 32⟩ ⟨1855603165, 3346965925, 32⟩).2 = false := by decide

-- M6gapEMZeta (11)
#print axioms M6gap.ZetaReflection.sawBernoulli_zero
#print axioms M6gap.ZetaReflection.sawBernoulli_measurable
#print axioms M6gap.ZetaReflection.abs_sawBernoulli_one_le
#print axioms M6gap.ZetaReflection.sawBernoulli_eq_on_Ico
#print axioms M6gap.ZetaReflection.sawBernoulli_one_eq_on_Ico
#print axioms M6gap.ZetaReflection.em_unit_step
#print axioms M6gap.ZetaReflection.euler_maclaurin_one
#print axioms M6gap.ZetaReflection.euler_maclaurin_one_window
#print axioms M6gap.ZetaReflection.em_zeta_partial_real
#print axioms M6gap.ZetaReflection.em_zeta_remainder_integrableOn
#print axioms M6gap.ZetaReflection.em_zeta_real
-- M6gapEMZetaComplex (23)
#print axioms M6gap.ZetaReflection.em_unit_step_cpow
#print axioms M6gap.ZetaReflection.euler_maclaurin_one_window_cpow
#print axioms M6gap.ZetaReflection.hasDerivAt_cpow_neg
#print axioms M6gap.ZetaReflection.em_cpow_partial
#print axioms M6gap.ZetaReflection.cpow_neg_integrableOn_Ioi
#print axioms M6gap.ZetaReflection.em_cpow_remainder_integrableOn
#print axioms M6gap.ZetaReflection.em_zeta_cpow
#print axioms M6gap.ZetaReflection.em_zeta_cpow_riemannZeta
#print axioms M6gap.ZetaReflection.em_cpow_remainder_integrableOn_strip
#print axioms M6gap.ZetaReflection.emZetaRemainder_bound
#print axioms M6gap.ZetaReflection.emZetaClosed_eq_riemannZeta_of_one_lt
#print axioms M6gap.ZetaReflection.log_le_rpow_div
#print axioms M6gap.ZetaReflection.hasDerivAt_emIntegrand
#print axioms M6gap.ZetaReflection.emZetaRemainder_hasDerivAt
#print axioms M6gap.ZetaReflection.emZetaRemainder_differentiableAt
#print axioms M6gap.ZetaReflection.isPreconnected_rightHalfPlane_diff_one
#print axioms M6gap.ZetaReflection.emZetaClosed_analyticOnNhd
#print axioms M6gap.ZetaReflection.riemannZeta_analyticOnNhd_strip
#print axioms M6gap.ZetaReflection.em_zeta_strip
#print axioms M6gap.ZetaReflection.em_zeta_strip_enclosure
#print axioms M6gap.ZetaReflection.re_em_zeta_strip_enclosure
#print axioms M6gap.ZetaReflection.im_em_zeta_strip_enclosure
#print axioms M6gap.ZetaReflection.em_zeta_critical_line_enclosure
-- M6gapEMZetaTail (27)
#print axioms M6gap.ZetaReflection.sawBernoulli_two_eq_on_Ico
#print axioms M6gap.ZetaReflection.abs_sawBernoulli_two_le
#print axioms M6gap.ZetaReflection.bernoulliFun_three
#print axioms M6gap.ZetaReflection.abs_sawBernoulli_three_le
#print axioms M6gap.ZetaReflection.sawAntideriv_hasDerivAt_Ioo
#print axioms M6gap.ZetaReflection.em_saw_step
#print axioms M6gap.ZetaReflection.em_saw_step_window
#print axioms M6gap.ZetaReflection.em_tail_integral_bound
#print axioms M6gap.ZetaReflection.integral_Ioi_shift_rpow
#print axioms M6gap.ZetaReflection.em_tail_integral_bound_shifted
#print axioms M6gap.ZetaReflection.em_tail3_bound
#print axioms M6gap.ZetaReflection.em_tail3_envelope_le
#print axioms M6gap.ZetaReflection.em_tail3_number
#print axioms M6gap.ZetaReflection.hasDerivAt_cpow_neg2
#print axioms M6gap.ZetaReflection.em_saw_step_cpow
#print axioms M6gap.ZetaReflection.em_saw_step_window_cpow
#print axioms M6gap.ZetaReflection.em_tail2_integrableOn
#print axioms M6gap.ZetaReflection.em_tail1_integrableOn
#print axioms M6gap.ZetaReflection.em_tail2_step
#print axioms M6gap.ZetaReflection.hasDerivAt_cpow_neg3
#print axioms M6gap.ZetaReflection.em_tail3_integrableOn
#print axioms M6gap.ZetaReflection.em_tail3_step
#print axioms M6gap.ZetaReflection.em_tail_order3_identity
#print axioms M6gap.ZetaReflection.em_zeta_strip3
#print axioms M6gap.ZetaReflection.em_zeta_strip3_enclosure
#print axioms M6gap.ZetaReflection.em_zeta_critical_line3_enclosure
#print axioms M6gap.ZetaReflection.em_zeta_critical_line3_number
-- M6gapZetaEMSum (1)
#print axioms M6gap.ZetaEMSum.emZetaFinite3_eq_dirichlet
-- M6gapHeightFloorCheck (12)
#print axioms M6gap.HeightFloor.pow2_cast
#print axioms M6gap.HeightFloor.DI.two_pow_pos
#print axioms M6gap.HeightFloor.DI.ofInt_sound
#print axioms M6gap.HeightFloor.DI.neg_sound
#print axioms M6gap.HeightFloor.DI.shift_eq
#print axioms M6gap.HeightFloor.DI.add_sound
#print axioms M6gap.HeightFloor.DI.corners
#print axioms M6gap.HeightFloor.DI.mul_sound
#print axioms M6gap.HeightFloor.DI.gap_sq_le
#print axioms M6gap.HeightFloor.DI.evalAB_sound
#print axioms M6gap.HeightFloor.DI.checkAB_sound
#print axioms M6gap.HeightFloor.DI.box_sound
-- M6gapHeightFloorTrig (16)
#print axioms M6gap.HeightFloor.exp_I_partial
#print axioms M6gap.HeightFloor.cos_sin_taylor
#print axioms M6gap.HeightFloor.trig_encl
#print axioms M6gap.HeightFloor.abs_mul_log_two_sub_le
#print axioms M6gap.HeightFloor.two_rpow_neg_div_pow
#print axioms M6gap.HeightFloor.le_two_rpow_neg
#print axioms M6gap.HeightFloor.two_rpow_neg_le
#print axioms M6gap.HeightFloor.two_rpow_neg_nat
#print axioms M6gap.HeightFloor.two_rpow_neg_mono
#print axioms M6gap.HeightFloor.DI.mem_mk
#print axioms M6gap.HeightFloor.mem_cos
#print axioms M6gap.HeightFloor.mem_sin_low
#print axioms M6gap.HeightFloor.sin_anti_of_half_pi
#print axioms M6gap.HeightFloor.mem_sin_high
#print axioms M6gap.HeightFloor.mem_sin_mid
#print axioms M6gap.HeightFloor.mem_m
-- M6gapHeightFloorEM (8)
#print axioms M6gap.HeightFloor.G2_eq
#print axioms M6gap.HeightFloor.norm_le_of_sq
#print axioms M6gap.HeightFloor.two_rpow_neg_five_halves_le
#print axioms M6gap.HeightFloor.tail_le
#print axioms M6gap.HeightFloor.G2_norm_le_of_zero
#print axioms M6gap.HeightFloor.two_cpow_neg_re_im
#print axioms M6gap.HeightFloor.G2_re_im
#print axioms M6gap.HeightFloor.G2_norm_gt_of_AB
-- M6gapHeightFloorBoxes (56)
#print axioms M6gap.HeightFloor.Boxes.trig_0
#print axioms M6gap.HeightFloor.Boxes.trig_1
#print axioms M6gap.HeightFloor.Boxes.trig_2
#print axioms M6gap.HeightFloor.Boxes.trig_3
#print axioms M6gap.HeightFloor.Boxes.trig_4
#print axioms M6gap.HeightFloor.Boxes.trig_5
#print axioms M6gap.HeightFloor.Boxes.trig_6
#print axioms M6gap.HeightFloor.Boxes.trig_7
#print axioms M6gap.HeightFloor.Boxes.trig_8
#print axioms M6gap.HeightFloor.Boxes.trig_9
#print axioms M6gap.HeightFloor.Boxes.trig_10
#print axioms M6gap.HeightFloor.Boxes.trig_11
#print axioms M6gap.HeightFloor.Boxes.trig_12
#print axioms M6gap.HeightFloor.Boxes.trig_13
#print axioms M6gap.HeightFloor.Boxes.trig_14
#print axioms M6gap.HeightFloor.Boxes.trig_15
#print axioms M6gap.HeightFloor.Boxes.trig_16
#print axioms M6gap.HeightFloor.Boxes.m12_hi
#print axioms M6gap.HeightFloor.Boxes.m34_lo
#print axioms M6gap.HeightFloor.Boxes.m34_hi
#print axioms M6gap.HeightFloor.Boxes.m1_lo
#print axioms M6gap.HeightFloor.Boxes.box_0_0
#print axioms M6gap.HeightFloor.Boxes.box_0_1
#print axioms M6gap.HeightFloor.Boxes.box_0_2
#print axioms M6gap.HeightFloor.Boxes.box_0_3
#print axioms M6gap.HeightFloor.Boxes.box_0_4
#print axioms M6gap.HeightFloor.Boxes.box_0_5
#print axioms M6gap.HeightFloor.Boxes.box_0_6
#print axioms M6gap.HeightFloor.Boxes.box_0_7
#print axioms M6gap.HeightFloor.Boxes.box_0_8
#print axioms M6gap.HeightFloor.Boxes.box_0_9
#print axioms M6gap.HeightFloor.Boxes.box_0_10
#print axioms M6gap.HeightFloor.Boxes.box_0_11
#print axioms M6gap.HeightFloor.Boxes.box_0_12
#print axioms M6gap.HeightFloor.Boxes.box_0_13
#print axioms M6gap.HeightFloor.Boxes.box_0_14
#print axioms M6gap.HeightFloor.Boxes.box_0_15
#print axioms M6gap.HeightFloor.Boxes.box_1_0
#print axioms M6gap.HeightFloor.Boxes.box_1_1
#print axioms M6gap.HeightFloor.Boxes.box_1_2
#print axioms M6gap.HeightFloor.Boxes.box_1_3
#print axioms M6gap.HeightFloor.Boxes.box_1_4
#print axioms M6gap.HeightFloor.Boxes.box_1_5
#print axioms M6gap.HeightFloor.Boxes.box_1_6
#print axioms M6gap.HeightFloor.Boxes.box_1_7
#print axioms M6gap.HeightFloor.Boxes.box_1_8
#print axioms M6gap.HeightFloor.Boxes.box_1_9
#print axioms M6gap.HeightFloor.Boxes.box_1_10
#print axioms M6gap.HeightFloor.Boxes.box_1_11
#print axioms M6gap.HeightFloor.Boxes.box_1_12
#print axioms M6gap.HeightFloor.Boxes.box_1_13
#print axioms M6gap.HeightFloor.Boxes.box_1_14
#print axioms M6gap.HeightFloor.Boxes.box_1_15
#print axioms M6gap.HeightFloor.Boxes.slab_0
#print axioms M6gap.HeightFloor.Boxes.slab_1
#print axioms M6gap.HeightFloor.Boxes.G2_norm_gt
-- M6gapZetaZeroConfinement (4)
#print axioms M6gap.ZetaZeroConfinement.zeta_zero_iff_completed_zero_of_im_ne
#print axioms M6gap.ZetaZeroConfinement.zeta_zero_reflect
#print axioms M6gap.ZetaZeroConfinement.zeta_zero_re_mem_strip
#print axioms M6gap.ZetaZeroConfinement.no_low_zeros_of_strip_clear
-- M6gapDlvpZetaSymmetry (5)
#print axioms M6gap.ZeroFreeBridge.riemannZeta_one_sub_eq_zero
#print axioms M6gap.ZeroFreeBridge.zeta_zero_on_line_of_right_half_clear
#print axioms M6gap.ZeroFreeBridge.riemannZeta_conj_eq_zero
#print axioms M6gap.ZeroFreeBridge.zeta_zero_on_line_of_quarter_clear
#print axioms M6gap.ZeroFreeBridge.riemannZeta_reflect_line_eq_zero
-- M6gapHeightFloor (16)
#print axioms M6gap.HeightFloor.zeta_ne_zero_low_right
#print axioms M6gap.HeightFloor.strip_clear_low
#print axioms M6gap.HeightFloor.height_floor
#print axioms M6gap.HeightFloor.height_floor_280000
#print axioms M6gap.HeightFloor.im_gt_of_zero
#print axioms M6gap.HeightFloor.abs_im_gt_of_zero
#print axioms M6gap.HeightFloor.G2_norm_le_of_zero_of_im_nonneg
#print axioms M6gap.HeightFloor.zeta_ne_zero_low_right_of_im_nonneg
#print axioms M6gap.HeightFloor.riemannZeta_ofReal_ne_zero_of_mem_Ico
#print axioms M6gap.HeightFloor.zeta_ne_zero_of_half_le_of_im_le
#print axioms M6gap.HeightFloor.strip_clear_low_of_im_nonneg
#print axioms M6gap.HeightFloor.strip_zero_abs_im_gt
#print axioms M6gap.HeightFloor.p15_thm12_i_of_le
#print axioms m6gap_height_floor
#print axioms m6gap_dbn_zeta_zero_free_low
#print axioms m6gap_dbn_p15_thm12_i
-- M6gapImAxis (14)
#print axioms M6gap.H_conj
#print axioms M6gap.cos_ofReal_mul_I_mul
#print axioms M6gap.H_ofReal_mul_I
#print axioms M6gap.integrableOn_imAxis
#print axioms M6gap.H_ofReal_mul_I_im
#print axioms M6gap.H_ofReal_mul_I_re_pos
#print axioms M6gap.H_ofReal_mul_I_ne_zero
#print axioms M6gap.H_ne_zero_of_re_eq_zero
#print axioms M6gap.xiArg_imAxis
#print axioms M6gap.riemannXi_ofReal_ne_zero
#print axioms M6gap.riemannZeta_ofReal_ne_zero_of_mem_Ioo
#print axioms M6gap.riemannZeta_ofReal_ne_zero_of_half_le
#print axioms m6gap_dbn_H_imag_axis_ne_zero
#print axioms m6gap_dbn_no_real_zero_in_unit_interval
-- M6gapP15ZeroFree (12)
#print axioms M6gap.xiArg_im
#print axioms M6gap.xiArgInv_re
#print axioms M6gap.H0_ne_zero_core
#print axioms M6gap.H0_ne_zero_of_abs_re_le
#print axioms M6gap.zeta_strip_zero_abs_im_gt
#print axioms M6gap.p15_prop33_i_of_le
#print axioms M6gap.xiArg_conj
#print axioms M6gap.p15_prop33_i_of_thm12_i
#print axioms M6gap.p15_prop33_i_of_le_via_bridge
#print axioms m6gap_dbn_H0_zero_free_abs_re_le
#print axioms m6gap_dbn_p15_prop33_i
#print axioms m6gap_dbn_p15_prop33_i_of_thm12_i

-- DBNM5Alpha (Route C M5 brick 1: P15 alpha-calculus and Thm 1.3 bounds (20)-(22))
#print axioms DBNM5.mem_slitPlane_of_im_ne_zero
#print axioms DBNM5.ne_zero_of_im_ne_zero
#print axioms DBNM5.sub_one_ne_zero_of_im_ne_zero
#print axioms DBNM5.two_pi_ne_zero
#print axioms DBNM5.log_div_two_pi
#print axioms DBNM5.hasDerivAt_alpha
#print axioms DBNM5.hasDerivAt_logM0
#print axioms DBNM5.hasDerivAt_logMt
#print axioms DBNM5.M0_eq_p15_eq6
#print axioms DBNM5.norm_alphaDeriv_le
#print axioms DBNM5.arg_ne_pi_of_im_ne_zero
#print axioms DBNM5.alpha_conj
#print axioms DBNM5.logM0_conj
#print axioms DBNM5.logMt_conj
#print axioms DBNM5.norm_Mt
#print axioms DBNM5.convex_im_eq
#print axioms DBNM5.norm_alpha_sub_le_of_im_eq
#print axioms DBNM5.norm_kappa_le
#print axioms DBNM5.alpha_I_sub_main
#print axioms DBNM5.p15_eq76_fails_at_200
#print axioms DBNM5.norm_alpha_sub_main_le
#print axioms DBNM5.re_alpha_sPlus
#print axioms DBNM5.rat_part_ge_21
#print axioms DBNM5.rat_part_ge_66
#print axioms DBNM5.re_sStar
#print axioms DBNM5.log_norm_sPlus_ge
#print axioms DBNM5.re_sStar_ge
#print axioms DBNM5.re_sStar_ge_prop66
#print axioms DBNM5.re_alpha_ge_of_im
#print axioms DBNM5.norm_alpha_le_of_im
#print axioms DBNM5.gamma_numeric
#print axioms DBNM5.re_logMtDeriv_ge
#print axioms DBNM5.hasDerivAt_gLine
#print axioms DBNM5.norm_gammaP_eq
#print axioms DBNM5.norm_gammaP_le
-- DBNM5Target (M5 target P15Thm13 [NOT proved], Cor 1.4 and Cor 6.5 => Thm 1.3, conditional)
#print axioms DBNM5.Bt_ne_zero
#print axioms DBNM5.H_ne_zero_of_P15Thm13
#print axioms DBNM5.conj_sStar_add_kappa
#print axioms DBNM5.Bt_mul_ft
#print axioms DBNM5.EA_div_Bt
#print axioms DBNM5.EB_div_Bt
#print axioms DBNM5.EC0_div_Bt
#print axioms DBNM5.P15Thm13_of_P15Cor65

-- Route C: P15 criterion wired (M4 + M1 + M6gap)
#print axioms dbn_m1aStep_holds
#print axioms dbn_p15_criterion
#print axioms dbn_p15ZeroFreeRect_of_le
#print axioms dbn_p15_criterion_low

-- Route C: zero-free half-plane for zeta => real zeros of H_t for t >= 2(theta - 1/2)^2;
-- theta = 7/8 (OpenAI QRH statement as an explicit HYPOTHESIS) gives t >= 9/32.  Not RH.
#print axioms DBN.H0_neg_im_le_of_zeta_halfplane
#print axioms DBN.H0_im_sq_le_of_zeta_halfplane
#print axioms dbn_real_zeros_of_zeta_halfplane
#print axioms dbn_real_zeros_of_qrh
#print axioms dbn_H0_im_sq_le_of_qrh

-- Newman / Lambda >= 0 programme, step 1 (DBNBohr): Bohr almost periodicity for everywhere
-- absolutely convergent Dirichlet series, qualitative form (pure Mathlib; Dobner Thm 5 input).
-- Says nothing about zeta zeros.  Nothing here proves RH.  conjecture1_proved = False.
#print axioms DBNBohr.exists_twist_close
#print axioms DBNBohr.norm_LSeries_shift_sub_le
#print axioms DBNBohr.exists_shifts_tendstoLocallyUniformly

-- Newman / Lambda >= 0 programme, step 2 (DBNFtZero): the Gaussian-weighted Dirichlet series
-- F c s = sum exp(-c (log n)^2) n^(-s) is entire of finite order and HAS A ZERO (Dobner Lemma 3,
-- qualitative), via Hadamard.entire_no_zeros_is_exp_polynomial.  Nothing here proves RH.
#print axioms DBNFtZero.lseriesSummable
#print axioms DBNFtZero.hasFiniteOrder_F
#print axioms DBNFtZero.exists_zero

-- Newman step 2b (DBNFtZeroHigh): F c has zeros of arbitrarily large imaginary part
-- (Bohr shifts + Hurwitz zero-free form; no Rouche).  Nothing here proves RH.
#print axioms DBNFtZero.exists_zero_im_ge

-- Newman step 3 (DBNStirling): complex Stirling with remainder, Gamma z = exp (L z) on Re z > 0,
-- ||R z|| <= 1/(4||z||), psi z = log z - 1/(2z) + R' z with ||R' z|| <= 1/(2||z||^2).  Pure Mathlib
-- (Euler's product + second-order Euler-Maclaurin + real Stirling).  Nothing here proves RH.
#print axioms DBNStirling.sum_log_eq
#print axioms DBNStirling.Gamma_eq_exp_L
#print axioms DBNStirling.norm_R_le
#print axioms DBNStirling.hasDerivAt_R
#print axioms DBNStirling.norm_R'_le
#print axioms DBNStirling.digamma_eq
#print axioms DBNStirling.norm_digamma_sub_log_le

-- Newman step 4 (DBNGaussConv): H_{-c} as a Gaussian convolution of H_0, the Cauchy shift of the
-- Gaussian line, and Dobner's (9): H_{-c}(-i(2s-1)) = sum_n B_n(s) with B_n the Gaussian-convolved
-- n-th Dirichlet term on Re v = a > 1.  Nothing here proves RH.  conjecture1_proved = False.
#print axioms DBNGaussConv.norm_Gamma_le_Gamma_re
#print axioms DBNGaussConv.H_neg_eq_gauss
#print axioms DBNGaussConv.shift_line
#print axioms DBNGaussConv.H_zero_eq_tsum
#print axioms DBNGaussConv.xi_eq_tsum_B

-- Newman step 5a (DBNSaddleAlg): the exact saddle-point bookkeeping for Dobner's Theorem 4:
-- gamma(b+delta) = gamma(b) rho(delta) exp(Q(delta) + delta l(b)) via Stirling's L, the contour of B
-- may be moved (Cauchy), B_n(J(s)) = gamma_t(s) a_n n^{-s} (1 + E_n(s)) exactly, and
-- xi_c(J(s)) = gamma_t(s) (F_{c/4}(s) + sum_n a_n n^{-s} E_n(s)) given convergence of the error
-- series.  No estimates yet.  Nothing here proves RH.  conjecture1_proved = False.
#print axioms DBNSaddle.γ_add_eq
#print axioms DBNSaddle.B_J_eq
#print axioms DBNSaddle.B_shift
#print axioms DBNSaddle.tsum_coef_eq_F
#print axioms DBNSaddle.xi_J_eq

-- Newman step 5b (DBNSaddleBounds): the pointwise estimates behind Theorem 4 -- ||exp Q - 1|| <=
-- ||Q|| e^{||Q||}, the branch-free split Log((b+d)/2) = Log(b/2) + Log(1+d/b), the near-field bound
-- ||K - 1|| <= 8P/||b|| e^{2P/||b||}, and the global bound on ||K||.  Nothing here proves RH.
#print axioms DBNSaddle.norm_exp_sub_one_le_mul_exp
#print axioms DBNSaddle.log_half_add_eq
#print axioms DBNSaddle.norm_K_sub_one_le
#print axioms DBNSaddle.norm_K_le

-- Newman step 5c/5 (DBNSaddleSum, DBNTheorem4): the unified pointwise bound integrated against the
-- Gaussian and summed over n -- the error series is uniformly small on the strip -- and Dobner's
-- Theorem 4 in qualitative form: xi_c(J(s))/gamma_t(s) - F_{c/4}(s) -> 0 as Im s -> oo, uniformly for
-- |Re s - x_0| <= 1.  Nothing here proves RH.  conjecture1_proved = False.
#print axioms DBNSaddle.norm_K_sub_one_le_unified
#print axioms DBNSaddle.norm_E_le
#print axioms DBNSaddle.error_sum_small
#print axioms DBNSaddle.theorem4

-- Newman step 6 (DBNNewman): NEWMAN'S CONJECTURE (Rodgers-Tao's theorem) on this island, after Dobner --
-- for every t < 0, H_t has a non-real zero: dbn_newman : forall t < 0, exists z, H t z = 0 and z.im != 0.
-- In the island's sInf-free vocabulary this is Lambda >= 0.  Lambda = 0 is RH and is NOT proved.
-- conjecture1_proved = False.
#print axioms DBNSaddle.dbn_newman_of_neg
#print axioms dbn_newman

-- Effective Theorem 4 (item 4): explicit Y(c, x0, eps); tsums kept as constants in theorem4_explicit,
-- fully closed-form in theorem4_fully_explicit. Not an effective Newman theorem (see the note).
#print axioms DBNSaddle.theorem4_explicit
#print axioms DBNSaddle.theorem4_fully_explicit
#print axioms DBNSaddle.C₁_eq
#print axioms DBNSaddle.C₂_eq

-- Extended Selberg class (item 3, Dobner's theorem in full for every ExtSelbergData): the data of an
-- S^# element as a structure (fields = hypotheses, incl. the entire continuation and strip bound),
-- the Gaussian-convolution flow, and Newman for it; zeta is the control instance. Lambda_F = 0 is not touched.
#print axioms DBNSelberg.ExtSelbergData.gammaF_add_eq
#print axioms DBNSelberg.ExtSelbergData.xi_eq_tsum_Bn
#print axioms DBNSelberg.ExtSelbergData.tsum_Bn_J_eq
#print axioms DBNSelberg.ExtSelbergData.norm_KF_sub_one_le_unified
#print axioms DBNSelberg.ExtSelbergData.P_eval_ne_zero
#print axioms DBNSelberg.ExtSelbergData.exists_zero_Ft
#print axioms DBNSelberg.ExtSelbergData.exists_zero_im_ge_Ft
#print axioms DBNSelberg.ExtSelbergData.error_sum_small
#print axioms DBNSelberg.ExtSelbergData.differentiable_flow
#print axioms DBNSelberg.ExtSelbergData.theorem4_of
#print axioms DBNSelberg.ExtSelbergData.selberg_newman_of
#print axioms DBNSelberg.zetaData_flow_eq
#print axioms selberg_newman
#print axioms dbn_newman_of_selberg

-- S^# itself (SelbergSharp: meromorphic F, functional equation on the strip, finite order on the right
-- half-plane) yields an ExtSelbergData: Gamma decay on vertical strips, the glued entire xi, the
-- Phragmen-Lindelof strip bound; hence Newman for every S^# element as the island states it.
#print axioms DBNStirling.norm_Gamma_le_vertical
#print axioms DBNSelberg.SelbergSharp.differentiable_xi
#print axioms DBNSelberg.SelbergSharp.xi_functional_equation
#print axioms DBNSelberg.SelbergSharp.hasFiniteOrder_xi
#print axioms DBNSelberg.SelbergSharp.exists_bound_xi_vertical
#print axioms selberg_newman_sharp_ext
#print axioms selberg_newman_sharp
