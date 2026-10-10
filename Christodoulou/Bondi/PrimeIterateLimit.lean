module
public import Christodoulou.Frozen.Bondi.ContractionFactor
public import Christodoulou.Frozen.Bondi.TranslatedDataField
public import Christodoulou.Frozen.Bondi.MemXPrimeBall
public import Christodoulou.Frozen.Bondi.YPrimeDistLe
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.IsDecaySlice
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Christodoulou.Frozen.Bondi.LinearStepYPrimeLipschitz
import Christodoulou.Frozen.Bondi.TranslatedIterateDerivUniformEquicontinuousOn
import Christodoulou.Frozen.Bondi.LinearStepYLipschitz
import Christodoulou.Frozen.Bondi.LinearStepMapApply
import Christodoulou.Frozen.Bondi.LinearStepZero
import Christodoulou.Frozen.Bondi.TranslatedDataFieldApply
import Christodoulou.Bondi.IterateLimit
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# The limit of the translated iterates on an arbitrary strip

The sealed weighted contraction gives geometric convergence in Y′. The translated-seed
uniform equicontinuity gate and radial interpolation give convergence of derivatives,
including the centre. Passing the weighted sum bound to the limit preserves the X′ radius.
The sealed unweighted Lipschitz estimate identifies the fixed point on each finite strip;
time clamping extends this equality to the ambient continuous maps.
-/

public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi
namespace XPL

private theorem primeWeight_ge_one (u r : ℝ≥0) : 1 ≤ primeWeight u r := by
  dsimp only [primeWeight]
  linarith only [u.coe_nonneg, r.coe_nonneg]

private theorem contractionFactor_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ contractionFactor x := by
  dsimp only [contractionFactor]
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hx 2)) (by positivity))
    (exp_pos _).le

private theorem geometric_tendsto {x : ℝ} (hx : 0 ≤ x)
    (hq : contractionFactor x < 1) :
    Tendsto (fun n : ℕ => 2 * x * contractionFactor x ^ n / (1 - contractionFactor x))
      atTop (𝓝 0) := by
  simpa only [mul_zero, zero_div] using
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (contractionFactor_nonneg hx) hq).const_mul
      (2 * x)).div_const (1 - contractionFactor x)

private theorem iterate_clamp {T : ℝ≥0} {x : ℝ} (data : C(ℝ≥0, ℝ))
    (h : ℕ → C(ℝ≥0 × ℝ≥0, ℝ)) (hb : ∀ n, MemXPrimeBall T x (h n))
    (hzero : h 0 = translatedDataField T data)
    (hstep : ∀ n, h (n + 1) = linearStepMap (hb n).1 data)
    (n : ℕ) (u r : ℝ≥0) : h n (u, r) = h n (min u T, r) := by
  cases n with
  | zero =>
    rw [hzero]
    change data (r + min u T / 2) = data (r + min (min u T) T / 2)
    rw [min_assoc, min_self]
  | succ n => rw [hstep]; exact XLim.linearStepMap_clamp _ _ _ _

private theorem iterate_step_bound {T : ℝ≥0} {x : ℝ} (data : C(ℝ≥0, ℝ))
    (hdata : IsDecaySlice data) (h : ℕ → C(ℝ≥0 × ℝ≥0, ℝ))
    (hb : ∀ n, MemXPrimeBall T x (h n))
    (hstep : ∀ n, h (n + 1) = linearStepMap (hb n).1 data) (n : ℕ) :
    YPrimeDistLe T (h (n + 1)) (h n) (2 * x * contractionFactor x ^ n) := by
  induction n with
  | zero =>
    intro u hu r
    have h0 := (hb 0).2 u hu r
    have h1 := (hb 1).2 u hu r
    have hw : 0 ≤ primeWeight u r := (zero_le_one.trans (primeWeight_ge_one u r))
    have ht := mul_le_mul_of_nonneg_left (abs_sub (h 1 (u, r)) (h 0 (u, r)))
      (pow_nonneg hw 3)
    have hq0 : 0 ≤ primeWeight u r ^ 4 * |radialDerivative (h 0) u r| := by positivity
    have hq1 : 0 ≤ primeWeight u r ^ 4 * |radialDerivative (h 1) u r| := by positivity
    simp only [pow_zero, mul_one]
    linarith only [h0, h1, ht, hq0, hq1]
  | succ n ih =>
    have hSK : MemXPrimeBall T x (linearStepMap (hb n).1 data) := by
      rw [← hstep n]
      exact hb (n + 1)
    have hh := linearStep_yPrime_lipschitz (hb (n + 1)) (hb n) data hdata.1.1 hSK ih
    rw [← hstep (n + 1), ← hstep n] at hh
    convert hh using 1
    ring

private theorem iterate_continuous_limit {T : ℝ≥0} {x : ℝ} (hx : 0 ≤ x)
    (hq : contractionFactor x < 1) (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
    (h : ℕ → C(ℝ≥0 × ℝ≥0, ℝ)) (hb : ∀ n, MemXPrimeBall T x (h n))
    (hzero : h 0 = translatedDataField T data)
    (hstep : ∀ n, h (n + 1) = linearStepMap (hb n).1 data) :
    ∃ H : C(ℝ≥0 × ℝ≥0, ℝ), TendstoUniformly (fun n p => h n p) H atTop ∧
      (∀ n, YPrimeDistLe T (h n) H
        (2 * x * contractionFactor x ^ n / (1 - contractionFactor x))) ∧
      (∀ u r, H (u, r) = H (min u T, r)) ∧ ∀ r, H (0, r) = data r := by
  have hdiff := iterate_step_bound data hdata h hb hstep
  have hclamp := iterate_clamp data h hb hzero hstep
  have hdist (p : ℝ≥0 × ℝ≥0) (n : ℕ) :
      dist (h n p) (h (n + 1) p) ≤ 2 * x * contractionFactor x ^ n := by
    have hh := hdiff n (min p.1 T) (min_le_right _ _) p.2
    rw [← hclamp n, ← hclamp (n + 1)] at hh
    rw [Real.dist_eq, abs_sub_comm]
    exact (le_mul_of_one_le_left (abs_nonneg _)
      (one_le_pow₀ (primeWeight_ge_one (min p.1 T) p.2))).trans hh
  choose H hlim using fun p => cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric (contractionFactor x) (2 * x) hq (hdist p))
  have hrate (n : ℕ) (p : ℝ≥0 × ℝ≥0) :
      dist (h n p) (H p) ≤ 2 * x * contractionFactor x ^ n / (1 - contractionFactor x) :=
    dist_le_of_le_geometric_of_tendsto (contractionFactor x) (2 * x) hq (hdist p) (hlim p) n
  have hunif : TendstoUniformly (fun n p => h n p) H atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [(geometric_tendsto hx hq).eventually (gt_mem_nhds hε)] with n hn p
    rw [dist_comm]
    exact (hrate n p).trans_lt hn
  refine ⟨⟨H, hunif.continuous (Frequently.of_forall fun n => (h n).continuous)⟩,
    hunif, ?_, ?_, ?_⟩
  · intro n u hu r
    have hw : 0 ≤ primeWeight u r := zero_le_one.trans (primeWeight_ge_one u r)
    have hd (k : ℕ) : dist (primeWeight u r ^ 3 * h k (u, r))
        (primeWeight u r ^ 3 * h (k + 1) (u, r)) ≤
          2 * x * contractionFactor x ^ k := by
      rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (pow_nonneg hw 3), abs_sub_comm]
      exact hdiff k u hu r
    have hh := dist_le_of_le_geometric_of_tendsto (contractionFactor x) (2 * x) hq hd
      ((hlim (u, r)).const_mul (primeWeight u r ^ 3)) n
    simpa only [ContinuousMap.coe_mk, Real.dist_eq, ← mul_sub, abs_mul,
      abs_of_nonneg (pow_nonneg hw 3)] using hh
  · intro u r
    exact tendsto_nhds_unique (hlim (u, r))
      ((hlim (min u T, r)).congr (fun n => (hclamp n u r).symm))
  · intro r
    have htrace (n : ℕ) : h n (0, r) = data r := by
      cases n with
      | zero =>
        rw [hzero, translatedDataField_apply T data 0 r (bot_le : (0 : ℝ≥0) ≤ T)]
        simp only [zero_div, add_zero]
      | succ n => rw [hstep, linearStepMap_apply, linearStep_zero]
    exact tendsto_nhds_unique (hlim (0, r))
      (tendsto_const_nhds.congr (fun n => (htrace n).symm))

/-- Uniform equicontinuity of the radial derivatives and uniform Cauchy convergence
of the functions imply uniform Cauchy convergence of the derivatives, on a half-strip. -/
private theorem radial_derivatives_uniform_cauchy {T : ℝ} {F Q : ℕ → ℝ × ℝ → ℝ}
    (hc : ∀ n u, u ∈ Icc 0 T → ContinuousOn (fun r => F n (u, r)) (Ici 0))
    (hd : ∀ n u, u ∈ Icc 0 T → ∀ r, 0 < r →
      HasDerivAt (fun s => F n (u, s)) (Q n (u, r)) r)
    (he : UniformEquicontinuousOn Q (Icc 0 T ×ˢ Ici 0))
    (hf : UniformCauchySeqOn F atTop (Icc 0 T ×ˢ Ici 0)) :
    UniformCauchySeqOn Q atTop (Icc 0 T ×ˢ Ici 0) := by
  rw [← uniformEquicontinuous_restrict_iff] at he
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformEquicontinuous_iff.mp he (ε / 4) (by positivity)
  let t := δ / 2
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp hf (ε * t / 8) (by positivity)
  refine ⟨N, ?_⟩
  intro m hm n hn p hp
  obtain ⟨u, r⟩ := p
  have hr : 0 ≤ r := hp.2
  obtain ⟨c, hcr, hcq⟩ := exists_hasDerivAt_eq_slope
    (fun s => F m (u, s) - F n (u, s)) (fun s => Q m (u, s) - Q n (u, s))
    (show r < r + t by linarith)
    (((hc m u hp.1).sub (hc n u hp.1)).mono (by intro s hs; exact le_trans hr hs.1))
    (fun s hs => (hd m u hp.1 s (by linarith [hs.1])).sub
      (hd n u hp.1 s (by linarith [hs.1])))
  have hdist : dist (⟨(u, r), hp⟩ : Icc 0 T ×ˢ Ici (0 : ℝ))
      ⟨(u, c), hp.1, le_trans hr hcr.1.le⟩ < δ := by
    rw [Subtype.dist_eq, Prod.dist_eq, dist_self, max_eq_right dist_nonneg,
      Real.dist_eq, abs_of_neg (sub_neg.mpr hcr.1)]
    dsimp [t] at hcr
    linarith only [hcr.2, hδ]
  have hmQ := hmod ⟨(u, r), hp⟩ ⟨(u, c), hp.1, le_trans hr hcr.1.le⟩ hdist m
  have hnQ := hmod ⟨(u, r), hp⟩ ⟨(u, c), hp.1, le_trans hr hcr.1.le⟩ hdist n
  have hFr := hN m hm n hn (u, r) hp
  have hFt := hN m hm n hn (u, r + t) ⟨hp.1, add_nonneg hr ht.le⟩
  have hcsmall : |Q m (u, c) - Q n (u, c)| < ε / 4 := by
    rw [hcq, show r + t - r = t by ring, abs_div, abs_of_pos ht]
    apply (div_lt_iff₀ ht).mpr
    have htri := abs_sub (F m (u, r + t) - F n (u, r + t)) (F m (u, r) - F n (u, r))
    rw [Real.dist_eq] at hFr hFt
    linarith only [htri, hFr, hFt]
  change dist (Q m (u, r)) (Q n (u, r)) < ε
  have htri := dist_triangle4 (Q m (u, r)) (Q m (u, c)) (Q n (u, c)) (Q n (u, r))
  change dist (Q m (u, r)) (Q m (u, c)) < ε / 4 at hmQ
  change dist (Q n (u, r)) (Q n (u, c)) < ε / 4 at hnQ
  rw [dist_comm (Q n (u, c))] at htri
  rw [← Real.dist_eq] at hcsmall
  linarith only [htri, hmQ, hnQ, hcsmall, hε]

private theorem contDiffOn_limit_Ici {F : ℕ → ℝ → ℝ} {f q : ℝ → ℝ}
    (hc : Continuous f) (hq : ContinuousOn q (Ici 0))
    (hF : ∀ n, ContDiffOn ℝ 1 (F n) (Ici 0))
    (hconv : ∀ r ∈ Ici (0 : ℝ), Tendsto (fun n => F n r) atTop (𝓝 (f r)))
    (hqconv : TendstoUniformlyOn (fun n => derivWithin (F n) (Ici 0)) q atTop (Ici 0)) :
    ContDiffOn ℝ 1 f (Ici 0) ∧ ∀ r ∈ Ici (0 : ℝ), derivWithin f (Ici 0) r = q r := by
  have hint (r : ℝ) (hr : 0 < r) : HasDerivAt f (q r) r := by
    apply hasDerivAt_of_tendstoUniformlyOn (s := Ioi (0 : ℝ)) isOpen_Ioi
      (hqconv.mono Ioi_subset_Ici_self)
      (Eventually.of_forall fun n s hs =>
        (((hF n).differentiableOn (by norm_num)) s
          (show 0 ≤ s from le_of_lt hs)).hasDerivWithinAt.hasDerivAt
          (Ici_mem_nhds hs))
      (fun s hs => hconv s (show 0 ≤ s from le_of_lt hs)) hr
  have hall (r : ℝ) (hr : 0 ≤ r) : HasDerivWithinAt f (q r) (Ici 0) r := by
    rcases hr.eq_or_lt with hr | hr
    · subst r
      apply hasDerivWithinAt_Ici_of_tendsto_deriv
        (s := Ioi 0) (fun s hs => (hint s hs).differentiableAt.differentiableWithinAt)
        hc.continuousWithinAt self_mem_nhdsWithin
      apply ((hq 0 (by simp)).mono Ioi_subset_Ici_self).congr'
      filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with s hs
      exact (hint s hs).deriv.symm
    · exact (hint r hr).hasDerivWithinAt
  have heq (r : ℝ) (hr : r ∈ Ici (0 : ℝ)) : derivWithin f (Ici 0) r = q r :=
    (hall r hr).derivWithin (uniqueDiffOn_Ici 0 r hr)
  refine ⟨(contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ici 0)).mpr ⟨?_, ?_⟩, heq⟩
  · exact fun r hr => (hall r hr).differentiableWithinAt
  · exact hq.congr heq

private theorem memXBall_of_uniform_limit {T : ℝ≥0} {x : ℝ}
    (f : ℕ → C(ℝ≥0 × ℝ≥0, ℝ)) (hb : ∀ n, MemXBall T x (f n))
    (H : C(ℝ≥0 × ℝ≥0, ℝ)) (hlim : TendstoUniformly (fun n p => f n p) H atTop)
    (he : UniformEquicontinuousOn
      (fun n (p : ℝ × ℝ) => derivWithin (fun s : ℝ => f n (p.1.toNNReal, s.toNNReal))
        (Ici 0) p.2) (Icc 0 (T : ℝ) ×ˢ Ici 0)) :
    MemXBall T x H ∧ TendstoUniformlyOn
      (fun n (p : ℝ × ℝ) => derivWithin (fun s : ℝ => f n (p.1.toNNReal, s.toNNReal))
        (Ici 0) p.2)
      (fun p : ℝ × ℝ => derivWithin (fun s : ℝ => H (p.1.toNNReal, s.toNNReal))
        (Ici 0) p.2) atTop (Icc 0 (T : ℝ) ×ˢ Ici 0) := by
  let F := fun n (p : ℝ × ℝ) => f n (p.1.toNNReal, p.2.toNNReal)
  let Q := fun n (p : ℝ × ℝ) => derivWithin (fun s : ℝ => f n (p.1.toNNReal, s.toNNReal))
    (Ici 0) p.2
  have hFc (n : ℕ) (u : ℝ) : Continuous (fun r => F n (u, r)) := by
    dsimp [F]
    exact (f n).continuous.comp ((continuous_const (y := u.toNNReal)).prodMk
      continuous_real_toNNReal)
  have hQc : UniformCauchySeqOn Q atTop (Icc 0 (T : ℝ) ×ˢ Ici 0) := by
    refine radial_derivatives_uniform_cauchy (fun n u _ => (hFc n u).continuousOn) ?_ he ?_
    · intro n u hu r hr
      exact (((hb n).1 u.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hu.2)).differentiableOn
        (by norm_num) r hr.le).hasDerivWithinAt.hasDerivAt (Ici_mem_nhds hr)
    · exact (hlim.comp (fun p : ℝ × ℝ =>
        (p.1.toNNReal, p.2.toNNReal))).tendstoUniformlyOn.uniformCauchySeqOn
  let q := fun p => limUnder atTop (fun n => Q n p)
  have hqlim : TendstoUniformlyOn Q q atTop (Icc 0 (T : ℝ) ×ˢ Ici 0) :=
    hQc.tendstoUniformlyOn_of_tendsto (fun p hp => (hQc.cauchySeq hp).tendsto_limUnder)
  have hqcont : ContinuousOn q (Icc 0 (T : ℝ) ×ˢ Ici 0) :=
    hqlim.continuousOn (Frequently.of_forall fun n => (hb n).2.1)
  have hslices (u : ℝ≥0) (hu : u ≤ T) :
      ContDiffOn ℝ 1 (fun s : ℝ => H (u, s.toNNReal)) (Ici 0) ∧
      ∀ r ∈ Ici (0 : ℝ), derivWithin (fun s : ℝ => H (u, s.toNNReal)) (Ici 0) r = q (u, r) := by
    have hu' : (u : ℝ) ∈ Icc 0 (T : ℝ) := ⟨u.coe_nonneg, by exact_mod_cast hu⟩
    apply contDiffOn_limit_Ici
      (H.continuous.comp (continuous_const.prodMk continuous_real_toNNReal))
      (hqcont.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun r hr => ⟨hu', hr⟩)) (fun n => (hb n).1 u hu)
      (fun r _ => hlim.tendsto_at (u, r.toNNReal))
    simpa only [Q, Function.comp_def, Real.toNNReal_coe, id_eq, NNReal.val_eq_coe] using
      (hqlim.comp (fun r : ℝ => ((u : ℝ), r))).mono
        (show Ici (0 : ℝ) ⊆ _ from fun r hr => ⟨hu', hr⟩)
  have heq : EqOn q
      (fun p : ℝ × ℝ => derivWithin (fun s : ℝ => H (p.1.toNNReal, s.toNNReal)) (Ici 0) p.2)
      (Icc 0 (T : ℝ) ×ˢ Ici 0) := by
    intro p hp
    have hh := (hslices p.1.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hp.1.2)).2 p.2 hp.2
    simpa only [Real.coe_toNNReal _ hp.1.1] using hh.symm
  have hderiv := hqlim.congr_right heq
  refine ⟨⟨fun u hu => (hslices u hu).1, hderiv.continuousOn
    (Frequently.of_forall fun n => (hb n).2.1), ?_⟩, hderiv⟩
  intro u hu r
  have hp : ((u : ℝ), (r : ℝ)) ∈ Icc 0 (T : ℝ) ×ˢ Ici 0 :=
    ⟨⟨u.coe_nonneg, by exact_mod_cast hu⟩, r.coe_nonneg⟩
  have hdlim := hderiv.tendsto_at hp
  simp only [Q, Real.toNNReal_coe] at hdlim
  exact le_of_tendsto
    (((hlim.tendsto_at (u, r)).abs.const_mul ((1 + (r : ℝ)) ^ 3)).add
      (hdlim.abs.const_mul ((1 + (r : ℝ)) ^ 4)))
    (Eventually.of_forall fun n => (hb n).2.2 u hu r)


theorem primeIterate_limit {T : ℝ≥0} {x : ℝ} (hx : 0 < x)
    (hq : contractionFactor x < 1) (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
    (h : ℕ → C(ℝ≥0 × ℝ≥0, ℝ)) (hb : ∀ n, MemXPrimeBall T x (h n))
    (hzero : h 0 = translatedDataField T data)
    (hstep : ∀ n, h (n + 1) = linearStepMap (hb n).1 data) :
    ∃ H : C(ℝ≥0 × ℝ≥0, ℝ), ∃ hH : MemXPrimeBall T x H,
      (∀ n : ℕ, YPrimeDistLe T (h n) H
        (2 * x * contractionFactor x ^ n / (1 - contractionFactor x))) ∧
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => derivWithin
        (fun z : ℝ => h n (p.1.toNNReal, z.toNNReal)) (Ici 0) p.2)
        (fun p : ℝ × ℝ => derivWithin
          (fun z : ℝ => H (p.1.toNNReal, z.toNNReal)) (Ici 0) p.2)
        atTop (Icc 0 (T : ℝ) ×ˢ Ici 0) ∧
      linearStepMap hH.1 data = H ∧ ∀ r, H (0, r) = data r := by
  obtain ⟨H, hlim, hrate, hclamp, htrace⟩ :=
    iterate_continuous_limit hx.le hq data hdata h hb hzero hstep
  have hbX (n : ℕ) : MemXBall T x (h n) := (hb n).1
  have he := translated_iterate_deriv_uniformEquicontinuousOn data hdata h hbX hzero hstep
  obtain ⟨hHX, hderiv⟩ := memXBall_of_uniform_limit h hbX H hlim he
  have hH : MemXPrimeBall T x H := by
    refine ⟨hHX, ?_⟩
    intro u hu r
    have hp : ((u : ℝ), (r : ℝ)) ∈ Icc 0 (T : ℝ) ×ˢ Ici 0 :=
      ⟨⟨u.coe_nonneg, by exact_mod_cast hu⟩, r.coe_nonneg⟩
    have hdlim := hderiv.tendsto_at hp
    simp only [Real.toNNReal_coe] at hdlim
    exact le_of_tendsto
      (((hlim.tendsto_at (u, r)).abs.const_mul (primeWeight u r ^ 3)).add
        (hdlim.abs.const_mul (primeWeight u r ^ 4)))
      (Eventually.of_forall fun n => (hb n).2 u hu r)
  refine ⟨H, hH, hrate, hderiv, ?_, htrace⟩
  have hY (n : ℕ) (u : ℝ≥0) (hu : u ≤ T) (r : ℝ≥0) :
      (1 + (r : ℝ)) ^ 3 * |H (u, r) - h n (u, r)| ≤
        2 * x * contractionFactor x ^ n / (1 - contractionFactor x) := by
    have hw : 1 + (r : ℝ) ≤ primeWeight u r := by
      dsimp only [primeWeight]
      exact le_add_of_nonneg_right (div_nonneg u.coe_nonneg (by norm_num))
    rw [abs_sub_comm]
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hw 3)
      (abs_nonneg _)).trans (hrate n u hu r)
  have hfix (u r : ℝ≥0) (hu : u ≤ T) : linearStepMap hH.1 data (u, r) = H (u, r) := by
    let c := (T : ℝ) * exp (π * x ^ 2 / 12 * (T : ℝ)) *
      (π * x ^ 2 * (37 / 6 + 2 * π * x ^ 2))
    have hineq (n : ℕ) : (1 + (r : ℝ)) ^ 3 *
        |linearStepMap hH.1 data (u, r) - h (n + 1) (u, r)| ≤
          c * (2 * x * contractionFactor x ^ n / (1 - contractionFactor x)) := by
      have hSn : MemXBall T x (linearStepMap (hb n).1 data) := by
        rw [← hstep n]
        exact (hb (n + 1)).1
      have hh := linearStep_y_lipschitz hH.1 (hb n).1 data hdata.1.1 hSn (hY n) u r hu
      simpa only [hstep, linearStepMap_apply] using hh
    have hle : (1 + (r : ℝ)) ^ 3 * |linearStepMap hH.1 data (u, r) - H (u, r)| ≤ 0 := by
      have ha := (((hlim.tendsto_at (u, r)).comp (tendsto_add_atTop_nat 1)).const_sub
        (linearStepMap hH.1 data (u, r))).abs.const_mul ((1 + (r : ℝ)) ^ 3)
      have hz : Tendsto
          (fun n : ℕ => c * (2 * x * contractionFactor x ^ n / (1 - contractionFactor x)))
          atTop (𝓝 0) := by
        simpa only [mul_zero] using (geometric_tendsto hx.le hq).const_mul c
      exact le_of_tendsto_of_tendsto ha hz (Eventually.of_forall hineq)
    have hw : 0 < (1 + (r : ℝ)) ^ 3 := by positivity
    have ha : |linearStepMap hH.1 data (u, r) - H (u, r)| ≤ 0 :=
      le_of_mul_le_mul_left (by simpa only [mul_zero] using hle) hw
    exact sub_eq_zero.mp (abs_nonpos_iff.mp ha)
  ext p
  obtain ⟨u, r⟩ := p
  rw [XLim.linearStepMap_clamp hH.1 data u r, hclamp u r]
  exact hfix (min u T) r (min_le_right _ _)

end XPL
end Christodoulou.Bondi
