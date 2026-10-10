module
public import Christodoulou.Frozen.Bondi.StepDelta
public import Christodoulou.Frozen.Bondi.XBallIterate
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.IsDecaySlice
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Christodoulou.Frozen.Bondi.LinearStepMapApply
import Christodoulou.Frozen.Bondi.XBallIterateRec
import Christodoulou.Frozen.Bondi.Lemma2
import Christodoulou.Frozen.Bondi.IterateDerivUniformEquicontinuousOn
import Christodoulou.Frozen.Bondi.LinearStepYLipschitz
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.UniformSpace.UniformApproximation



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

namespace XLim

/-- The linear step is constant in time beyond the end of the strip. -/
theorem linearStepMap_clamp {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (data : C(ℝ≥0, ℝ)) (u r : ℝ≥0) :
    linearStepMap hH data (u, r) = linearStepMap hH data (min u u₀, r) := by
  simp only [linearStepMap_apply, linearStep, NNReal.coe_min, min_assoc, min_self]

variable {u₀ : ℝ≥0} {d x₁ : ℝ}
    (hd : 0 ≤ d) (hx : 2 * d < x₁) (hT : (u₀ : ℝ) < stepEta x₁ d)
    (hδ : (u₀ : ℝ) < stepDelta x₁)
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 * |derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) r| ≤ d)

include hd hx hT hdata hbound in
private theorem iterate_clamp (n : ℕ) (u r : ℝ≥0) :
    (xBallIterate hd hx hT data hdata hbound n).val (u, r) = (xBallIterate
          hd hx hT data hdata hbound n).val (min u u₀, r) := by
  obtain ⟨hz, hs, _⟩ := xBallIterate_rec hd hx hT data hdata hbound
  cases n with
  | zero => rw [hz]; rfl
  | succ n => rw [hs]; exact linearStepMap_clamp _ _ _ _

include hd hx hT hδ hdata hbound in
private theorem iterate_step_bound (n : ℕ) (u : ℝ≥0) (hu : u ≤ u₀) (r : ℝ≥0) :
    (1 + (r : ℝ)) ^ 3 * |(xBallIterate
          hd hx hT data hdata hbound (n + 1)).val (u, r) - (xBallIterate
                hd hx hT data hdata hbound n).val (u, r)| ≤
      2 * x₁ / 2 ^ n := by
  induction n generalizing u r with
  | zero =>
    have h0 := (xBallIterate hd hx hT data hdata hbound 0).property.2.2 u hu r
    have h1 := (xBallIterate hd hx hT data hdata hbound 1).property.2.2 u hu r
    have hp : 0 ≤ (1 + (r : ℝ)) ^ 3 := by positivity
    have ht := mul_le_mul_of_nonneg_left (abs_sub ((xBallIterate
          hd hx hT data hdata hbound 1).val (u, r)) ((xBallIterate
                hd hx hT data hdata hbound 0).val (u, r))) hp
    have hq0 : 0 ≤ (1 + (r : ℝ)) ^ 4 *
        |derivWithin (fun s : ℝ => (xBallIterate
              hd hx hT data hdata hbound 0).val (u, s.toNNReal)) (Ici 0) r| := by positivity
    have hq1 : 0 ≤ (1 + (r : ℝ)) ^ 4 *
        |derivWithin (fun s : ℝ => (xBallIterate
              hd hx hT data hdata hbound 1).val (u, s.toNNReal)) (Ici 0) r| := by positivity
    simp only [pow_zero, div_one]
    linarith only [h0, h1, ht, hq0, hq1]
  | succ n ih =>
    obtain ⟨δ, hδeq, _, hc⟩ := lemma2 x₁
    have hb := hc d hd hx u₀ hT (hδeq ▸ hδ) data hdata hbound n
      (2 * x₁ / 2 ^ n) ih u hu r
    simpa only [Nat.succ_eq_add_one, pow_succ, div_div] using hb

include hd hx hT hδ hdata hbound in
private theorem iterate_continuous_limit :
    ∃ H : C(ℝ≥0 × ℝ≥0, ℝ),
      TendstoUniformly (fun n p => (xBallIterate hd hx hT data hdata hbound n).val p) H atTop ∧
      (∀ (n : ℕ) (u r : ℝ≥0), (1 + (r : ℝ)) ^ 3 * |(xBallIterate
            hd hx hT data hdata hbound n).val (u, r) - H (u, r)| ≤
        4 * x₁ / 2 ^ n) ∧
      (∀ u r, H (u, r) = H (min u u₀, r)) ∧
      ∀ r, H (0, r) = data r := by
  have hstep (p : ℝ≥0 × ℝ≥0) (n : ℕ) :
      dist ((xBallIterate hd hx hT data hdata hbound n).val p) ((xBallIterate
            hd hx hT data hdata hbound (n + 1)).val p) ≤ (4 * x₁) / 2 / 2 ^ n := by
    have hb := iterate_step_bound hd hx hT hδ data hdata hbound n
      (min p.1 u₀) (min_le_right _ _) p.2
    rw [← iterate_clamp hd hx hT data hdata hbound n,
      ← iterate_clamp hd hx hT data hdata hbound (n + 1)] at hb
    have hw : 1 ≤ (1 + (p.2 : ℝ)) ^ 3 := one_le_pow₀ (by linarith [p.2.coe_nonneg])
    rw [Real.dist_eq, abs_sub_comm]
    have hab := abs_nonneg ((xBallIterate hd hx hT data hdata hbound (n + 1)).val p - (xBallIterate
          hd hx hT data hdata hbound n).val p)
    have he : 4 * x₁ / 2 = 2 * x₁ := by ring
    rw [he]
    exact (le_mul_of_one_le_left hab hw).trans hb
  choose H hlim using fun p => cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric_two (hstep p))
  have hrate (n : ℕ) (p : ℝ≥0 × ℝ≥0) :
      dist ((xBallIterate hd hx hT data hdata hbound n).val p) (H p) ≤ 4 * x₁ / 2 ^ n :=
    dist_le_of_le_geometric_two_of_tendsto (hstep p) (hlim p) n
  have hgeom : Tendsto (fun n : ℕ => 4 * x₁ / 2 ^ n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul, inv_pow, mul_zero] using (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 : ℝ) / 2 < 1)) :
      Tendsto (fun n : ℕ => (4 * x₁) * ((1 : ℝ) / 2) ^ n) atTop (𝓝 ((4 * x₁) * 0)))
  have hunif : TendstoUniformly (fun n p => (xBallIterate
        hd hx hT data hdata hbound n).val p) H atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [hgeom.eventually (gt_mem_nhds hε)] with n hn p
    rw [dist_comm]
    exact (hrate n p).trans_lt hn
  refine ⟨⟨H, hunif.continuous (Frequently.of_forall fun n => (xBallIterate
        hd hx hT data hdata hbound n).val.continuous)⟩,
    hunif, ?_, ?_, ?_⟩
  · intro n u r
    have hb (k : ℕ) : dist ((1 + (r : ℝ)) ^ 3 * (xBallIterate
          hd hx hT data hdata hbound k).val (u, r))
        ((1 + (r : ℝ)) ^ 3 * (xBallIterate
              hd hx hT data hdata hbound (k + 1)).val (u, r)) ≤ (4 * x₁) / 2 / 2 ^ k := by
      have hb := iterate_step_bound hd hx hT hδ data hdata hbound k
        (min u u₀) (min_le_right _ _) r
      rw [← iterate_clamp hd hx hT data hdata hbound k,
        ← iterate_clamp hd hx hT data hdata hbound (k + 1)] at hb
      rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (by positivity), abs_sub_comm]
      convert hb using 1; ring
    have hh := dist_le_of_le_geometric_two_of_tendsto hb
      ((hlim (u, r)).const_mul ((1 + (r : ℝ)) ^ 3)) n
    simpa only [ContinuousMap.coe_mk, Real.dist_eq, ← mul_sub, abs_mul,
      abs_of_nonneg (show 0 ≤ (1 + (r : ℝ)) ^ 3 by positivity)] using hh
  · intro u r
    exact tendsto_nhds_unique (hlim (u, r))
      ((hlim (min u u₀, r)).congr (fun n => (iterate_clamp hd hx hT data hdata hbound n u r).symm))
  · intro r
    exact tendsto_nhds_unique (hlim (0, r))
      (tendsto_const_nhds.congr (fun n =>
        ((xBallIterate_rec hd hx hT data hdata hbound).2.2 n r).symm))

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

/-- The iterates and radial derivatives converge to a fixed point in the closed `X`-ball. -/
theorem xBallIterate_limit {u₀ : ℝ≥0} {d x₁ : ℝ}
    (hd : 0 ≤ d) (hx : 2 * d < x₁) (hT : (u₀ : ℝ) < stepEta x₁ d)
    (hδ : (u₀ : ℝ) < stepDelta x₁)
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 * |derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) r| ≤ d) :
    ∃ H : C(ℝ≥0 × ℝ≥0, ℝ), ∃ hH : MemXBall u₀ x₁ H,
      (∀ n : ℕ, ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 *
        |(xBallIterate hd hx hT data hdata hbound n).val (u, r) - H (u, r)| ≤ 4 * x₁ / 2 ^ n) ∧
      TendstoUniformlyOn
        (fun n (p : ℝ × ℝ) => derivWithin
          (fun s : ℝ => (xBallIterate hd hx hT data hdata hbound n).val
            (p.1.toNNReal, s.toNNReal)) (Ici 0) p.2)
        (fun p : ℝ × ℝ => derivWithin (fun s : ℝ => H (p.1.toNNReal, s.toNNReal)) (Ici 0) p.2)
        atTop (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) ∧
      linearStepMap hH data = H ∧
      ∀ r : ℝ≥0, H (0, r) = data r := by
  obtain ⟨H, hlim, hrate, hclamp, htrace⟩ :=
    iterate_continuous_limit hd hx hT hδ data hdata hbound
  let f := fun n => (xBallIterate hd hx hT data hdata hbound n).val
  have hb (n : ℕ) : MemXBall u₀ x₁ (f n) := (xBallIterate hd hx hT data hdata hbound n).property
  obtain ⟨hzero, hstep, _⟩ := xBallIterate_rec hd hx hT data hdata hbound
  have he := iterate_deriv_uniformEquicontinuousOn data f hb hzero hstep
  obtain ⟨hH, hderiv⟩ := memXBall_of_uniform_limit f hb H hlim he
  refine ⟨H, hH, (fun n u _ r => hrate n u r), hderiv, ?_, htrace⟩
  have hgeom : Tendsto (fun n : ℕ => 4 * x₁ / 2 ^ n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul, inv_pow, mul_zero] using
      (tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 : ℝ) / 2 < 1)) :
        Tendsto (fun n : ℕ => (4 * x₁) * ((1 : ℝ) / 2) ^ n) atTop (𝓝 ((4 * x₁) * 0)))
  have hfix (u r : ℝ≥0) (hu : u ≤ u₀) : linearStepMap hH data (u, r) = H (u, r) := by
    let c := (u₀ : ℝ) * exp (π * x₁ ^ 2 / 12 * (u₀ : ℝ)) *
      (π * x₁ ^ 2 * (37 / 6 + 2 * π * x₁ ^ 2))
    have hineq (n : ℕ) : (1 + (r : ℝ)) ^ 3 *
        |linearStepMap hH data (u, r) - f (n + 1) (u, r)| ≤ c * (4 * x₁ / 2 ^ n) := by
      have hSn : MemXBall u₀ x₁ (linearStepMap (hb n) data) := by
        rw [← hstep n]; exact hb (n + 1)
      have hh := linearStep_y_lipschitz hH (hb n) data hdata.1.1 hSn
        (fun v _ s => by simpa only [abs_sub_comm] using hrate n v s) u r hu
      simpa only [linearStepMap_apply, hstep, f] using hh
    have hle : (1 + (r : ℝ)) ^ 3 * |linearStepMap hH data (u, r) - H (u, r)| ≤ 0 := by
      have ha := (((hlim.tendsto_at (u, r)).comp (tendsto_add_atTop_nat 1)).const_sub
        (linearStepMap hH data (u, r))).abs.const_mul ((1 + (r : ℝ)) ^ 3)
      have hz : Tendsto (fun n : ℕ => c * (4 * x₁ / 2 ^ n)) atTop (𝓝 0) := by
        simpa only [mul_zero] using hgeom.const_mul c
      exact le_of_tendsto_of_tendsto ha hz (Eventually.of_forall hineq)
    have hw : 0 < (1 + (r : ℝ)) ^ 3 := by positivity
    have ha : |linearStepMap hH data (u, r) - H (u, r)| ≤ 0 := by
      exact le_of_mul_le_mul_left (by simpa only [mul_zero] using hle) hw
    exact sub_eq_zero.mp (abs_nonpos_iff.mp ha)
  ext p
  obtain ⟨u, r⟩ := p
  rw [linearStepMap_clamp hH data u r, hclamp u r]
  exact hfix (min u u₀) r (min_le_right _ _)

end XLim

end Christodoulou.Bondi
