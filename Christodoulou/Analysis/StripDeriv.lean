module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.TangentCone.Prod
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral



public section

open Set MeasureTheory Filter Topology

namespace Christodoulou.Analysis

/-- The partial derivative in the first variable at an interior time, including on the edge
`s = 0` of the half-line. -/
theorem hasDerivAt_fst_of_contDiffOn {F : ℝ × ℝ → ℝ} {u₀ : ℝ}
    (hF : ContDiffOn ℝ 1 F (Icc 0 u₀ ×ˢ Ici 0)) {u s : ℝ} (hu : u ∈ Ioo 0 u₀) (hs : 0 ≤ s) :
    HasDerivAt (fun v : ℝ => F (v, s))
      (fderivWithin ℝ F (Icc 0 u₀ ×ˢ Ici 0) (u, s) (1, 0)) u := by
  have hd := (hF.differentiableOn one_ne_zero (u, s)
    ⟨⟨hu.1.le, hu.2.le⟩, hs⟩).hasFDerivWithinAt
  apply hd.comp_hasDerivAt u ((hasDerivAt_id u).prodMk (hasDerivAt_const u s))
  filter_upwards [Icc_mem_nhds hu.1 hu.2] with v hv
  exact ⟨hv, hs⟩

/-- The partial derivative in the second variable at an interior point. -/
theorem hasDerivAt_snd_of_contDiffOn {F : ℝ × ℝ → ℝ} {u₀ : ℝ}
    (hF : ContDiffOn ℝ 1 F (Icc 0 u₀ ×ˢ Ici 0)) {u s : ℝ} (hu : u ∈ Ioo 0 u₀) (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => F (u, t))
      (fderivWithin ℝ F (Icc 0 u₀ ×ˢ Ici 0) (u, s) (0, 1)) s := by
  have hd := (hF.differentiableOn one_ne_zero (u, s)
    ⟨⟨hu.1.le, hu.2.le⟩, hs.le⟩).hasFDerivWithinAt
  apply hd.comp_hasDerivAt s ((hasDerivAt_const s u).prodMk (hasDerivAt_id s))
  filter_upwards [Ici_mem_nhds hs] with t ht
  exact ⟨⟨hu.1.le, hu.2.le⟩, ht⟩

/-- The directional within-derivatives are continuous on the closed strip (for `u₀ > 0`). -/
theorem continuousOn_fderivWithin_apply_of_contDiffOn {F : ℝ × ℝ → ℝ} {u₀ : ℝ}
    (hF : ContDiffOn ℝ 1 F (Icc 0 u₀ ×ˢ Ici 0)) (hu₀ : 0 < u₀) (w : ℝ × ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => fderivWithin ℝ F (Icc 0 u₀ ×ˢ Ici 0) p w)
      (Icc 0 u₀ ×ˢ Ici 0) := by
  exact (hF.continuousOn_fderivWithin
    ((uniqueDiffOn_Icc hu₀).prod (uniqueDiffOn_Ici 0)) le_rfl).clm_apply continuousOn_const

/-- Differentiation in the first variable under the integral over `[0, r]`. -/
theorem hasDerivAt_intervalIntegral_fst_of_contDiffOn {F : ℝ × ℝ → ℝ} {u₀ : ℝ}
    (hF : ContDiffOn ℝ 1 F (Icc 0 u₀ ×ˢ Ici 0)) {u r : ℝ} (hu : u ∈ Ioo 0 u₀) (hr : 0 ≤ r) :
    HasDerivAt (fun v : ℝ => ∫ s in (0 : ℝ)..r, F (v, s))
      (∫ s in (0 : ℝ)..r, fderivWithin ℝ F (Icc 0 u₀ ×ˢ Ici 0) (u, s) (1, 0)) u := by
  obtain ⟨a, ha, hau⟩ := exists_between hu.1
  obtain ⟨b, hub, hb⟩ := exists_between hu.2
  have hsub : Icc a b ×ˢ Icc 0 r ⊆ Icc 0 u₀ ×ˢ Ici 0 := by
    intro p hp
    exact ⟨⟨ha.le.trans hp.1.1, hp.1.2.trans hb.le⟩, hp.2.1⟩
  have hD := continuousOn_fderivWithin_apply_of_contDiffOn hF (hu.1.trans hu.2) (1, 0)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hD.mono hsub)
  have hslice (v : ℝ) (hv : v ∈ Icc 0 u₀) :
      IntervalIntegrable (fun s : ℝ => F (v, s)) volume 0 r := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hr]
    exact hF.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨hv, hs.1⟩)
  have hDslice : IntervalIntegrable
      (fun s : ℝ => fderivWithin ℝ F (Icc 0 u₀ ×ˢ Ici 0) (u, s) (1, 0)) volume 0 r := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hr]
    exact hD.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨⟨hu.1.le, hu.2.le⟩, hs.1⟩)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun v s => fderivWithin ℝ F (Icc 0 u₀ ×ˢ Ici 0) (v, s) (1, 0))
    (bound := fun _ => C) (Icc_mem_nhds hau hub) ?_
    (hslice u ⟨hu.1.le, hu.2.le⟩) (intervalIntegrable_iff.mp hDslice).aestronglyMeasurable
    ?_ intervalIntegrable_const ?_).2
  · filter_upwards [Icc_mem_nhds hu.1 hu.2] with v hv
    exact (intervalIntegrable_iff.mp (hslice v hv)).aestronglyMeasurable
  · filter_upwards with s hs v hv
    rw [uIoc_of_le hr] at hs
    exact hC (v, s) ⟨hv, hs.1.le, hs.2⟩
  · filter_upwards with s hs v hv
    rw [uIoc_of_le hr] at hs
    exact hasDerivAt_fst_of_contDiffOn hF ⟨ha.trans_le hv.1, hv.2.trans_lt hb⟩ hs.1.le

end Christodoulou.Analysis
