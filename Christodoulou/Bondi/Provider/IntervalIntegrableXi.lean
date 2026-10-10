module
public import Christodoulou.Frozen.Bondi.GBar
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Christodoulou.Frozen.Radial.ContinuousMean
import Christodoulou.Radial.MeanC1
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Integral.Bochner.Basic



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem intervalIntegrable_xi {h : C(ℝ≥0, ℝ)} {hh : IsSlice h} {r : ℝ≥0} :
    IntervalIntegrable
      (fun s : ℝ => gBar h hh (Real.toNNReal s) *
        (h (Real.toNNReal s) - mean h (Real.toNNReal s)) / s) volume 0 (r : ℝ) := by
  set R : ℝ := (r : ℝ) with hRdef
  have hR : 0 ≤ R := r.2
  -- Lipschitz bound for the lift of `h` on `[0, R]`.
  obtain ⟨K, hK⟩ := (hh.1.mono (Icc_subset_Ici_self : Icc 0 R ⊆ Ici 0)).exists_lipschitzOnWith
    one_ne_zero (convex_Icc 0 R) isCompact_Icc
  -- `ḡ` is continuous, hence bounded on `[0, R]`.
  have hgc : Continuous fun s : ℝ => gBar h hh (Real.toNNReal s) :=
    (continuous_mean (f := gMap h hh)).comp continuous_real_toNNReal
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 R) hgc.continuousOn
  have hmeas : Continuous fun s : ℝ => gBar h hh (Real.toNNReal s) *
      (h (Real.toNNReal s) - mean h (Real.toNNReal s)) :=
    hgc.mul ((h.continuous.comp continuous_real_toNNReal).sub
      ((continuous_mean (f := h)).comp continuous_real_toNNReal))
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR]
  refine Measure.integrableOn_of_bounded (M := B * K) measure_Ioc_lt_top.ne
    (hmeas.measurable.div measurable_id).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hs' : s ∈ Icc 0 R := ⟨hs.1.le, hs.2⟩
  have h1 := abs_sub_mean_le h hK hs'
  have h2 := hB s hs'
  rw [Real.norm_eq_abs] at h2 ⊢
  rw [abs_div, abs_mul, abs_of_pos hs.1, div_le_iff₀ hs.1]
  calc |gBar h hh (Real.toNNReal s)| * |h (Real.toNNReal s) - mean h (Real.toNNReal s)|
      ≤ B * (K * s) := mul_le_mul h2 h1 (abs_nonneg _) ((abs_nonneg _).trans h2)
    _ = B * K * s := by ring

end Christodoulou.Bondi.Provider
