module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Real



public section

open Set MeasureTheory Filter Topology Asymptotics Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem IsClassicalSolution.isSlice {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : Christodoulou.Bondi.IsClassicalSolution u₀ H := by assumption) {u : ℝ≥0}
    (hu : u ≤ u₀ := by assumption) : IsSlice (H.curry u) := by
  obtain ⟨h1, ⟨C, hC⟩, -⟩ := hH
  refine ⟨?_, ?_⟩
  · have hmap : MapsTo (fun s : ℝ => ((u : ℝ), s)) (Ici 0) (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) :=
      fun s hs => ⟨⟨u.2, by exact_mod_cast hu⟩, hs⟩
    have := h1.comp (contDiffOn_const.prodMk contDiffOn_id) hmap
    refine this.congr fun s _ => ?_
    simp [Function.comp, ContinuousMap.curry_apply]
  · refine IsBigO.of_bound C ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have hb := hC u hu (Real.toNNReal s)
    rw [Real.coe_toNNReal s hs.le] at hb
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (zpow_pos hs _)]
    calc |(H.curry u) (Real.toNNReal s)| = |H (u, Real.toNNReal s)| := rfl
      _ ≤ C * (1 + s) ^ (-3 : ℤ) := hb
      _ ≤ C * s ^ (-3 : ℤ) := by
          have hC0 : 0 ≤ C := by
            have := hC 0 (by positivity) 0
            simp at this
            linarith [abs_nonneg (H (0, 0))]
          gcongr
          rw [zpow_neg, zpow_neg, zpow_ofNat, zpow_ofNat]
          exact inv_anti₀ (pow_pos hs 3) (pow_le_pow_left₀ hs.le (by linarith) 3)

end Christodoulou.Bondi.Provider
