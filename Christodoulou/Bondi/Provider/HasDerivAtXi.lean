module
public import Christodoulou.Frozen.Bondi.Xi
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Christodoulou.Frozen.Bondi.IntervalIntegrableXi
import Christodoulou.Frozen.Radial.ContinuousMean
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem hasDerivAt_xi {h : C(ℝ≥0, ℝ)} {hh : IsSlice h} {r : ℝ≥0}
    (hr : 0 < r := by assumption) :
    HasDerivAt (fun s : ℝ => xi h hh (Real.toNNReal s))
      (gBar h hh r * (h r - mean h r) / (r : ℝ)) (r : ℝ) := by
  set f : ℝ → ℝ := fun s => gBar h hh (Real.toNNReal s) *
    (h (Real.toNNReal s) - mean h (Real.toNNReal s)) / s with hf
  have hrpos : (0 : ℝ) < r := hr
  have hcont : ContinuousOn f (Ioi 0) := by
    refine ContinuousOn.div (Continuous.continuousOn ?_) continuousOn_id fun s hs => ne_of_gt hs
    exact ((continuous_mean (f := gMap h hh)).comp continuous_real_toNNReal).mul
      ((h.continuous.comp continuous_real_toNNReal).sub
        ((continuous_mean (f := h)).comp continuous_real_toNNReal))
  have hII : IntervalIntegrable f volume 0 (r : ℝ) := intervalIntegrable_xi h hh r
  have hFTC : HasDerivAt (fun x => ∫ s in (0 : ℝ)..x, f s) (f r) r :=
    intervalIntegral.integral_hasDerivAt_right hII
      ((hcont.mono (fun _ h => h)).stronglyMeasurableAtFilter isOpen_Ioi _ hrpos)
      (hcont.continuousAt (Ioi_mem_nhds hrpos))
  have hval : f r = gBar h hh r * (h r - mean h r) / (r : ℝ) := by
    simp [hf, Real.toNNReal_coe]
  rw [hval] at hFTC
  refine hFTC.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hrpos] with s hs
  simp only [xi, Real.coe_toNNReal s (le_of_lt hs), hf]

end Christodoulou.Bondi.Provider
