module
public import Christodoulou.Frozen.Bondi.G
import Christodoulou.Bondi.GBasic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

/-- For `r > 0`, `∂_r g = 4π g (h − h̄)²/r`: the FTC at the continuity point `r` of `F`, then the
chain rule for `exp`. -/
theorem hasDerivAt_g {h : C(ℝ≥0, ℝ)} {hh : IsSlice h} {r : ℝ≥0} (hr : 0 < r := by assumption) :
    HasDerivAt (fun s : ℝ => g h hh (Real.toNNReal s))
      (4 * π * g h hh r * (h r - mean h r) ^ 2 / (r : ℝ)) (r : ℝ) := by
  have hr' : (0 : ℝ) < r := hr
  have hFTC : HasDerivAt (fun x : ℝ => ∫ s in (0 : ℝ)..x, tailIntegrand h s)
      (tailIntegrand h r) (r : ℝ) :=
    intervalIntegral.integral_hasDerivAt_right (integrable_tailIntegrand h hh).intervalIntegrable
      (measurable_tailIntegrand h).aestronglyMeasurable.stronglyMeasurableAtFilter
      ((continuousOn_tailIntegrand h).continuousAt (Ioi_mem_nhds hr'))
  have hE := ((hFTC.const_sub (∫ s in Ioi (0 : ℝ), tailIntegrand h s)).const_mul (-(4 * π))).exp
  have heq : (fun s : ℝ => g h hh (Real.toNNReal s)) =ᶠ[𝓝 (r : ℝ)] fun x =>
      Real.exp (-(4 * π) * ((∫ s in Ioi (0 : ℝ), tailIntegrand h s) -
        ∫ s in (0 : ℝ)..x, tailIntegrand h s)) := by
    filter_upwards [lt_mem_nhds hr'] with s hs
    rw [g_eq h hh, Real.coe_toNNReal s hs.le]
  refine (hE.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [← g_eq h hh r]
  simp only [tailIntegrand, Real.toNNReal_coe]
  ring

end Christodoulou.Bondi.Provider
