module
public import Christodoulou.Frozen.Bondi.Mass
public import Christodoulou.Frozen.Bondi.GPos
public import Christodoulou.Frozen.Bondi.MonotoneG
public import Christodoulou.Frozen.Bondi.HasDerivAtG
public import Christodoulou.Frozen.Radial.MeanZero
public import Christodoulou.Frozen.Radial.MeanEqIntegral
public import Christodoulou.Frozen.Radial.HasDerivAtMean
public import Christodoulou.Frozen.Radial.ContinuousMean



public section

open Set MeasureTheory Filter Topology Asymptotics Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

theorem gMap_apply (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) (r : ℝ≥0) : gMap h hh r = g h hh r := rfl

/-- The centre value `ḡ(0) = g(0)`. -/
theorem gBar_zero (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) : gBar h hh 0 = g h hh 0 :=
  mean_zero (gMap h hh)

/-- `ḡ(r) = r⁻¹ ∫₀ʳ g` for `r > 0`. -/
theorem gBar_eq_integral (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) (r : ℝ≥0) (hr : 0 < r) :
    gBar h hh r = (r : ℝ)⁻¹ * ∫ s in (0 : ℝ)..(r : ℝ), g h hh (Real.toNNReal s) :=
  mean_eq_integral (gMap h hh) r hr

theorem continuous_gBar (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) : Continuous (gBar h hh) :=
  continuous_mean (gMap h hh)

theorem gBar_pos (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) (r : ℝ≥0) : 0 < gBar h hh r := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [gBar_zero]; exact g_pos h hh 0
  · have hr' : (0 : ℝ) < r := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hr)
    rw [gBar_eq_integral h hh r (pos_iff_ne_zero.2 hr)]
    refine mul_pos (inv_pos.2 hr') ?_
    have hc : Continuous fun s : ℝ => g h hh (Real.toNNReal s) :=
      (continuous_g h hh).comp continuous_real_toNNReal
    exact intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable _ _)
      (fun s _ => g_pos h hh _) hr'


theorem hasDerivAt_gBar (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) (r : ℝ≥0) (hr : 0 < r) :
    HasDerivAt (fun s : ℝ => gBar h hh (Real.toNNReal s))
      ((g h hh r - gBar h hh r) / (r : ℝ)) (r : ℝ) := by
  have := hasDerivAt_mean (gMap h hh) r hr
  exact this

/-- The mass function is continuous on `[0, ∞)`. -/
theorem continuous_mass (h : C(ℝ≥0, ℝ)) (hh : IsSlice h) : Continuous (mass h hh) := by
  unfold mass
  exact (NNReal.continuous_coe.div_const 2).mul (continuous_const.sub
    ((continuous_gBar h hh).div (continuous_g h hh) fun r => (g_pos h hh r).ne'))

end Christodoulou.Bondi
