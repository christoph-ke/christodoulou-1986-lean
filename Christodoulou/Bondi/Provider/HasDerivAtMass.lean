module
public import Christodoulou.Frozen.Bondi.Mass
import Christodoulou.Bondi.GBarBasic
import Mathlib.Analysis.Calculus.Deriv.Mul



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

/-- (4.4): for `r > 0`, `∂_r m = 2π (ḡ/g)(h − h̄)²`, by the product and quotient rules with
`g′ = 4π g (h − h̄)²/r` and `ḡ′ = (g − ḡ)/r`. -/
theorem hasDerivAt_mass {h : C(ℝ≥0, ℝ)} {hh : IsSlice h} {r : ℝ≥0} (hr : 0 < r := by assumption) :
    HasDerivAt (fun s : ℝ => mass h hh (Real.toNNReal s))
      (2 * π * (gBar h hh r / g h hh r) * (h r - mean h r) ^ 2) (r : ℝ) := by
  have hr' : (0 : ℝ) < r := hr
  have hg := Christodoulou.Bondi.hasDerivAt_g h hh r hr
  have hb := hasDerivAt_gBar h hh r hr
  have hgr : g h hh r ≠ 0 := (g_pos h hh r).ne'
  have hq := (hb.div hg (by simpa using hgr))
  have hm := ((hasDerivAt_id (r : ℝ)).div_const 2).mul ((hasDerivAt_const (r : ℝ) (1 : ℝ)).sub hq)
  have heq : (fun s : ℝ => mass h hh (Real.toNNReal s)) =ᶠ[𝓝 (r : ℝ)]
      fun s => id s / 2 * (1 - (fun s : ℝ => gBar h hh (Real.toNNReal s)) s /
        (fun s : ℝ => g h hh (Real.toNNReal s)) s) := by
    filter_upwards [lt_mem_nhds hr'] with s hs
    simp only [mass, id, Real.coe_toNNReal s hs.le]
  refine (hm.congr_of_eventuallyEq heq).congr_deriv ?_
  simp only [id, Pi.sub_apply, Pi.div_apply, Real.toNNReal_coe]
  field_simp
  ring

end Christodoulou.Bondi.Provider
