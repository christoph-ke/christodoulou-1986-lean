module
public import Christodoulou.Frozen.Bondi.GBar
import Christodoulou.Bondi.GBarBasic
import Mathlib.Analysis.Calculus.Deriv.Inv



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

/-- [P] p. 356: for `r > 0`, `ḡ″ = −2(g − ḡ)/r² + 4π g (h − h̄)²/r²`. Near `r`,
`ḡ′ = (g − ḡ)/s`; differentiate this quotient with `g′ = 4π g (h − h̄)²/r` and `ḡ′ = (g − ḡ)/r`. -/
theorem hasDerivAt_deriv_gBar {h : C(ℝ≥0, ℝ)} {hh : IsSlice h} {r : ℝ≥0}
    (hr : 0 < r := by assumption) :
    HasDerivAt (deriv fun s : ℝ => gBar h hh (Real.toNNReal s))
      (-2 * (g h hh r - gBar h hh r) / (r : ℝ) ^ 2
        + 4 * π * g h hh r * (h r - mean h r) ^ 2 / (r : ℝ) ^ 2) (r : ℝ) := by
  have hr' : (0 : ℝ) < r := hr
  have hg := Christodoulou.Bondi.hasDerivAt_g h hh r hr
  have hb := hasDerivAt_gBar h hh r hr
  have hq := (hg.sub hb).div (hasDerivAt_id (r : ℝ)) hr'.ne'
  have heq : (deriv fun s : ℝ => gBar h hh (Real.toNNReal s)) =ᶠ[𝓝 (r : ℝ)]
      ((fun s : ℝ => g h hh (Real.toNNReal s)) -
        fun s : ℝ => gBar h hh (Real.toNNReal s)) / id := by
    filter_upwards [lt_mem_nhds hr'] with s hs
    have hs' : 0 < Real.toNNReal s := Real.toNNReal_pos.2 hs
    have := (hasDerivAt_gBar h hh (Real.toNNReal s) hs').deriv
    rw [Real.coe_toNNReal s hs.le] at this
    rw [this]
    simp [Pi.div_apply, id]
  refine (hq.congr_of_eventuallyEq heq).congr_deriv ?_
  simp only [id, Pi.sub_apply, Real.toNNReal_coe]
  field_simp
  ring

end Christodoulou.Bondi.Provider
