module
public import Christodoulou.Frozen.Bondi.G
import Christodoulou.Bondi.GBasic



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

/-- Continuity of `g` on `[0, ∞)`: by the tail identity, `g` is `exp` of an affine function of the
continuous primitive `r ↦ ∫₀ʳ F`. -/
theorem continuous_g {h : C(ℝ≥0, ℝ)} (hh : IsSlice h := by assumption) : Continuous (g h hh) := by
  have hp : Continuous fun x : ℝ => ∫ s in (0 : ℝ)..x, tailIntegrand h s :=
    intervalIntegral.continuous_primitive
      (fun _ _ => (integrable_tailIntegrand h hh).intervalIntegrable) 0
  rw [show g h hh = fun r : ℝ≥0 => Real.exp (-(4 * π) * ((∫ s in Ioi (0 : ℝ), tailIntegrand h s) -
      ∫ s in (0 : ℝ)..(r : ℝ), tailIntegrand h s)) from funext (g_eq h hh)]
  fun_prop

end Christodoulou.Bondi.Provider
