module
public import Christodoulou.Frozen.Bondi.Mass
import Christodoulou.Bondi.GBarBasic
import Christodoulou.Frozen.Bondi.GBarLeG



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

/-- `m ≥ 0` ([P] p. 344, "Therefore"): from the sealed `gBar_le_g` and `g > 0`. -/
theorem mass_nonneg {h : C(ℝ≥0, ℝ)} {hh : IsSlice h} {r : ℝ≥0} : 0 ≤ mass h hh r := by
  unfold mass
  have h1 : gBar h hh r / g h hh r ≤ 1 :=
    (div_le_one (g_pos h hh r)).2 (Christodoulou.Bondi.gBar_le_g h hh r)
  have h2 : (0 : ℝ) ≤ (r : ℝ) / 2 := by positivity
  exact mul_nonneg h2 (by linarith)

end Christodoulou.Bondi.Provider
