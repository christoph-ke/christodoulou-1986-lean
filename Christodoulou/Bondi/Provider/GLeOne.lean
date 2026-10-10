module
public import Christodoulou.Frozen.Bondi.G
import Christodoulou.Bondi.GBasic



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

/-- `g ≤ 1`, [P] p. 346: the exponent `−4π ∫_(r,∞) F` is nonpositive since `F ≥ 0`. -/
theorem g_le_one {h : C(ℝ≥0, ℝ)} {hh : IsSlice h} {r : ℝ≥0} : g h hh r ≤ 1 := by
  rw [g, Real.exp_le_one_iff]
  have := setIntegral_Ioi_nonneg h r
  have hπ : 0 < 4 * π := by positivity
  change -(4 * π) * (∫ s in Ioi (r : ℝ), tailIntegrand h s) ≤ 0
  nlinarith

end Christodoulou.Bondi.Provider
