module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.MemXBall
public import Christodoulou.Frozen.Bondi.LinearStep
import Christodoulou.Bondi.ClassicalBridge



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem linearStep_eq_of_isClassicalSolution {u₀ : ℝ≥0}
    {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H}
    (hclass : IsClassicalSolution u₀ H := by assumption)
    {u : ℝ≥0}
    (hu : u ≤ u₀ := by assumption)
    {r : ℝ≥0} :
    linearStep hH (H.curry 0) u r = H (u, r) :=
  XCB.linearStep_eq_of_isClassicalSolution hH hclass u hu r

end Christodoulou.Bondi.Provider
