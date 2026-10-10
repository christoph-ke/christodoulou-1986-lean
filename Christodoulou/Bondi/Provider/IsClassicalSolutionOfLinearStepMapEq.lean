module
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
import Christodoulou.Bondi.ClassicalOfFixedPoint



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem isClassicalSolution_of_linearStepMap_eq {u₀ : ℝ≥0}
    {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H}
    {data : C(ℝ≥0, ℝ)}
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data s.toNNReal) (Ici 0) := by assumption)
    (hfix : linearStepMap hH data = H := by assumption) :
    IsClassicalSolution u₀ H :=
  XFix.isClassicalSolution_of_linearStepMap_eq hH data hdata hfix

end Christodoulou.Bondi.Provider
