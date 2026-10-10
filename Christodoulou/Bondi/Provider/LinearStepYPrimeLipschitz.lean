module
public import Christodoulou.Frozen.Bondi.MemXPrimeBall
public import Christodoulou.Frozen.Bondi.YPrimeDistLe
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.ContractionFactor
import Christodoulou.Bondi.WeightedLipschitz



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem linearStep_yPrime_lipschitz {T : ℝ≥0}
    {x y : ℝ}
    {H K : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXPrimeBall T x H := by assumption)
    (hK : MemXPrimeBall T x K := by assumption)
    {data : C(ℝ≥0, ℝ)}
    (hdata : ContDiffOn ℝ 1 (fun z : ℝ => data z.toNNReal) (Ici 0) := by assumption)
    (hSK : MemXPrimeBall T x (linearStepMap hK.1 data) := by assumption)
    (hy : YPrimeDistLe T H K y := by assumption) :
    YPrimeDistLe T (linearStepMap hH.1 data) (linearStepMap hK.1 data)
      (contractionFactor x * y) :=
  XWL.linearStep_yPrime_lipschitz hH hK data hdata hSK hy

end Christodoulou.Bondi.Provider
