module
public import Christodoulou.Frozen.Bondi.SmallDataG
public import Christodoulou.Frozen.Bondi.ContractionFactor
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.MemXPrimeBall
public import Christodoulou.Frozen.Bondi.IsDecaySlice
public import Christodoulou.Frozen.Bondi.InitialBound
public import Christodoulou.Frozen.Bondi.RadialDerivative
import Christodoulou.Bondi.GlobalGluing



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem global_exists_of_G {x d : ℝ}
    (hx : 0 < x := by assumption)
    (hd : 0 ≤ d := by assumption)
    (hsmall : d ≤ smallDataG x := by assumption)
    (hq : contractionFactor x < 1 := by assumption)
    {data : C(ℝ≥0, ℝ)}
    (hdata : IsDecaySlice data := by assumption)
    (hbound : InitialBound data d := by assumption) :
    ∃ H : C(ℝ≥0 × ℝ≥0, ℝ),
      (∀ T : ℝ≥0, IsClassicalSolution T H ∧ MemXPrimeBall T x H) ∧
      (∀ r, H (0, r) = data r) ∧
      ∀ u r : ℝ≥0,
        |H (u, r)| ≤ 8 * x * (1 + (u : ℝ) + (r : ℝ)) ^ (-3 : ℤ) ∧
        |radialDerivative H u r| ≤ 16 * x * (1 + (u : ℝ) + (r : ℝ)) ^ (-4 : ℤ) :=
  XGG.global_exists_of_G hx hd hsmall hq data hdata hbound

end Christodoulou.Bondi.Provider
