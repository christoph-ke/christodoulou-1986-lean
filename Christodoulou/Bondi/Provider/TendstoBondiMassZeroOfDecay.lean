module
public import Christodoulou.Frozen.Bondi.BondiMass
public import Christodoulou.Frozen.Bondi.RadialDerivative
import Christodoulou.Bondi.BondiMassLimit



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem tendsto_bondiMass_zero_of_decay {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hs : ∀ u : ℝ≥0, IsSlice (H.curry u) := by assumption)
    {C : ℝ}
    (hd : ∀ u r : ℝ≥0, |radialDerivative H u r| ≤ C * (1 + (u : ℝ) + (r : ℝ)) ^ (-4 : ℤ) :=
      by assumption) :
    Tendsto (fun u : ℝ≥0 => bondiMass (H.curry u) (hs u)) atTop (𝓝 0) :=
  XBL.tendsto_bondiMass_zero_of_decay H hs hd

end Christodoulou.Bondi.Provider
