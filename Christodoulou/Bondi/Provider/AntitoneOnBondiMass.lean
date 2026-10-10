module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.RadialDerivative
public import Christodoulou.Frozen.Bondi.BondiMass
import Christodoulou.Bondi.BondiTheorem



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem antitoneOn_bondiMass {u₀ : ℝ≥0}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H := by assumption)
    (hs : ∀ v : ℝ≥0, IsSlice (H.curry v) := by assumption)
    {C : ℝ}
    (hd : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      |radialDerivative H u r| ≤ C * (1 + (r : ℝ)) ^ (-4 : ℤ) := by assumption) :
    AntitoneOn (fun u : ℝ≥0 => bondiMass (H.curry u) (hs u)) (Icc 0 u₀) :=
  XBT.antitoneOn_bondiMass hH hs hd

end Christodoulou.Bondi.Provider
