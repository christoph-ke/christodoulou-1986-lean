module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.IsClassicalSolutionIsSlice
public import Christodoulou.Frozen.Bondi.Mass
public import Christodoulou.Frozen.Bondi.ReflectedRay
import Christodoulou.Bondi.ForwardCharacteristic



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem monotoneOn_mass_reflectedRay_outgoing {u₀ : ℝ≥0}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H := by assumption)
    {u₁ : ℝ}
    {χ : ℝ → ℝ} :
    MonotoneOn (fun p : ℝ × ℝ => mass (H.curry (min (Real.toNNReal p.1) u₀))
        (hH.isSlice _ (min_le_right _ _)) (Real.toNNReal p.2))
      {p | p ∈ reflectedRay u₁ χ ∧ p.1 = u₁} :=
  XFC.monotoneOn_mass_reflectedRay_outgoing hH u₁ χ

end Christodoulou.Bondi.Provider
