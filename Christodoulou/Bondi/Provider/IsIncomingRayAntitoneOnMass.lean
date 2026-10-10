module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.IsClassicalSolutionIsSlice
public import Christodoulou.Frozen.Bondi.MemXBall
public import Christodoulou.Frozen.Bondi.IsIncomingRay
public import Christodoulou.Frozen.Bondi.Mass
import Christodoulou.Bondi.ForwardCharacteristic



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem IsIncomingRay.antitoneOn_mass {u₀ : ℝ≥0}
    {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H := by assumption)
    (hX : MemXBall u₀ x H := by assumption)
    {r₀ : ℝ≥0}
    {u₁ : ℝ}
    {χ : ℝ → ℝ}
    (hχ : IsIncomingRay hX r₀ u₁ χ := by assumption) :
    AntitoneOn (fun s : ℝ => mass (H.curry (min (Real.toNNReal s) u₀))
        (hH.isSlice _ (min_le_right _ _)) (Real.toNNReal (χ s))) (Icc 0 u₁) :=
  XFC.IsIncomingRay.antitoneOn_mass hH hX hχ

end Christodoulou.Bondi.Provider
