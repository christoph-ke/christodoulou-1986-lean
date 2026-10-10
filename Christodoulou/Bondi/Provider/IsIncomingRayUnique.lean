module
public import Christodoulou.Frozen.Bondi.IsIncomingRay
import Christodoulou.Bondi.ForwardCharacteristic



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem IsIncomingRay.unique {u₀ : ℝ≥0}
    {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H}
    {r₀ : ℝ≥0}
    {u₁ u₂ : ℝ}
    {χ₁ χ₂ : ℝ → ℝ}
    (h₁ : IsIncomingRay hH r₀ u₁ χ₁ := by assumption)
    (h₂ : IsIncomingRay hH r₀ u₂ χ₂ := by assumption) :
    u₁ = u₂ ∧ EqOn χ₁ χ₂ (Icc 0 u₁) :=
  XFC.IsIncomingRay.unique h₁ h₂

end Christodoulou.Bondi.Provider
