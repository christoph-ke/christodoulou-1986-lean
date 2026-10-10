module
public import Christodoulou.Frozen.Bondi.IsIncomingRay
public import Christodoulou.Frozen.Bondi.IsCharacteristic
import Christodoulou.Bondi.ForwardCharacteristic



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem IsIncomingRay.isCharacteristic {u₀ : ℝ≥0}
    {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H}
    {r₀ : ℝ≥0}
    {u₁ : ℝ}
    {χ : ℝ → ℝ}
    (hχ : IsIncomingRay hH r₀ u₁ χ := by assumption)
    {t : Icc (0 : ℝ) u₀}
    (ht : (t : ℝ) ≤ u₁ := by assumption) :
    IsCharacteristic hH t (Real.toNNReal (χ t)) χ :=
  XFC.IsIncomingRay.isCharacteristic hχ t ht

end Christodoulou.Bondi.Provider
