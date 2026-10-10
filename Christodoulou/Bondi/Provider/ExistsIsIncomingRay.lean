module
public import Christodoulou.Frozen.Bondi.IsIncomingRay
import Christodoulou.Bondi.ForwardCharacteristic



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem exists_isIncomingRay {u₀ : ℝ≥0}
    {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H}
    {r₀ : ℝ≥0} :
    ∃ u₁ : ℝ, ∃ χ : ℝ → ℝ, IsIncomingRay hH r₀ u₁ χ :=
  XFC.exists_isIncomingRay hH r₀

end Christodoulou.Bondi.Provider
