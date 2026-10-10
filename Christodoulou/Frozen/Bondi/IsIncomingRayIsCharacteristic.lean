/-
# `Christodoulou.Bondi.IsIncomingRay.isCharacteristic`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.IsIncomingRay
public import Christodoulou.Frozen.Bondi.IsCharacteristic
import Christodoulou.Bondi.Provider.IsIncomingRayIsCharacteristic



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- The incoming ray is the (backward) characteristic through each of its points (t, χ(t)). -/
theorem IsIncomingRay.isCharacteristic {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {r₀ : ℝ≥0} {u₁ : ℝ} {χ : ℝ → ℝ} (hχ : IsIncomingRay hH r₀ u₁ χ)
    (t : Icc (0 : ℝ) u₀) (ht : (t : ℝ) ≤ u₁) :
    IsCharacteristic hH t (Real.toNNReal (χ t)) χ :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.IsIncomingRay.isCharacteristic



end Christodoulou.Bondi

