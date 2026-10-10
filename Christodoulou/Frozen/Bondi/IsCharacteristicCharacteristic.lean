/-
# `Christodoulou.Bondi.isCharacteristic_characteristic`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.IsCharacteristic
public import Christodoulou.Frozen.Bondi.Characteristic
import Christodoulou.Bondi.Provider.IsCharacteristicCharacteristic



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

/-- `characteristic` is a characteristic through `(u₁, r₁)`. -/
theorem isCharacteristic_characteristic {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u₁ : Icc (0 : ℝ) u₀) (r₁ : ℝ≥0) :
    IsCharacteristic hH u₁ r₁ (characteristic hH u₁ r₁) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.isCharacteristic_characteristic



end Christodoulou.Bondi

