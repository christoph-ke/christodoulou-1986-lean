module
public import Christodoulou.Frozen.Bondi.IsCharacteristic
public import Christodoulou.Frozen.Bondi.Characteristic
import Christodoulou.Frozen.Bondi.IsCharacteristicEqOn
import Christodoulou.Frozen.Bondi.IsCharacteristicCharacteristic

/-!
# Provider for `Christodoulou.Bondi.IsCharacteristic.eqOn_characteristic`

Implementation module for the frozen anchor
`Christodoulou/Frozen/Bondi/IsCharacteristicEqOnCharacteristic.lean`.
The anchor is SEALED; downstream code must cite the frozen export, not this module.
Binders follow the provider convention of `Christodoulou/Frozen/README.md`.

Route: the sealed `IsCharacteristic.eqOn` applied to `hχ` and the sealed
`isCharacteristic_characteristic`.
-/

public section

open Set
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem IsCharacteristic.eqOn_characteristic {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH u₁ r₁ χ := by assumption) :
    EqOn χ (characteristic hH u₁ r₁) (Icc 0 (u₁ : ℝ)) :=
  Christodoulou.Bondi.IsCharacteristic.eqOn hχ (isCharacteristic_characteristic hH u₁ r₁)

end Christodoulou.Bondi.Provider
