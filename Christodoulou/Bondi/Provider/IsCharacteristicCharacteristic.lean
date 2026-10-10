module
public import Christodoulou.Frozen.Bondi.IsCharacteristic
public import Christodoulou.Frozen.Bondi.Characteristic

/-!
# Provider for `Christodoulou.Bondi.isCharacteristic_characteristic`

Implementation module for the frozen anchor
`Christodoulou/Frozen/Bondi/IsCharacteristicCharacteristic.lean`.
The anchor is SEALED; downstream code must cite the frozen export, not this module.
Binders follow the provider convention of `Christodoulou/Frozen/README.md`.

Route: `Classical.choose_spec` of the existence part of the sealed `existsUnique_characteristicOn`;
`characteristic` unfolds to `curveExtension u₁ (Classical.choose …)`.
-/

public section

open Set
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem isCharacteristic_characteristic {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} :
    IsCharacteristic hH u₁ r₁ (characteristic hH u₁ r₁) :=
  Classical.choose_spec (existsUnique_characteristicOn hH u₁ r₁).exists

end Christodoulou.Bondi.Provider
