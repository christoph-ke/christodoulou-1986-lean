module
public import Christodoulou.Frozen.Bondi.IsCharacteristic
import Christodoulou.Frozen.Bondi.IsPicardLindelofCharField
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Provider for `Christodoulou.Bondi.exists_isCharacteristic`

Implementation module for the frozen anchor
`Christodoulou/Frozen/Bondi/ExistsIsCharacteristic.lean`.
The anchor is SEALED; downstream code must cite the frozen export, not this module.
Binders follow the provider convention of `Christodoulou/Frozen/README.md`.

Route: Mathlib's `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀` applied to the
sealed `isPicardLindelof_charField hH u₁ r₁ 0` gives a solution on `[0, u₀]` through `(u₁, r₁)`;
restrict the derivative set to `[0, u₁]`.
-/

public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem exists_isCharacteristic {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} :
    ∃ χ : ℝ → ℝ, IsCharacteristic hH u₁ r₁ χ := by
  obtain ⟨χ, hχ₁, hχ⟩ :=
    (isPicardLindelof_charField hH u₁ r₁ 0).exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨χ, hχ₁, fun t ht => (hχ t ⟨ht.1, ht.2.trans u₁.2.2⟩).mono ?_⟩
  intro s hs
  exact ⟨hs.1, hs.2.trans u₁.2.2⟩

end Christodoulou.Bondi.Provider
