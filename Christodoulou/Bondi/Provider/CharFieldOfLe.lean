module
public import Christodoulou.Frozen.Bondi.CharField

/-!
# Provider for `Christodoulou.Bondi.charField_of_le`

Implementation module for the frozen anchor `Christodoulou/Frozen/Bondi/CharFieldOfLe.lean`.
The anchor is SEALED; downstream code must cite the frozen export, not this module.
Binders follow the provider convention of `Christodoulou/Frozen/README.md`.

Route: unfold `charField` and `gBarX`; the time clamp and proof irrelevance (a `subst`-based
congruence).
-/

public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem charField_of_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)} {hH : MemXBall u₀ x H}
    {t : ℝ} (ht : t ≤ u₀ := by assumption) {hs : IsSlice (H.curry (Real.toNNReal t))} {z : ℝ} :
    charField hH t z = -(1 / 2) * gBar (H.curry (Real.toNNReal t)) hs (Real.toNNReal z) := by
  have hle : Real.toNNReal t ≤ u₀ := by
    rw [Real.toNNReal_le_iff_le_coe]; exact ht
  have key : ∀ {a b : ℝ≥0} (_ : a = b) (pa : IsSlice (H.curry a)) (pb : IsSlice (H.curry b)),
      gBar (H.curry a) pa (Real.toNNReal z) = gBar (H.curry b) pb (Real.toNNReal z) := by
    intro a b hab pa pb; subst hab; rfl
  simp only [charField, gBarX]
  rw [key (min_eq_left hle) _ hs]

end Christodoulou.Bondi.Provider
