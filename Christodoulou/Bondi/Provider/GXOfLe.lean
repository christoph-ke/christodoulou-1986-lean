module
public import Christodoulou.Frozen.Bondi.GX

/-!
# Provider for `Christodoulou.Bondi.gX_of_le`

Implementation module for the frozen anchor `Christodoulou/Frozen/Bondi/GXOfLe.lean`.
The anchor is SEALED; downstream code must cite the frozen export, not this module.
Binders follow the provider convention of `Christodoulou/Frozen/README.md`.

Route: the time clamp `min u u₀ = u` and proof irrelevance (a `subst`-based congruence).
-/

public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem gX_of_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)} {hH : MemXBall u₀ x H} {u : ℝ≥0}
    (hu : u ≤ u₀ := by assumption) {hs : IsSlice (H.curry u)} {r : ℝ≥0} :
    gX hH u r = g (H.curry u) hs r := by
  have key : ∀ {a b : ℝ≥0} (_ : a = b) (pa : IsSlice (H.curry a)) (pb : IsSlice (H.curry b)),
      g (H.curry a) pa r = g (H.curry b) pb r := by
    intro a b hab pa pb; subst hab; rfl
  exact key (min_eq_left hu) _ _

end Christodoulou.Bondi.Provider
