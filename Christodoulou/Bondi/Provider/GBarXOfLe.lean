module
public import Christodoulou.Frozen.Bondi.GBarX

/-!
# Provider for `Christodoulou.Bondi.gBarX_of_le`

Implementation module for the frozen anchor `Christodoulou/Frozen/Bondi/GBarXOfLe.lean`.
The anchor is SEALED; downstream code must cite the frozen export, not this module.
Binders follow the provider convention of `Christodoulou/Frozen/README.md`.

Route: the time clamp `min u u₀ = u` and proof irrelevance (a `subst`-based congruence).
-/

public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

/-- `gBar` of two time-slices agrees when the times agree (any slice proofs). -/
theorem gBar_curry_congr {H : C(ℝ≥0 × ℝ≥0, ℝ)} {a b : ℝ≥0} (hab : a = b)
    (pa : IsSlice (H.curry a)) (pb : IsSlice (H.curry b)) (r : ℝ≥0) :
    gBar (H.curry a) pa r = gBar (H.curry b) pb r := by
  subst hab; rfl

theorem gBarX_of_le {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)} {hH : MemXBall u₀ x H} {u : ℝ≥0}
    (hu : u ≤ u₀ := by assumption) {hs : IsSlice (H.curry u)} {r : ℝ≥0} :
    gBarX hH u r = gBar (H.curry u) hs r :=
  gBar_curry_congr (min_eq_left hu) _ _ r

end Christodoulou.Bondi.Provider
