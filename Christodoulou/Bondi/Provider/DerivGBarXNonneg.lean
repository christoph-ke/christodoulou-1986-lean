module
public import Christodoulou.Frozen.Bondi.DerivGBarX
import Christodoulou.Bondi.XBallDeriv

/-!
# Provider for `Christodoulou.Bondi.derivGBarX_nonneg`

Implementation module for the frozen anchor `Christodoulou/Frozen/Bondi/DerivGBarXNonneg.lean`.
The anchor is SEALED; downstream code must cite the frozen export, not this module.
Binders follow the provider convention of `Christodoulou/Frozen/README.md`.

Route: the helper `Christodoulou.Bondi.XBall.derivGBarX_nonneg` (`Bondi/XBallDeriv.lean`):
`ḡ ≤ g` (sealed `gBar_le_g`).
-/

public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem derivGBarX_nonneg {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)} {hH : MemXBall u₀ x H}
    {u r : ℝ≥0} : 0 ≤ derivGBarX hH u r :=
  XBall.derivGBarX_nonneg hH u r

end Christodoulou.Bondi.Provider
