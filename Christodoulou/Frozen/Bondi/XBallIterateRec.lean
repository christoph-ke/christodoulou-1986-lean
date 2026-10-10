/-
# `Christodoulou.Bondi.xBallIterate_rec`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.XBallIterate
import Christodoulou.Bondi.Provider.XBallIterateRec



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


theorem xBallIterate_rec {u₀ : ℝ≥0} {d x : ℝ}
    (hd : 0 ≤ d) (hx : 2 * d < x) (hT : (u₀ : ℝ) < stepEta x d)
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 *
        |derivWithin (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) r| ≤ d) :
    (xBallIterate hd hx hT data hdata hbound 0).val = constantDataField data ∧
    (∀ n, (xBallIterate hd hx hT data hdata hbound (n + 1)).val =
      linearStepMap (xBallIterate hd hx hT data hdata hbound n).property data) ∧
    (∀ n r, (xBallIterate hd hx hT data hdata hbound n).val (0, r) = data r) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.xBallIterate_rec



end Christodoulou.Bondi

