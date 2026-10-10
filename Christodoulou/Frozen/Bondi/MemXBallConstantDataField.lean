/-
# `Christodoulou.Bondi.memXBall_constantDataField`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.ConstantDataField
public import Christodoulou.Frozen.Bondi.MemXBall
public import Christodoulou.Frozen.Bondi.IsDecaySlice
import Christodoulou.Bondi.Provider.MemXBallConstantDataField



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


theorem memXBall_constantDataField (u₀ : ℝ≥0) (d : ℝ) (data : C(ℝ≥0, ℝ))
    (hdata : IsDecaySlice data)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 *
        |derivWithin (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) r| ≤ d) :
    MemXBall u₀ d (constantDataField data) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.memXBall_constantDataField



end Christodoulou.Bondi

