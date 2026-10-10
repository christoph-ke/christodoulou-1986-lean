/-
# `Christodoulou.Bondi.xBallIterate`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/
module
public import Christodoulou.Frozen.Bondi.InitialMemXBall
public import Christodoulou.Frozen.Bondi.LinearStepMapMemXBall



public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial


@[expose] noncomputable def xBallIterate {u₀ : ℝ≥0} {d x : ℝ}
    (hd : 0 ≤ d) (hx : 2 * d < x) (hT : (u₀ : ℝ) < stepEta x d)
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 *
        |derivWithin (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) r| ≤ d) :
    ℕ → {H : C(ℝ≥0 × ℝ≥0, ℝ) // MemXBall u₀ x H} :=
  Nat.rec ⟨constantDataField data, initial_memXBall hd hx data hdata hbound⟩
    (fun _ b => ⟨linearStepMap b.property data,
      linearStepMap_memXBall hd hx hT data hdata hbound b.property⟩)

end Christodoulou.Bondi
