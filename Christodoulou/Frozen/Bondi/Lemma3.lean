/-
# `Christodoulou.Bondi.lemma3`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.XBallIterate
public import Christodoulou.Frozen.Bondi.IsDecaySlice
public import Mathlib.Topology.UniformSpace.Equicontinuity
import Christodoulou.Bondi.Provider.Lemma3



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi

/-- **Lemma 3**, [P] p. 349: under the hypotheses of Lemma 1, the sequence `{∂h_n/∂r}` is
equicontinuous on `[0, u₀] × [0, ∞)`. -/
theorem lemma3 {u₀ : ℝ≥0} {d x₁ : ℝ}
    (hd : 0 ≤ d) (hx : 2 * d < x₁) (hT : (u₀ : ℝ) < stepEta x₁ d)
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 * |derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) r| ≤ d) :
    EquicontinuousOn
      (fun n (p : ℝ × ℝ) => derivWithin
        (fun s : ℝ => (xBallIterate hd hx hT data hdata hbound n).val
          (p.1.toNNReal, s.toNNReal)) (Ici 0) p.2)
      (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.lemma3



end Christodoulou.Bondi

