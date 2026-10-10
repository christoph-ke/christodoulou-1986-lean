module
public import Christodoulou.Frozen.Bondi.XBallIterate
public import Christodoulou.Frozen.Bondi.IsDecaySlice
public import Mathlib.Topology.UniformSpace.Equicontinuity
import Christodoulou.Bondi.Lemma3Proof



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem lemma3 {u₀ : ℝ≥0}
    {d x₁ : ℝ}
    (hd : 0 ≤ d := by assumption)
    (hx : 2 * d < x₁ := by assumption)
    (hT : (u₀ : ℝ) < stepEta x₁ d := by assumption)
    {data : C(ℝ≥0, ℝ)}
    (hdata : IsDecaySlice data := by assumption)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 * |derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) r| ≤ d :=
      by assumption) :
    EquicontinuousOn
      (fun n (p : ℝ × ℝ) => derivWithin
        (fun s : ℝ => (xBallIterate hd hx hT data hdata hbound n).val
          (p.1.toNNReal, s.toNNReal)) (Ici 0) p.2)
      (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) :=
  XEq.lemma3 hd hx hT data hdata hbound

end Christodoulou.Bondi.Provider
