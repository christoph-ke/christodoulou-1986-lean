/-
# `Christodoulou.Bondi.xBallIterate_time_bound`

Source: Christodoulou, CMP 105 (1986), 337–361, DOI: https://doi.org/10.1007/BF01205930.
See `depgraph/anchors.json` for the source correspondence.
-/

module
public import Christodoulou.Frozen.Bondi.XBallIterate
public import Christodoulou.Frozen.Bondi.IsDecaySlice
import Christodoulou.Bondi.Provider.XBallIterateTimeBound



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi

/-- (7.60), [P] p. 349: the iterates have equibounded time derivatives (every `n`, including the
time-independent `h₀`). -/
theorem xBallIterate_time_bound {u₀ : ℝ≥0} {d x : ℝ}
    (hd : 0 ≤ d) (hx : 2 * d < x) (hT : (u₀ : ℝ) < stepEta x d)
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 * |derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) r| ≤ d)
    (n : ℕ) (u r : ℝ≥0) (hu : u ≤ u₀) :
    |derivWithin (fun t : ℝ => (xBallIterate hd hx hT data hdata hbound n).val (t.toNNReal, r))
      (Icc 0 (u₀ : ℝ)) u| ≤
      1 / 2 * x * (1 + π / 3 * x ^ 2) / (1 + (r : ℝ)) ^ 3 :=
-- Proof.
  by exact Christodoulou.Bondi.Provider.xBallIterate_time_bound



end Christodoulou.Bondi

