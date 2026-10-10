module
public import Christodoulou.Bondi.DerivEquicontinuity
public import Christodoulou.Frozen.Bondi.XBallIterate
import Christodoulou.Frozen.Bondi.XBallIterateRec

/-!
# Lemma 3: equicontinuity of the radial derivatives of the iterates

The sealed iterate recursion and its ball membership discharge the hypotheses of the
uniform equicontinuity theorem. Restricting its conclusion gives the source-facing lemma.
-/

public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi
namespace XEq

/-- Lemma 3: the canonical iterates have jointly equicontinuous radial derivatives. -/
theorem lemma3 {u₀ : ℝ≥0} {d x₁ : ℝ}
    (hd : 0 ≤ d) (hx : 2 * d < x₁) (hT : (u₀ : ℝ) < stepEta x₁ d)
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
    (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ)) ^ 4 * |derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) r| ≤ d) :
    EquicontinuousOn
      (fun n (p : ℝ × ℝ) => derivWithin
        (fun s : ℝ => (xBallIterate hd hx hT data hdata hbound n).val
          (p.1.toNNReal, s.toNNReal)) (Ici 0) p.2)
      (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) := by
  have hrec := xBallIterate_rec hd hx hT data hdata hbound
  exact (iterate_deriv_uniformEquicontinuousOn data
    (fun n => (xBallIterate hd hx hT data hdata hbound n).val)
    (fun n => (xBallIterate hd hx hT data hdata hbound n).property)
    hrec.1 hrec.2.1).equicontinuousOn

end XEq
end Christodoulou.Bondi
