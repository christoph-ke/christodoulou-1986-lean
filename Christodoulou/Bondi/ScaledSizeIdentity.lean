module
public import Christodoulou.Frozen.Bondi.RadialScale
public import Christodoulou.Frozen.Bondi.InitialSize
public import Christodoulou.Frozen.Bondi.ScaledInitialSize
import Christodoulou.Bondi.ScalingBasic

/-!
# Initial size under radial scaling

The p. 360 identity identifies the initial size of the radially scaled data with the
scale-dependent initial size. The proof reindexes the weighted supremum by `r ↦ a * r`,
using the one-sided derivative identities from `ScalingBasic`.
-/

public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

namespace XSI

private theorem weighted_sup_scale_within (a : ℝ≥0) (ha : 0 < a)
    (data : C(ℝ≥0, ℝ)) :
    sSup (Set.range (fun r : ℝ≥0 =>
      (1 + (r : ℝ) / (a : ℝ)) ^ 3 * |data r| +
      (1 + (r : ℝ) / (a : ℝ)) ^ 4 *
        |(a : ℝ) * derivWithin (fun s : ℝ => data (Real.toNNReal s)) (Ici 0) r|)) =
    sSup (Set.range (fun r : ℝ≥0 =>
      (1 + (r : ℝ)) ^ 3 * |radialScale a data r| +
      (1 + (r : ℝ)) ^ 4 *
        |derivWithin (fun s : ℝ => radialScale a data (Real.toNNReal s)) (Ici 0) r|)) := by
  congr 1
  ext v
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r / a, (XSB.weighted_summand_rescale_radius_within a ha data r).symm⟩
  · rintro ⟨r, rfl⟩
    exact ⟨a * r, (XSB.weighted_summand_scale_within a ha data r).symm⟩

/-- The p. 360 identity: the initial size of `data (a * r)` is the scale-`a` initial size. -/
theorem initialSize_radialScale {a : ℝ≥0} (ha : 0 < a) {data : C(ℝ≥0, ℝ)}
    (hdata : IsDecaySlice data) (hs : IsDecaySlice (radialScale a data)) :
    initialSize (radialScale a data) hs = scaledInitialSize a ha data hdata := by
  exact (weighted_sup_scale_within a ha data).symm

end XSI

end Christodoulou.Bondi
