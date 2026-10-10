module
public import Christodoulou.Frozen.Bondi.RadialScale
public import Christodoulou.Frozen.Bondi.ScaledInitialSize
public import Christodoulou.Frozen.Bondi.InitialSize
public import Christodoulou.Frozen.Bondi.IsDecaySlice
public import Christodoulou.Bondi.ScalingBasic
import Christodoulou.Frozen.Bondi.IsDecaySliceRadialScale
import Christodoulou.Frozen.Bondi.InitialSizeCharacterization

/-!
# The carrier of the scaled initial size

The literal range in `scaledInitialSize` agrees, by a change of radius, with the (7.4) range
of the scaled data. For positive scales and decaying data this range is nonempty and bounded
above, so the literal supremum is its least upper bound.
-/

public section

open Set Real
open scoped NNReal

namespace Christodoulou.Bondi.XSZ

/-- The literal range used in `scaledInitialSize`. -/
@[expose] noncomputable def scaledSizeRange (a : ℝ≥0) (data : C(ℝ≥0, ℝ)) : Set ℝ :=
  Set.range (fun r : ℝ≥0 => (1 + (r : ℝ) / (a : ℝ)) ^ 3 * |data r| +
    (1 + (r : ℝ) / (a : ℝ)) ^ 4 *
      |(a : ℝ) * derivWithin (fun z : ℝ => data z.toNNReal) (Ici 0) r|)

/-- The frozen scaled initial size is the supremum of its literal range. -/
theorem scaledInitialSize_eq_sSup (a : ℝ≥0) (ha : 0 < a)
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data) :
    scaledInitialSize a ha data hdata = sSup (scaledSizeRange a data) := rfl

/-- Change of radius identifies the scale-a range with the ordinary scaled-data range. -/
theorem scaledSizeRange_radialScale {a : ℝ≥0} (ha : 0 < a)
    (data : C(ℝ≥0, ℝ)) :
    scaledSizeRange a data = Set.range (fun r : ℝ≥0 =>
      (1 + (r : ℝ)) ^ 3 * |radialScale a data r| +
      (1 + (r : ℝ)) ^ 4 *
        |derivWithin (fun z : ℝ => radialScale a data z.toNNReal) (Ici 0) r|) := by
  ext v
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r / a, (XSB.weighted_summand_rescale_radius_within a ha data r).symm⟩
  · rintro ⟨r, rfl⟩
    exact ⟨a * r, (XSB.weighted_summand_scale_within a ha data r).symm⟩

/-- No empty or unbounded supremum occurs for positive scales on the decay carrier. -/
theorem scaledInitialSize_isLUB {a : ℝ≥0} (ha : 0 < a)
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data) :
    (scaledSizeRange a data).Nonempty ∧ BddAbove (scaledSizeRange a data) ∧
      IsLUB (scaledSizeRange a data) (scaledInitialSize a ha data hdata) := by
  have hne : (scaledSizeRange a data).Nonempty := Set.range_nonempty _
  have hs := isDecaySlice_radialScale ha hdata
  have hbound := ((initialSize_characterization (radialScale a data) hs).2
    (initialSize (radialScale a data) hs)).2 le_rfl
  have hba : BddAbove (scaledSizeRange a data) := by
    rw [scaledSizeRange_radialScale ha data]
    refine ⟨initialSize (radialScale a data) hs, ?_⟩
    rintro _ ⟨r, rfl⟩
    exact hbound r
  exact ⟨hne, hba, isLUB_csSup hne hba⟩

end Christodoulou.Bondi.XSZ
