module
public import Christodoulou.Frozen.Bondi.RadialScale
public import Christodoulou.Frozen.Bondi.ScaledInitialSize
public import Christodoulou.Frozen.Bondi.ScaleInvariantSize
public import Christodoulou.Bondi.ScalingBasic



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.XSN

/-- Composition of scale-weighted summands under multiplication of the radius. -/
theorem weighted_summand_comp_within {a b : ℝ≥0} (ha : 0 < a) (hb : 0 < b)
    (data : C(ℝ≥0, ℝ)) (r : ℝ≥0) :
    (1 + (r : ℝ) / (a : ℝ)) ^ 3 * |radialScale b data r| +
      (1 + (r : ℝ) / (a : ℝ)) ^ 4 *
        |(a : ℝ) * derivWithin (fun z : ℝ => radialScale b data z.toNNReal) (Ici 0) r| =
    (1 + ((b * r : ℝ≥0) : ℝ) / ((a * b : ℝ≥0) : ℝ)) ^ 3 * |data (b * r)| +
      (1 + ((b * r : ℝ≥0) : ℝ) / ((a * b : ℝ≥0) : ℝ)) ^ 4 *
        |((a * b : ℝ≥0) : ℝ) *
          derivWithin (fun z : ℝ => data z.toNNReal) (Ici 0) (b * r)| := by
  rw [XSB.derivWithin_radialScale b hb]
  simp only [XSB.radialScale_apply, NNReal.coe_mul]
  have hw : (b : ℝ) * (r : ℝ) / ((a : ℝ) * (b : ℝ)) = (r : ℝ) / (a : ℝ) := by
    field_simp
  rw [hw]
  simp only [mul_assoc]

/-- Radial scaling composes the scale parameters in the literal weighted supremum. -/
theorem scaledInitialSize_radialScale {a b : ℝ≥0} (ha : 0 < a) (hb : 0 < b)
    {data : C(ℝ≥0, ℝ)} (hdata : IsDecaySlice data)
    (hs : IsDecaySlice (radialScale b data)) :
    scaledInitialSize a ha (radialScale b data) hs =
      scaledInitialSize (a * b) (mul_pos ha hb) data hdata := by
  unfold scaledInitialSize
  congr 1
  ext v
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨b * r, (weighted_summand_comp_within ha hb data r).symm⟩
  · rintro ⟨r, rfl⟩
    refine ⟨r / b, ?_⟩
    simpa only [mul_div_cancel₀ r (ne_of_gt hb), NNReal.coe_div,
      mul_div_cancel₀ (r : ℝ) (show (b : ℝ) ≠ 0 from ne_of_gt hb)] using
      weighted_summand_comp_within ha hb data (r / b)


theorem scaleInvariantSize_radialScale {b : ℝ≥0} (hb : 0 < b) {data : C(ℝ≥0, ℝ)}
    (hdata : IsDecaySlice data) (hs : IsDecaySlice (radialScale b data)) :
    scaleInvariantSize (radialScale b data) hs = scaleInvariantSize data hdata := by
  unfold scaleInvariantSize
  let φ : {a : ℝ≥0 // 0 < a} → {a : ℝ≥0 // 0 < a} :=
    fun a => ⟨a * b, mul_pos a.2 hb⟩
  have hφ : Function.Surjective φ := by
    intro a
    refine ⟨⟨a / b, div_pos a.2 hb⟩, ?_⟩
    apply Subtype.ext
    exact div_mul_cancel₀ a.val (ne_of_gt hb)
  exact Function.Surjective.iInf_congr φ hφ
    (fun a => (scaledInitialSize_radialScale a.2 hb hdata hs).symm)

end Christodoulou.Bondi.XSN
