module
public import Christodoulou.Frozen.Bondi.ScaledInitialSize
public import Christodoulou.Frozen.Bondi.ScaleInvariantSize
public import Christodoulou.Frozen.Bondi.InitialSize



public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

namespace XSV

/-- The literal scaled supremum is nonnegative at every positive scale. -/
theorem scaledInitialSize_nonneg {a : ℝ≥0} (ha : 0 < a)
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data) :
    0 ≤ scaledInitialSize a ha data hdata := by
  apply Real.sSup_nonneg
  rintro _ ⟨r, rfl⟩
  positivity

/-- The scale-one size is exactly the ordinary initial size. -/
theorem scaledInitialSize_one (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data) :
    scaledInitialSize 1 zero_lt_one data hdata = initialSize data hdata := by
  simp only [scaledInitialSize, initialSize, NNReal.coe_one, div_one, one_mul]

/-- Positive scales and their size range are nonempty, with zero as a lower bound. -/
theorem scaleInvariantSize_carrier (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data) :
    Nonempty {a : ℝ≥0 // 0 < a} ∧
      (Set.range (fun a : {a : ℝ≥0 // 0 < a} =>
        scaledInitialSize a a.2 data hdata)).Nonempty ∧
      0 ∈ lowerBounds (Set.range (fun a : {a : ℝ≥0 // 0 < a} =>
        scaledInitialSize a a.2 data hdata)) := by
  refine ⟨⟨⟨1, zero_lt_one⟩⟩, ⟨_, ⟨⟨1, zero_lt_one⟩, rfl⟩⟩, ?_⟩
  rintro _ ⟨a, rfl⟩
  exact scaledInitialSize_nonneg a.2 data hdata

/-- The scale-invariant size is nonnegative and at most the ordinary initial size. -/
theorem scaleInvariantSize_le_initialSize (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data) :
    0 ≤ scaleInvariantSize data hdata ∧
      scaleInvariantSize data hdata ≤ initialSize data hdata := by
  obtain ⟨hne, _, hbelow⟩ := scaleInvariantSize_carrier data hdata
  let : Nonempty {a : ℝ≥0 // 0 < a} := hne
  constructor
  · exact le_ciInf (fun a => scaledInitialSize_nonneg a.2 data hdata)
  · rw [← scaledInitialSize_one data hdata]
    exact ciInf_le (show BddBelow (Set.range (fun a : {a : ℝ≥0 // 0 < a} =>
      scaledInitialSize a a.2 data hdata)) from ⟨0, hbelow⟩) ⟨1, zero_lt_one⟩

/-- A strict upper bound on the scale-invariant size supplies a positive scale below it. -/
theorem exists_scaledInitialSize_lt {data : C(ℝ≥0, ℝ)} (hdata : IsDecaySlice data)
    {δ : ℝ} (h : scaleInvariantSize data hdata < δ) :
    ∃ (a : ℝ≥0) (ha : 0 < a), scaledInitialSize a ha data hdata < δ := by
  let : Nonempty {a : ℝ≥0 // 0 < a} := ⟨⟨1, zero_lt_one⟩⟩
  obtain ⟨a, ha⟩ := exists_lt_of_ciInf_lt h
  exact ⟨a, a.2, ha⟩

end XSV

end Christodoulou.Bondi
