module
public import Christodoulou.Frozen.Bondi.ContractionFactor
public import Christodoulou.Frozen.Bondi.SmallDataDelta
import Christodoulou.Bondi.SmallDataScalars
import Christodoulou.Frozen.Bondi.ContractionFactorStrictMonoOn
import Christodoulou.Frozen.Bondi.SmallDataDeltaCharacterization
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Roots and witnesses for the small-data argument

The positive contraction radius is unique by the frozen strict-monotonicity gate. The frozen
maximum characterization gives a positive threshold and witnesses inside every positive interval.
-/

public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi
namespace XSR

/-- The equation `s = 1` has exactly one positive nonnegative-real radius. -/
theorem existsUnique_contraction_radius :
    ∃! x₁ : ℝ≥0, 0 < x₁ ∧ contractionFactor x₁ = 1 := by
  have hc : Continuous contractionFactor := by unfold contractionFactor; fun_prop
  have hzero : contractionFactor 0 = 0 := by simp only [contractionFactor, zero_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_zero, zero_mul]
  let R : ℝ := √(3 / π)
  have hR : 0 < R := sqrt_pos.mpr (by positivity)
  have hRsq : R ^ 2 = 3 / π := sq_sqrt (by positivity)
  have hscale : π / 3 * R ^ 2 = 1 := by
    rw [hRsq]
    field_simp
  have hlarge : 1 < contractionFactor R := by
    unfold contractionFactor
    rw [hscale, one_mul]
    have hpoly : 1 < (37 / 6 : ℝ) + 2 * π * R ^ 2 := by
      have hnonneg : 0 ≤ 2 * π * R ^ 2 := by positivity
      linarith only [hnonneg]
    exact hpoly.trans_le (le_mul_of_one_le_right (by positivity) (one_le_exp (by positivity)))
  obtain ⟨r, hr, heq⟩ := intermediate_value_Icc hR.le hc.continuousOn
    (show (1 : ℝ) ∈ Icc (contractionFactor 0) (contractionFactor R) by
      rw [hzero]
      exact ⟨zero_le_one, hlarge.le⟩)
  have hrpos : 0 < r := by
    refine lt_of_le_of_ne hr.1 ?_
    intro h
    rw [← h, hzero] at heq
    norm_num at heq
  refine ⟨⟨r, hr.1⟩, ⟨NNReal.coe_pos.mp hrpos, heq⟩, ?_⟩
  intro y hy
  apply NNReal.coe_injective
  exact Christodoulou.Bondi.contractionFactor_strictMonoOn.injOn
    y.coe_nonneg hr.1 (hy.2.trans heq.symm)

/-- The threshold is positive and every smaller nonnegative datum has an interior witness. -/
theorem smallDataDelta_pos_and_witness (x₁ : ℝ≥0) (hx₁ : 0 < x₁) :
    0 < smallDataDelta x₁ ∧ ∀ d : ℝ, 0 ≤ d → d < smallDataDelta x₁ →
      ∃ x : ℝ, 0 < x ∧ x < x₁ ∧ d ≤ smallDataG x := by
  have hx₁' : (0 : ℝ) < x₁ := NNReal.coe_pos.mpr hx₁
  have hratio : ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < smallDataG x / x :=
    XSD.tendsto_smallDataG_div.eventually_const_lt (by norm_num)
  have hupper : ∀ᶠ x : ℝ in 𝓝[>] 0, x < x₁ :=
    (eventually_lt_nhds hx₁').filter_mono nhdsWithin_le_nhds
  obtain ⟨a, ha, haupper, haratio⟩ :=
    (eventually_mem_nhdsWithin.and (hupper.and hratio)).exists
  have hapos : 0 < a := ha
  have haG : 0 < smallDataG a := (div_pos_iff_of_pos_right hapos).mp haratio
  obtain ⟨z, hz, heq, hmax⟩ := Christodoulou.Bondi.smallDataDelta_characterization x₁
  have hdelta : 0 < smallDataDelta x₁ :=
    haG.trans_le (hmax a ⟨hapos.le, haupper.le⟩)
  refine ⟨hdelta, ?_⟩
  intro d hd hdδ
  have hzpos : 0 < z := by
    refine lt_of_le_of_ne hz.1 ?_
    intro h
    rw [← h] at heq
    simp only [smallDataG, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_div, zero_mul] at heq
    linarith only [hdelta, heq]
  have hdG : d < smallDataG z := heq ▸ hdδ
  have hnear : ∀ᶠ x in 𝓝 z, d < smallDataG x :=
    XSD.continuous_smallDataG.continuousAt.tendsto.eventually_const_lt hdG
  have hleft : ∀ᶠ x in 𝓝[<] z, 0 < x ∧ d < smallDataG x :=
    ((eventually_gt_nhds hzpos).and hnear).filter_mono nhdsWithin_le_nhds
  obtain ⟨x, ⟨hxpos, hxG⟩, hxlt⟩ := (hleft.and eventually_mem_nhdsWithin).exists
  exact ⟨x, hxpos, lt_of_lt_of_le hxlt hz.2, hxG.le⟩

end XSR
end Christodoulou.Bondi
