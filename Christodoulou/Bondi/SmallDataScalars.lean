module
public import Christodoulou.Frozen.Bondi.SmallDataG
public import Christodoulou.Frozen.Bondi.ContractionFactor
public import Christodoulou.Frozen.Bondi.SmallDataDelta
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Scalar anchors for the small-data argument

The contraction factor is strictly increasing on the nonnegative real axis. The supremum
defining the small-data threshold is an attained maximum. Shared continuity and limit helpers
use only the frozen scalar definitions.
-/

public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi
namespace XSD

/-- The small-data scalar function is continuous. -/
theorem continuous_smallDataG : Continuous smallDataG := by
  unfold smallDataG
  have hA : ∀ x : ℝ, 2 + π / 6 * x ^ 2 ≠ 0 := fun x => ne_of_gt (by positivity)
  fun_prop

/-- The contraction factor is strictly increasing on the nonnegative real axis. -/
theorem contractionFactor_strictMonoOn :
    StrictMonoOn contractionFactor (Ici 0) := by
  intro a ha b hb hab
  change 0 ≤ a at ha
  change 0 ≤ b at hb
  have hab2 : a ^ 2 < b ^ 2 := by nlinarith only [ha, hb, hab]
  have h1 : π / 3 * a ^ 2 < π / 3 * b ^ 2 :=
    mul_lt_mul_of_pos_left hab2 (by positivity)
  have h2 : (37 / 6 : ℝ) + 2 * π * a ^ 2 ≤ 37 / 6 + 2 * π * b ^ 2 := by
    gcongr
  have h3 : exp (5 * π / 9 * a ^ 2) ≤ exp (5 * π / 9 * b ^ 2) := by
    gcongr
  unfold contractionFactor
  exact mul_lt_mul_of_pos_right
    (mul_lt_mul h1 h2 (by positivity) (by positivity)) (exp_pos _)
    |>.trans_le (mul_le_mul_of_nonneg_left h3 (by positivity))

/-- The small-data threshold is an attained maximum of `G` on its defining interval. -/
theorem smallDataDelta_characterization (x₁ : ℝ≥0) :
    ∃ z ∈ Icc 0 (x₁ : ℝ), smallDataDelta x₁ = smallDataG z ∧
      ∀ x ∈ Icc 0 (x₁ : ℝ), smallDataG x ≤ smallDataDelta x₁ := by
  have hne : (Icc 0 (x₁ : ℝ)).Nonempty := ⟨0, le_rfl, x₁.coe_nonneg⟩
  obtain ⟨z, hz, hm⟩ := isCompact_Icc.exists_isMaxOn hne continuous_smallDataG.continuousOn
  have heq : smallDataDelta x₁ = smallDataG z := by
    unfold smallDataDelta
    apply le_antisymm
    · exact csSup_le (hne.image smallDataG) (by rintro _ ⟨a, ha, rfl⟩; exact hm ha)
    · exact le_csSup (isCompact_Icc.bddAbove_image continuous_smallDataG.continuousOn)
        ⟨z, hz, rfl⟩
  exact ⟨z, hz, heq, fun x hx => heq.symm ▸ hm hx⟩

/-- The ratio of the small-data scalar function to its argument tends to one half at zero. -/
theorem tendsto_smallDataG_div :
    Tendsto (fun x : ℝ => smallDataG x / x) (𝓝[>] 0) (𝓝 (1 / 2 : ℝ)) := by
  have hA : ∀ x : ℝ, 2 + π / 6 * x ^ 2 ≠ 0 := fun x => ne_of_gt (by positivity)
  have hc : Continuous (fun x : ℝ =>
      (exp (-(4 * π / 3) * x ^ 2) - π / 8 * x ^ 2 * (2 + π / 6 * x ^ 2)) /
        (2 + π / 6 * x ^ 2)) := by fun_prop
  have ht : Tendsto (fun x : ℝ =>
      (exp (-(4 * π / 3) * x ^ 2) - π / 8 * x ^ 2 * (2 + π / 6 * x ^ 2)) /
        (2 + π / 6 * x ^ 2)) (𝓝[>] 0) (𝓝 (1 / 2 : ℝ)) := by
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 < x at hx
  dsimp [smallDataG]
  field_simp [hx.ne']

end XSD
end Christodoulou.Bondi
