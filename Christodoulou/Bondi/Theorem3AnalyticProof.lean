module
public import Christodoulou.Frozen.Bondi.FieldScale
public import Christodoulou.Frozen.Bondi.ScaleInvariantSize
public import Christodoulou.Frozen.Bondi.SmallDataDelta
public import Christodoulou.Frozen.Bondi.ContractionFactor
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.RadialDerivative
import Christodoulou.Frozen.Bondi.Theorem3Unscaled
import Christodoulou.Frozen.Bondi.ExistsScaledInitialSizeLt
import Christodoulou.Frozen.Bondi.IsDecaySliceRadialScale
import Christodoulou.Frozen.Bondi.InitialSizeRadialScale
import Christodoulou.Frozen.Bondi.IsClassicalSolutionFieldScale
import Christodoulou.Frozen.Bondi.RadialDerivativeFieldScale
import Christodoulou.Bondi.ScalingBasic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The analytic conclusion of Theorem 3

Rescale admissible data to apply the sealed unscaled theorem, then transfer the solution
and its decay bounds back by inverse scaling. The small-data threshold and its contraction
witness are inherited from the unscaled theorem. The explicit decay constants are unfrozen
helpers. The mass and geodesic-completeness conclusions remain outside this module's scope.
-/

public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi
namespace XT3A

/-- The denominator comparison used to transfer the global weighted decay. -/
theorem scaled_decay_weight {a : ℝ≥0} (ha : 0 < a) (u r : ℝ≥0) (n : ℕ) :
    (1 + ((a⁻¹ * u : ℝ≥0) : ℝ) + ((a⁻¹ * r : ℝ≥0) : ℝ)) ^ (-(n : ℤ)) ≤
      max 1 (a : ℝ) ^ n * (1 + (u : ℝ) + (r : ℝ)) ^ (-(n : ℤ)) := by
  have ha' : (0 : ℝ) < a := ha
  have hM : 1 ≤ max 1 (a : ℝ) / (a : ℝ) := by
    rw [le_div_iff₀ ha']
    simpa only [one_mul] using le_max_right 1 (a : ℝ)
  have hq : 1 + (u : ℝ) + (r : ℝ) ≤ max 1 (a : ℝ) *
      (1 + ((a⁻¹ * u : ℝ≥0) : ℝ) + ((a⁻¹ * r : ℝ≥0) : ℝ)) := by
    calc
      _ ≤ max 1 (a : ℝ) + (u : ℝ) + (r : ℝ) := by
        linarith only [le_max_left 1 (a : ℝ)]
      _ ≤ max 1 (a : ℝ) + (max 1 (a : ℝ) / (a : ℝ)) * (u : ℝ) +
          (max 1 (a : ℝ) / (a : ℝ)) * (r : ℝ) := by
        have hu := mul_le_mul_of_nonneg_right hM u.coe_nonneg
        have hr := mul_le_mul_of_nonneg_right hM r.coe_nonneg
        simp only [one_mul] at hu hr
        linarith only [hu, hr]
      _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_inv, div_eq_mul_inv]; ring
  have hs : 0 < 1 + ((a⁻¹ * u : ℝ≥0) : ℝ) + ((a⁻¹ * r : ℝ≥0) : ℝ) := by positivity
  have hq0 : 0 < 1 + (u : ℝ) + (r : ℝ) := by positivity
  have hi : (1 + ((a⁻¹ * u : ℝ≥0) : ℝ) + ((a⁻¹ * r : ℝ≥0) : ℝ))⁻¹ ≤
      max 1 (a : ℝ) / (1 + (u : ℝ) + (r : ℝ)) := by
    rw [inv_eq_one_div, div_le_div_iff₀ hs hq0]
    simpa only [one_mul] using hq
  have hp := pow_le_pow_left₀ (inv_nonneg.mpr hs.le) hi n
  simpa only [zpow_neg, zpow_natCast, inv_pow, div_pow, div_eq_mul_inv, mul_pow] using hp

/-- Transfer the explicit decay bounds to the inverse-scaled field. -/
theorem fieldScale_inv_decay_explicit {a : ℝ≥0} (ha : 0 < a)
    {H' : C(ℝ≥0 × ℝ≥0, ℝ)} {x : ℝ} (hx : 0 ≤ x)
    (hdecay : ∀ u r : ℝ≥0,
      |H' (u, r)| ≤ 8 * x * (1 + (u : ℝ) + (r : ℝ)) ^ (-3 : ℤ) ∧
      |radialDerivative H' u r| ≤ 16 * x * (1 + (u : ℝ) + (r : ℝ)) ^ (-4 : ℤ)) :
    ∀ u r : ℝ≥0,
      |fieldScale a⁻¹ H' (u, r)| ≤
        (8 * x * max 1 (a : ℝ) ^ 3) * (1 + (u : ℝ) + (r : ℝ)) ^ (-3 : ℤ) ∧
      |radialDerivative (fieldScale a⁻¹ H') u r| ≤
        ((16 * x / (a : ℝ)) * max 1 (a : ℝ) ^ 4) *
          (1 + (u : ℝ) + (r : ℝ)) ^ (-4 : ℤ) := by
  intro u r
  obtain ⟨hv, hd⟩ := hdecay (a⁻¹ * u) (a⁻¹ * r)
  constructor
  · calc
      _ ≤ 8 * x * (1 + ((a⁻¹ * u : ℝ≥0) : ℝ) + ((a⁻¹ * r : ℝ≥0) : ℝ)) ^ (-3 : ℤ) := hv
      _ ≤ 8 * x * (max 1 (a : ℝ) ^ 3 * (1 + (u : ℝ) + (r : ℝ)) ^ (-3 : ℤ)) :=
        mul_le_mul_of_nonneg_left (scaled_decay_weight ha u r 3) (by positivity)
      _ = _ := by ring
  · rw [radialDerivative_fieldScale (inv_pos.mpr ha), abs_mul,
      NNReal.coe_inv, abs_of_nonneg (inv_nonneg.mpr a.coe_nonneg)]
    calc
      _ ≤ (a : ℝ)⁻¹ * (16 * x *
          (1 + ((a⁻¹ * u : ℝ≥0) : ℝ) + ((a⁻¹ * r : ℝ≥0) : ℝ)) ^ (-4 : ℤ)) :=
        mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr a.coe_nonneg)
      _ ≤ (a : ℝ)⁻¹ * (16 * x *
          (max 1 (a : ℝ) ^ 4 * (1 + (u : ℝ) + (r : ℝ)) ^ (-4 : ℤ))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (scaled_decay_weight ha u r 4) (by positivity))
          (inv_nonneg.mpr a.coe_nonneg)
      _ = _ := by simp only [div_eq_mul_inv]; ring

/-- The analytic Theorem 3 with explicit scale-dependent decay constants. -/
theorem theorem3_analytic_explicit : ∃ δ : ℝ, 0 < δ ∧
    (∃ x₁ : ℝ≥0, 0 < x₁ ∧ contractionFactor x₁ = 1 ∧ δ = smallDataDelta x₁) ∧
    ∀ (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data), scaleInvariantSize data hdata < δ →
      ∃ a : ℝ≥0, 0 < a ∧ ∃ x : ℝ, 0 < x ∧
      ∃ H : C(ℝ≥0 × ℝ≥0, ℝ),
        (∀ T : ℝ≥0, IsClassicalSolution T H) ∧
        (∀ r, H (0, r) = data r) ∧
        ∀ u r : ℝ≥0,
          |H (u, r)| ≤ (8 * x * max 1 (a : ℝ) ^ 3) * (1 + (u : ℝ) + (r : ℝ)) ^ (-3 : ℤ) ∧
          |radialDerivative H u r| ≤ ((16 * x / (a : ℝ)) * max 1 (a : ℝ) ^ 4) *
            (1 + (u : ℝ) + (r : ℝ)) ^ (-4 : ℤ) := by
  obtain ⟨δ, hδ, hx₁, hsmall⟩ := Christodoulou.Bondi.theorem3_unscaled
  refine ⟨δ, hδ, hx₁, ?_⟩
  intro data hdata hd₀
  obtain ⟨a, ha, hsize⟩ := exists_scaledInitialSize_lt hdata hd₀
  have hs := isDecaySlice_radialScale ha hdata
  have hd : initialSize (radialScale a data) hs < δ := by
    rw [initialSize_radialScale ha hdata hs]
    exact hsize
  obtain ⟨H', x, hx, hH', htrace, hdecay⟩ := hsmall (radialScale a data) hs hd
  refine ⟨a, ha, x, hx, fieldScale a⁻¹ H', ?_, ?_, ?_⟩
  · intro T
    exact isClassicalSolution_fieldScale (inv_pos.mpr ha) (hH' (a⁻¹ * T)).1
  · intro r
    rw [XSB.fieldScale_apply, mul_zero, htrace, XSB.radialScale_apply,
      ← mul_assoc, mul_inv_cancel₀ (ne_of_gt ha), one_mul]
  · exact fieldScale_inv_decay_explicit ha hx.le hdecay

/-- The analytic conclusion of Theorem 3 under the scale-invariant small-data hypothesis. -/
theorem theorem3_analytic : ∃ δ : ℝ, 0 < δ ∧
    (∃ x₁ : ℝ≥0, 0 < x₁ ∧ contractionFactor x₁ = 1 ∧ δ = smallDataDelta x₁) ∧
    ∀ (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data), scaleInvariantSize data hdata < δ →
      ∃ H : C(ℝ≥0 × ℝ≥0, ℝ),
        (∀ T : ℝ≥0, IsClassicalSolution T H) ∧
        (∀ r, H (0, r) = data r) ∧
        ∃ C : ℝ, ∀ u r : ℝ≥0,
          |H (u, r)| ≤ C * (1 + (u : ℝ) + (r : ℝ)) ^ (-3 : ℤ) ∧
          |radialDerivative H u r| ≤ C * (1 + (u : ℝ) + (r : ℝ)) ^ (-4 : ℤ) := by
  obtain ⟨δ, hδ, hx₁, hsmall⟩ := theorem3_analytic_explicit
  refine ⟨δ, hδ, hx₁, ?_⟩
  intro data hdata hd₀
  obtain ⟨a, _, x, _, H, hH, htrace, hdecay⟩ := hsmall data hdata hd₀
  refine ⟨H, hH, htrace, ?_⟩
  let Cv : ℝ := 8 * x * max 1 (a : ℝ) ^ 3
  let Cd : ℝ := (16 * x / (a : ℝ)) * max 1 (a : ℝ) ^ 4
  refine ⟨max Cv Cd, ?_⟩
  intro u r
  obtain ⟨hv, hd⟩ := hdecay u r
  constructor
  · exact hv.trans (mul_le_mul_of_nonneg_right (le_max_left Cv Cd) (by positivity))
  · exact hd.trans (mul_le_mul_of_nonneg_right (le_max_right Cv Cd) (by positivity))


end XT3A
end Christodoulou.Bondi
