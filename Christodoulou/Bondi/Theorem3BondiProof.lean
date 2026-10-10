module
public import Christodoulou.Frozen.Bondi.AntitoneOnBondiMass
public import Christodoulou.Frozen.Bondi.Theorem3MassZero
public import Christodoulou.Frozen.Bondi.BondiMass
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.RadialDerivative
public import Christodoulou.Frozen.Bondi.SmallDataDelta
public import Christodoulou.Frozen.Bondi.ContractionFactor
public import Christodoulou.Frozen.Bondi.ScaleInvariantSize
public import Christodoulou.Frozen.Bondi.IsDecaySlice
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

/-!
# Theorem 3 with Bondi mass monotonicity

The global decay from `theorem3_mass_zero` supplies the derivative bound on every closed
time strip. The sealed Bondi theorem then gives global antitonicity, while preserving the
small-data witnesses, solution, slice family, and zero-mass limit.
-/

public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi

namespace XT3B

/-- The value bound at the origin makes the common decay constant nonnegative. -/
private theorem decay_constant_nonneg {H : C(ℝ≥0 × ℝ≥0, ℝ)} {C : ℝ}
    (h : ∀ u r : ℝ≥0,
      |H (u, r)| ≤ C * (1 + (u : ℝ) + (r : ℝ)) ^ (-3 : ℤ) ∧
      |radialDerivative H u r| ≤ C * (1 + (u : ℝ) + (r : ℝ)) ^ (-4 : ℤ)) :
    0 ≤ C := by
  have h0 := (h 0 0).1
  simp only [NNReal.coe_zero, add_zero, one_zpow, mul_one] at h0
  exact (abs_nonneg _).trans h0

/-- The global radial decay implies the uniform derivative bound on each time strip. -/
private theorem radial_bound_on_strip {H : C(ℝ≥0 × ℝ≥0, ℝ)} {C : ℝ}
    (hC : 0 ≤ C)
    (hd : ∀ u r : ℝ≥0,
      |radialDerivative H u r| ≤ C * (1 + (u : ℝ) + (r : ℝ)) ^ (-4 : ℤ))
    (T : ℝ≥0) :
    ∀ u : ℝ≥0, u ≤ T → ∀ r : ℝ≥0,
      |radialDerivative H u r| ≤ C * (1 + (r : ℝ)) ^ (-4 : ℤ) := by
  intro u _ r
  apply (hd u r).trans
  apply mul_le_mul_of_nonneg_left _ hC
  simp only [zpow_neg, zpow_ofNat]
  apply inv_le_inv₀ (by positivity) (by positivity) |>.2
  exact pow_le_pow_left₀ (by positivity) (by nlinarith [u.coe_nonneg]) 4

/-- The global small-data solution has nonincreasing Bondi mass tending to zero. -/
theorem theorem3_bondi : ∃ δ : ℝ, 0 < δ ∧
    (∃ x₁ : ℝ≥0, 0 < x₁ ∧ contractionFactor x₁ = 1 ∧ δ = smallDataDelta x₁) ∧
    ∀ (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data), scaleInvariantSize data hdata < δ →
      ∃ H : C(ℝ≥0 × ℝ≥0, ℝ),
        (∀ T : ℝ≥0, IsClassicalSolution T H) ∧
        (∀ r, H (0, r) = data r) ∧
        (∃ C : ℝ, ∀ u r : ℝ≥0,
          |H (u, r)| ≤ C * (1 + (u : ℝ) + (r : ℝ)) ^ (-3 : ℤ) ∧
          |radialDerivative H u r| ≤ C * (1 + (u : ℝ) + (r : ℝ)) ^ (-4 : ℤ)) ∧
        ∃ hs : ∀ u : ℝ≥0, IsSlice (H.curry u),
          Antitone (fun u : ℝ≥0 => bondiMass (H.curry u) (hs u)) ∧
          Tendsto (fun u : ℝ≥0 => bondiMass (H.curry u) (hs u)) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hx, hdata⟩ := theorem3_mass_zero
  refine ⟨δ, hδ, hx, ?_⟩
  intro data hd hsmall
  obtain ⟨H, hH, hinit, ⟨C, hdecay⟩, hs, hlim⟩ := hdata data hd hsmall
  refine ⟨H, hH, hinit, ⟨C, hdecay⟩, hs, ?_, hlim⟩
  have hstrip := radial_bound_on_strip (decay_constant_nonneg hdecay)
    (fun u r => (hdecay u r).2)
  intro a b hab
  exact antitoneOn_bondiMass (hH b) hs (hstrip b) ⟨bot_le, hab⟩ ⟨bot_le, le_rfl⟩ hab

end XT3B

end Christodoulou.Bondi
