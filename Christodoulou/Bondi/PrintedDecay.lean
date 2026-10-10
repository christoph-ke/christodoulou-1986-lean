module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.RadialDerivative
public import Christodoulou.Frozen.Bondi.MemXBall
public import Christodoulou.Frozen.Bondi.Theorem2
public import Christodoulou.Frozen.Bondi.ExistsMemXBallOfIsClassicalSolution
public import Christodoulou.Bondi.ClassicalBridge
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.Order.Compact



public section

open Set Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi
namespace XPD

/-- The radial derivative of a classical solution is continuous on the closed strip. -/
theorem continuousOn_radialDerivative_of_isClassicalSolution
    {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : IsClassicalSolution u₀ H) :
    ContinuousOn (fun p : ℝ≥0 × ℝ≥0 => radialDerivative H p.1 p.2)
      {p | p.1 ≤ u₀} := by
  have hc := (XT2H.classical_radial_continuous hH).comp
    (NNReal.continuous_coe.prodMap NNReal.continuous_coe).continuousOn
    (show MapsTo (fun p : ℝ≥0 × ℝ≥0 => ((p.1 : ℝ), (p.2 : ℝ)))
      {p | p.1 ≤ u₀} (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) from
      fun p hp => ⟨⟨p.1.coe_nonneg, hp⟩, p.2.coe_nonneg⟩)
  simpa [Function.comp_def, radialDerivative] using hc

/-- Compact control plus uniform tail decay gives a global weighted bound. -/
theorem weighted_iff_printed_of_continuousOn {u₀ : ℝ≥0}
    (f : ℝ≥0 × ℝ≥0 → ℝ) (hf : ContinuousOn f {p | p.1 ≤ u₀}) (n : ℕ) :
    (∃ C : ℝ, ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      |f (u, r)| ≤ C * (1 + (r : ℝ)) ^ (-(n : ℤ))) ↔
    ∃ C : ℝ, ∀ᶠ r : ℝ≥0 in atTop, ∀ u : ℝ≥0, u ≤ u₀ →
      |f (u, r)| ≤ C * (r : ℝ) ^ (-(n : ℤ)) := by
  simp only [zpow_neg, zpow_natCast]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨max C 0, eventually_atTop.2 ⟨1, ?_⟩⟩
    intro r hr u hu
    have hrpos : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
    calc
      |f (u, r)| ≤ C * ((1 + (r : ℝ)) ^ n)⁻¹ := hC u hu r
      _ ≤ max C 0 * ((1 + (r : ℝ)) ^ n)⁻¹ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C 0 * ((r : ℝ) ^ n)⁻¹ :=
        mul_le_mul_of_nonneg_left
          (inv_le_inv₀ (pow_pos (by positivity) n) (pow_pos hrpos n) |>.2
            (pow_le_pow_left₀ r.coe_nonneg (by linarith) n)) (le_max_right _ _)
  · rintro ⟨C, hC⟩
    obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 hC
    let R : ℝ≥0 := max R₀ 1
    have hR₀R : R₀ ≤ R := le_max_left _ _
    have hR1 : (1 : ℝ≥0) ≤ R := le_max_right _ _
    obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
      (hf.mono (show Icc 0 u₀ ×ˢ Icc 0 R ⊆ {p | p.1 ≤ u₀} from fun p hp => hp.1.2))
    let D : ℝ := max B 0 * (1 + (R : ℝ)) ^ n + max C 0 * 2 ^ n
    refine ⟨D, fun u hu r => ?_⟩
    have hw : 0 < (1 + (r : ℝ)) ^ n := pow_pos (by positivity) n
    have hB0 : 0 ≤ max B 0 := le_max_right _ _
    have hC0 : 0 ≤ max C 0 := le_max_right _ _
    apply (le_mul_inv_iff₀ hw).2
    by_cases hr : r ≤ R
    · have hbB : |f (u, r)| ≤ B := by
        simpa only [Real.norm_eq_abs] using
          hB (u, r) ⟨⟨zero_le, hu⟩, ⟨zero_le, hr⟩⟩
      have hb : |f (u, r)| ≤ max B 0 := hbB.trans (le_max_left _ _)
      have hp : (1 + (r : ℝ)) ^ n ≤ (1 + (R : ℝ)) ^ n :=
        pow_le_pow_left₀ (by positivity) (by have hr' : (r : ℝ) ≤ R := hr; linarith) n
      exact (mul_le_mul hb hp (le_of_lt hw) hB0).trans
        (le_add_of_nonneg_right (by positivity))
    · have hRr : R ≤ r := le_of_lt (lt_of_not_ge hr)
      have hr1 : (1 : ℝ) ≤ r := hR1.trans hRr
      have hrpos : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr1
      have hb : |f (u, r)| * (r : ℝ) ^ n ≤ max C 0 := by
        have ht := hR₀ r (hR₀R.trans hRr) u hu
        exact ((le_mul_inv_iff₀ (pow_pos hrpos n)).1 ht).trans (le_max_left _ _)
      have hp : (1 + (r : ℝ)) ^ n ≤ 2 ^ n * (r : ℝ) ^ n := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) (by linarith) n
      calc
        |f (u, r)| * (1 + (r : ℝ)) ^ n ≤
            |f (u, r)| * (2 ^ n * (r : ℝ) ^ n) :=
          mul_le_mul_of_nonneg_left hp (abs_nonneg _)
        _ = (|f (u, r)| * (r : ℝ) ^ n) * 2 ^ n := by ring
        _ ≤ max C 0 * 2 ^ n := mul_le_mul_of_nonneg_right hb (by positivity)
        _ ≤ D := le_add_of_nonneg_left (by positivity)


theorem valueBound_weighted_iff_printed {u₀ : ℝ≥0} (H : C(ℝ≥0 × ℝ≥0, ℝ)) :
    (∃ C : ℝ, ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      |H (u, r)| ≤ C * (1 + (r : ℝ)) ^ (-3 : ℤ)) ↔
      ∃ C : ℝ, ∀ᶠ r : ℝ≥0 in atTop, ∀ u : ℝ≥0, u ≤ u₀ →
        |H (u, r)| ≤ C * (r : ℝ) ^ (-3 : ℤ) := by
  exact weighted_iff_printed_of_continuousOn H H.continuous.continuousOn 3


theorem radialDerivative_weighted_iff_printed {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H) :
    (∃ C : ℝ, ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
        |radialDerivative H u r| ≤ C * (1 + (r : ℝ)) ^ (-4 : ℤ)) ↔
      ∃ C : ℝ, ∀ᶠ r : ℝ≥0 in atTop, ∀ u : ℝ≥0, u ≤ u₀ →
        |radialDerivative H u r| ≤ C * (r : ℝ) ^ (-4 : ℤ) := by
  exact weighted_iff_printed_of_continuousOn _
    (continuousOn_radialDerivative_of_isClassicalSolution hH) 4

/-- [P] p. 351, Theorem 2, with the printed hypothesis ∂_r h = O(r⁻⁴) as r → ∞, uniformly in u. -/
theorem theorem2_printed {u₀ : ℝ≥0} {H K : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hcH : IsClassicalSolution u₀ H) (hcK : IsClassicalSolution u₀ K)
    (hHderiv : ∃ C : ℝ, ∀ᶠ r : ℝ≥0 in atTop, ∀ u : ℝ≥0, u ≤ u₀ →
      |radialDerivative H u r| ≤ C * (r : ℝ) ^ (-4 : ℤ))
    (hKderiv : ∃ C : ℝ, ∀ᶠ r : ℝ≥0 in atTop, ∀ u : ℝ≥0, u ≤ u₀ →
      |radialDerivative K u r| ≤ C * (r : ℝ) ^ (-4 : ℤ))
    (hdata : ∀ r : ℝ≥0, H (0, r) = K (0, r)) :
    ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0, H (u, r) = K (u, r) := by
  exact Christodoulou.Bondi.theorem2 hcH hcK
    ((radialDerivative_weighted_iff_printed hcH).mpr hHderiv)
    ((radialDerivative_weighted_iff_printed hcK).mpr hKderiv) hdata

/-- A classical solution with the printed ∂_r h = O(r⁻⁴), uniformly in u, lies in an X-ball, so
the X-ball hypothesis of the later solution and mass results is available under the printed
hypothesis. -/
theorem exists_memXBall_of_isClassicalSolution_printed {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H)
    (hderiv : ∃ C : ℝ, ∀ᶠ r : ℝ≥0 in atTop, ∀ u : ℝ≥0, u ≤ u₀ →
      |radialDerivative H u r| ≤ C * (r : ℝ) ^ (-4 : ℤ)) :
    ∃ x : ℝ, MemXBall u₀ x H := by
  exact Christodoulou.Bondi.exists_memXBall_of_isClassicalSolution hH
    ((radialDerivative_weighted_iff_printed hH).mpr hderiv)


theorem printedBound_iff_explicit {u₀ : ℝ≥0} (f : ℝ≥0 → ℝ≥0 → ℝ) (k : ℤ) :
    (∃ C : ℝ, ∀ᶠ r : ℝ≥0 in atTop, ∀ u : ℝ≥0, u ≤ u₀ → |f u r| ≤ C * (r : ℝ) ^ k) ↔
      ∃ C R : ℝ, 0 < R ∧ ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0, R ≤ r →
        |f u r| ≤ C * (r : ℝ) ^ k := by
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.1 hC
    refine ⟨C, max (R₀ : ℝ) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro u hu r hr
    have hR₀r : R₀ ≤ r := by
      exact_mod_cast (le_max_left (R₀ : ℝ) 1).trans hr
    exact hR₀ r hR₀r u hu
  · rintro ⟨C, R, hR, hC⟩
    refine ⟨C, Filter.eventually_atTop.2 ⟨R.toNNReal, ?_⟩⟩
    intro r hr u hu
    have hRr : R ≤ (r : ℝ) := by
      have hco : (R.toNNReal : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      simpa only [Real.coe_toNNReal R (le_of_lt hR)] using hco
    exact hC u hu r hRr

end XPD

end Christodoulou.Bondi
