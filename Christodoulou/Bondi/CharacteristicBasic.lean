module
public import Christodoulou.Frozen.Bondi.IsCharacteristic
public import Christodoulou.Frozen.Bondi.GBarXPos
public import Christodoulou.Frozen.Bondi.GBarXLeOne
public import Christodoulou.Frozen.Bondi.LipschitzWithGBarX
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Uniqueness and physical bounds for backward characteristics

The sealed coefficient estimates give uniqueness from the terminal datum, physical radial
bounds, and strict decrease on the closed time interval, including its degenerate case.
-/

public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi

private theorem lipschitzWith_charField {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (t : ℝ) :
    LipschitzWith (Real.toNNReal (π / 6 * x ^ 2)) (charField hH t) := by
  refine LipschitzWith.of_dist_le_mul fun z w => ?_
  calc
    dist (charField hH t z) (charField hH t w) =
        (1 / 2 : ℝ) * dist (gBarX hH t.toNNReal z.toNNReal)
          (gBarX hH t.toNNReal w.toNNReal) := by
      simp only [charField, Real.dist_eq, ← mul_sub, abs_mul]
      norm_num
    _ ≤ dist (gBarX hH t.toNNReal z.toNNReal)
        (gBarX hH t.toNNReal w.toNNReal) :=
      mul_le_of_le_one_left dist_nonneg (by norm_num)
    _ ≤ _ := (lipschitzWith_gBarX hH t.toNNReal).dist_le_mul z w

private theorem charField_neg {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (t z : ℝ) : charField hH t z < 0 :=
  mul_neg_of_neg_of_pos (by norm_num) (gBarX_pos hH t.toNNReal z.toNNReal)

/-- Uniqueness: two characteristics through the same terminal point agree on `[0, u₁]`. -/
theorem XChar.eqOn {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ ψ : ℝ → ℝ}
    (hχ : IsCharacteristic hH u₁ r₁ χ) (hψ : IsCharacteristic hH u₁ r₁ ψ) :
    EqOn χ ψ (Icc 0 (u₁ : ℝ)) := by
  exact ODE_solution_unique_of_mem_Icc_left
    (s := fun _ => univ) (fun t _ => (lipschitzWith_charField hH t).lipschitzOnWith)
    (HasDerivWithinAt.continuousOn hχ.2)
    (fun t ht => (hχ.2 t ⟨ht.1.le, ht.2⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLE_of_mem ht)) (fun _ _ => mem_univ _)
    (HasDerivWithinAt.continuousOn hψ.2)
    (fun t ht => (hψ.2 t ⟨ht.1.le, ht.2⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLE_of_mem ht)) (fun _ _ => mem_univ _) (hχ.1.trans hψ.1.symm)

/-- The characteristic stays in the physical domain: `r₁ ≤ χ(t) ≤ r₁ + (u₁ − t)/2` on `[0, u₁]`
(from `0 < ḡ ≤ 1`; the upper bound at `t = 0` is (5.3), p. 346). -/
theorem XChar.mem_Icc {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH u₁ r₁ χ) {t : ℝ} (ht : t ∈ Icc 0 (u₁ : ℝ)) :
    χ t ∈ Icc (r₁ : ℝ) (r₁ + ((u₁ : ℝ) - t) / 2) := by
  have hc : ContinuousOn χ (Icc 0 (u₁ : ℝ)) := HasDerivWithinAt.continuousOn hχ.2
  have ha : AntitoneOn χ (Icc 0 (u₁ : ℝ)) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) hc
      (fun s hs => (hχ.2 s (interior_subset hs)).mono interior_subset)
      (fun s _ => (charField_neg hH s (χ s)).le)
  have hm : MonotoneOn (fun s => χ s + s / 2) (Icc 0 (u₁ : ℝ)) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (hc.add (continuous_id.div_const 2).continuousOn)
      (fun s hs => ((hχ.2 s (interior_subset hs)).mono interior_subset).add
        ((hasDerivAt_id s).div_const 2).hasDerivWithinAt) ?_
    intro s _
    have hg := gBarX_le_one hH s.toNNReal (χ s).toNNReal
    dsimp only [charField]
    linarith only [hg]
  have hu : (u₁ : ℝ) ∈ Icc 0 (u₁ : ℝ) := ⟨u₁.2.1, le_rfl⟩
  constructor
  · calc
      (r₁ : ℝ) = χ u₁ := hχ.1.symm
      _ ≤ χ t := ha ht hu ht.2
  · have hb : χ t + t / 2 ≤ χ u₁ + (u₁ : ℝ) / 2 := hm ht hu ht.2
    rw [hχ.1] at hb
    linarith only [hb]

/-- A characteristic decreases strictly in time on `[0, u₁]` (since `ḡ > 0`). -/
theorem XChar.strictAntiOn {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hH u₁ r₁ χ) : StrictAntiOn χ (Icc 0 (u₁ : ℝ)) := by
  exact strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
    (HasDerivWithinAt.continuousOn hχ.2)
    (fun t ht => (hχ.2 t (interior_subset ht)).mono interior_subset)
    (fun t _ => charField_neg hH t (χ t))

end Christodoulou.Bondi
