module
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.LinearStep
public import Christodoulou.Frozen.Bondi.StepDelta
public import Christodoulou.Frozen.Bondi.XBallIterate
public import Christodoulou.Frozen.Bondi.IsDecaySlice
import Christodoulou.Frozen.Bondi.CoefficientYLipschitz
import Christodoulou.Frozen.Bondi.StepDeltaPosAndBound
import Christodoulou.Frozen.Bondi.LinearStepDifferenceIntegral
import Christodoulou.Frozen.Bondi.LinearStepMapApply
import Christodoulou.Frozen.Bondi.HasDerivWithinAtLinearStep
import Christodoulou.Frozen.Bondi.IsCharacteristicCharacteristic
import Christodoulou.Frozen.Bondi.IsCharacteristicMemIcc
import Christodoulou.Frozen.Bondi.XBallIterateRec
import Christodoulou.Bondi.StepDifference

/-!
# The Y-Lipschitz bound and Lemma 2

The coefficient differences and the output X-ball bound control the source of the difference
integral. Backward characteristics transfer its radial weight to the terminal point. The
explicit contraction time then gives Lemma 2 for the canonical ball-valued iterates.
-/

public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi
namespace XL2

private theorem remainder_bound {u₀ : ℝ≥0} {x : ℝ}
    {H K : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (hK : MemXBall u₀ x K)
    (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data s.toNNReal) (Ici 0))
    (hSK : MemXBall u₀ x (linearStepMap hK data)) {y : ℝ} (hy0 : 0 ≤ y)
    (hy : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0,
      (1 + (r : ℝ)) ^ 3 * |H (u, r) - K (u, r)| ≤ y)
    (u r : ℝ≥0) (hu : u ≤ u₀) :
    |(gBarX hH u r - gBarX hK u r) / 2 * derivLinearStep hK data hdata u r +
      (linearCoeff hH u r - linearCoeff hK u r) * linearStep hK data u r +
      linearSource hH u r - linearSource hK u r| ≤
      (π * x ^ 2 * (37 / 6 + 2 * π * x ^ 2)) * y / (1 + (r : ℝ)) ^ 3 := by
  let w := 1 + (r : ℝ)
  let S := linearStep hK data u r
  let q := derivLinearStep hK data hdata u r
  have hw : 0 < w := by dsimp [w]; positivity
  have hw1 : 1 ≤ w := by dsimp [w]; linarith only [r.coe_nonneg]
  have hbudget := hSK.2.2 u hu r
  simp only [linearStepMap_apply] at hbudget
  have hqeq := (hasDerivWithinAt_linearStep hK data hdata u r).derivWithin
    (uniqueDiffOn_Ici 0 r r.coe_nonneg)
  rw [hqeq] at hbudget
  change w ^ 3 * |S| + w ^ 4 * |q| ≤ x at hbudget
  have hx : 0 ≤ x := (add_nonneg
    (mul_nonneg (pow_pos hw 3).le (abs_nonneg S))
    (mul_nonneg (pow_pos hw 4).le (abs_nonneg q))).trans hbudget
  have hSv : |S| ≤ x / w ^ 3 := (le_div_iff₀ (pow_pos hw 3)).mpr (by
    nlinarith only [hbudget, mul_nonneg (pow_pos hw 4).le (abs_nonneg q)])
  have hqv : |q| ≤ x / w ^ 4 := (le_div_iff₀ (pow_pos hw 4)).mpr (by
    nlinarith only [hbudget, mul_nonneg (pow_pos hw 3).le (abs_nonneg S)])
  have hSw : |S| ≤ x / w := hSv.trans (div_le_div_of_nonneg_left hx hw
    (by simpa only [pow_one] using pow_le_pow_right₀ hw1 (by norm_num : 1 ≤ 3)))
  have hqw : |q| ≤ x / w ^ 2 := hqv.trans (div_le_div_of_nonneg_left hx
    (pow_pos hw 2) (pow_le_pow_right₀ hw1 (by norm_num : 2 ≤ 4)))
  obtain ⟨_, _, hg, ha, hf⟩ := coefficient_y_lipschitz hH hK hy u r
  have hgterm : |(gBarX hH u r - gBarX hK u r) / 2 * q| ≤
      2 * π * x ^ 2 * y / w ^ 3 := by
    rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ (4 * π * x * y / w / 2) * (x / w ^ 2) :=
        mul_le_mul (div_le_div_of_nonneg_right hg (by norm_num)) hqw
          (abs_nonneg q) (by positivity)
      _ = _ := by field_simp; ring
  have hac : |linearCoeff hH u r - linearCoeff hK u r| ≤
      π * x * (2 + π * x ^ 2) * y / w ^ 2 := by
    rw [linearCoeff, linearCoeff, ← mul_sub, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc
      _ ≤ 1 / 2 * (2 * π * x * (2 + π * x ^ 2) * y / w ^ 2) :=
        mul_le_mul_of_nonneg_left ha (by norm_num)
      _ = _ := by ring
  have haterm : |(linearCoeff hH u r - linearCoeff hK u r) * S| ≤
      π * x ^ 2 * (2 + π * x ^ 2) * y / w ^ 3 := by
    rw [abs_mul]
    calc
      _ ≤ (π * x * (2 + π * x ^ 2) * y / w ^ 2) * (x / w) :=
        mul_le_mul hac hSw (abs_nonneg S) (by positivity)
      _ = _ := by field_simp
  calc
    _ = |(gBarX hH u r - gBarX hK u r) / 2 * q +
        (linearCoeff hH u r - linearCoeff hK u r) * S +
        (linearSource hH u r - linearSource hK u r)| := by
      congr 1
      dsimp [q, S]
      ring
    _ ≤ (|(gBarX hH u r - gBarX hK u r) / 2 * q| +
        |(linearCoeff hH u r - linearCoeff hK u r) * S|) +
        |linearSource hH u r - linearSource hK u r| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 2 * π * x ^ 2 * y / w ^ 3 +
        π * x ^ 2 * (2 + π * x ^ 2) * y / w ^ 3 +
        π * x ^ 2 * (13 / 6 + π * x ^ 2) * y / w ^ 3 :=
      add_le_add (add_le_add hgterm haterm) hf
    _ = _ := by dsimp [w]; ring

/-- The linear step is Lipschitz in the field in the weighted Y-bound. -/
theorem linearStep_y_lipschitz {u₀ : ℝ≥0} {x : ℝ}
    {H K : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (hK : MemXBall u₀ x K)
    (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data s.toNNReal) (Ici 0))
    (hSK : MemXBall u₀ x (linearStepMap hK data)) {y : ℝ}
    (hy : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |H (u, r) - K (u, r)| ≤ y)
    (u r : ℝ≥0) (hu : u ≤ u₀) :
    (1 + (r : ℝ)) ^ 3 * |linearStep hH data u r - linearStep hK data u r| ≤
      (u₀ : ℝ) * exp (π * x ^ 2 / 12 * (u₀ : ℝ)) *
        (π * x ^ 2 * (37 / 6 + 2 * π * x ^ 2)) * y := by
  have hy0 : 0 ≤ y := (by positivity :
    0 ≤ (1 + ((0 : ℝ≥0) : ℝ)) ^ 3 * |H (0, 0) - K (0, 0)|).trans
      (hy 0 bot_le 0)
  let v : Icc (0 : ℝ) u₀ := ⟨u, u.coe_nonneg, hu⟩
  let C := (π * x ^ 2 * (37 / 6 + 2 * π * x ^ 2)) * y
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb := XDiff.abs_linearStep_sub_le hH hK data hdata v r C
  dsimp only at hb
  have hpoint : ∀ s ∈ Icc 0 (v : ℝ),
      |(gBarX hH s.toNNReal (characteristic hH v r s).toNNReal -
        gBarX hK s.toNNReal (characteristic hH v r s).toNNReal) / 2 *
          derivLinearStep hK data hdata s.toNNReal (characteristic hH v r s).toNNReal +
        (linearCoeff hH s.toNNReal (characteristic hH v r s).toNNReal -
          linearCoeff hK s.toNNReal (characteristic hH v r s).toNNReal) *
            linearStep hK data s.toNNReal (characteristic hH v r s).toNNReal +
        linearSource hH s.toNNReal (characteristic hH v r s).toNNReal -
          linearSource hK s.toNNReal (characteristic hH v r s).toNNReal| ≤
        C / (1 + (r : ℝ)) ^ 3 := by
    intro s hs
    have hsT : s.toNNReal ≤ u₀ :=
      Real.toNNReal_le_iff_le_coe.mpr (hs.2.trans v.2.2)
    have hr := ((isCharacteristic_characteristic hH v r).mem_Icc hs).1
    have hρ : (r : ℝ) ≤ (characteristic hH v r s).toNNReal :=
      hr.trans (Real.le_coe_toNNReal _)
    exact (remainder_bound hH hK data hdata hSK hy0 hy _ _ hsT).trans
      (div_le_div_of_nonneg_left hC (by positivity) (by gcongr))
  have hi := hb hpoint
  simp only [v, Real.toNNReal_coe] at hi
  have hw : 0 < (1 + (r : ℝ)) ^ 3 := by positivity
  have hiw := (le_div_iff₀ hw).mp hi
  calc
    _ = |linearStep hH data u r - linearStep hK data u r| * (1 + (r : ℝ)) ^ 3 :=
      mul_comm _ _
    _ ≤ (u : ℝ) * exp (π * x ^ 2 / 12 * (u₀ : ℝ)) * C := hiw
    _ ≤ (u₀ : ℝ) * exp (π * x ^ 2 / 12 * (u₀ : ℝ)) * C :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (show (u : ℝ) ≤ u₀ from hu) (exp_pos _).le) hC
    _ = _ := by dsimp [C]; ring

/-- Lemma 2: the explicit positive time makes successive iterates contract in Y. -/
theorem lemma2 (x₁ : ℝ) :
    ∃ δ : ℝ, δ = stepDelta x₁ ∧ 0 < δ ∧
      ∀ (d : ℝ) (hd : 0 ≤ d) (hx : 2 * d < x₁) (u₀ : ℝ≥0)
        (hT : (u₀ : ℝ) < stepEta x₁ d), (u₀ : ℝ) < δ →
      ∀ (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
        (hbound : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |data r| +
          (1 + (r : ℝ)) ^ 4 *
            |derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) r| ≤ d)
        (n : ℕ) (y : ℝ),
      (∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 *
        |(xBallIterate hd hx hT data hdata hbound (n + 1)).val (u, r) -
          (xBallIterate hd hx hT data hdata hbound n).val (u, r)| ≤ y) →
      ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 *
        |(xBallIterate hd hx hT data hdata hbound (n + 2)).val (u, r) -
          (xBallIterate hd hx hT data hdata hbound (n + 1)).val (u, r)| ≤ y / 2 := by
  refine ⟨stepDelta x₁, rfl, (stepDelta_pos_and_bound x₁).1, ?_⟩
  intro d hd hx u₀ hT hδ data hdata hbound n y hy u hu r
  let b := xBallIterate hd hx hT data hdata hbound
  have hrec := (xBallIterate_rec hd hx hT data hdata hbound).2.1
  have hSK : MemXBall u₀ x₁ (linearStepMap (b n).property data) := by
    rw [← hrec n]
    exact (b (n + 1)).property
  have hi := linearStep_y_lipschitz (b (n + 1)).property (b n).property
    data hdata.1.1 hSK hy u r hu
  have hy0 : 0 ≤ y := (by positivity :
    0 ≤ (1 + ((0 : ℝ≥0) : ℝ)) ^ 3 *
      |(b (n + 1)).val (0, 0) - (b n).val (0, 0)|).trans (hy 0 bot_le 0)
  have hc := (stepDelta_pos_and_bound x₁).2 u₀ u₀.coe_nonneg hδ
  have hfinal := hi.trans (by
    calc
      _ ≤ (1 / 2) * y := mul_le_mul_of_nonneg_right hc hy0
      _ = y / 2 := by ring)
  have hnext := congrArg (fun F : C(ℝ≥0 × ℝ≥0, ℝ) => F (u, r)) (hrec (n + 1))
  have hcurrent := congrArg (fun F : C(ℝ≥0 × ℝ≥0, ℝ) => F (u, r)) (hrec n)
  simp only [linearStepMap_apply] at hnext hcurrent
  rw [show n + 2 = (n + 1) + 1 from rfl, hnext, hcurrent]
  exact hfinal

end XL2
end Christodoulou.Bondi
