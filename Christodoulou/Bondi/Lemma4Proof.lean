module
public import Christodoulou.Frozen.Bondi.SmallDataG
public import Christodoulou.Frozen.Bondi.TranslatedDataField
public import Christodoulou.Frozen.Bondi.MemXPrimeBall
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.IsDecaySlice
public import Christodoulou.Frozen.Bondi.InitialBound
import Christodoulou.Frozen.Bondi.LinearStepPrimeBound
import Christodoulou.Frozen.Bondi.TranslatedDataFieldMemXPrimeBall
import Christodoulou.Bondi.XPrimeBasics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma 4 on the frozen X′ gates

The exact small-data inequality makes the X′ ball invariant under the frozen linear step.
The frozen translated-seed bound starts a unique subtype-valued sequence on every time strip.
-/

public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi
namespace XL4

private theorem invariance_iff {x d : ℝ} :
    (2 + π / 6 * x ^ 2) * exp (4 * π / 3 * x ^ 2) * (d + π / 8 * x ^ 3) ≤ x ↔
      d ≤ smallDataG x := by
  have hA : 0 < 2 + π / 6 * x ^ 2 := by positivity
  have hE := exp_pos (4 * π / 3 * x ^ 2)
  have hG : smallDataG x =
      x / ((2 + π / 6 * x ^ 2) * exp (4 * π / 3 * x ^ 2)) - π / 8 * x ^ 3 := by
    unfold smallDataG
    rw [show -(4 * π / 3) * x ^ 2 = -(4 * π / 3 * x ^ 2) by ring, exp_neg]
    field_simp
  rw [hG, ← le_div_iff₀' (mul_pos hA hE)]
  constructor <;> intro h <;> linarith only [h]

private theorem smallDataG_lt_half {x : ℝ} (hx : 0 < x) : smallDataG x < x / 2 := by
  have hA : 2 < 2 + π / 6 * x ^ 2 := lt_add_of_pos_right 2 (by positivity)
  have hE : exp (-(4 * π / 3) * x ^ 2) ≤ 1 :=
    exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (sq_nonneg x))
  have hsub : exp (-(4 * π / 3) * x ^ 2) -
      π / 8 * x ^ 2 * (2 + π / 6 * x ^ 2) ≤ 1 :=
    (sub_le_self _ (by positivity)).trans hE
  calc
    smallDataG x ≤ x / (2 + π / 6 * x ^ 2) := by
      unfold smallDataG
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hsub (by positivity)
    _ < x / 2 := div_lt_div_of_pos_left hx (by norm_num) hA

/-- Lemma 4: the translated seed generates a unique sequence in the X′ ball. -/
theorem lemma4 {T : ℝ≥0} {x d : ℝ} (hx : 0 < x) (hd : 0 ≤ d)
    (hsmall : d ≤ smallDataG x) (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data)
    (hbound : InitialBound data d) :
    ∃! h : ℕ → {H : C(ℝ≥0 × ℝ≥0, ℝ) // MemXPrimeBall T x H},
      (h 0).val = translatedDataField T data ∧
      ∀ n, (h (n + 1)).val = linearStepMap (h n).property.1 data := by
  have hdx : d ≤ x :=
    (hsmall.trans (smallDataG_lt_half hx).le).trans (by linarith only [hx])
  have hseed : MemXPrimeBall T x (translatedDataField T data) :=
    (translatedDataField_memXPrimeBall data hdata hbound).mono hdx
  have hinvariant := invariance_iff.mpr hsmall
  let seed : {H : C(ℝ≥0 × ℝ≥0, ℝ) // MemXPrimeBall T x H} :=
    ⟨translatedDataField T data, hseed⟩
  let step (H : {H : C(ℝ≥0 × ℝ≥0, ℝ) // MemXPrimeBall T x H}) :
      {H : C(ℝ≥0 × ℝ≥0, ℝ) // MemXPrimeBall T x H} :=
    ⟨linearStepMap H.property.1 data,
      (linearStep_prime_bound H.property data hdata hd hbound).mono hinvariant⟩
  let h : ℕ → {H : C(ℝ≥0 × ℝ≥0, ℝ) // MemXPrimeBall T x H} :=
    fun n => Nat.rec seed (fun _ H => step H) n
  refine ⟨h, ⟨rfl, fun _ => rfl⟩, ?_⟩
  intro k hk
  funext n
  induction n with
  | zero => exact Subtype.ext hk.1
  | succ n ih =>
    apply Subtype.ext
    calc
      (k (n + 1)).val = linearStepMap (k n).property.1 data := hk.2 n
      _ = linearStepMap (h n).property.1 data :=
        congrArg (fun H : {H : C(ℝ≥0 × ℝ≥0, ℝ) // MemXPrimeBall T x H} =>
          linearStepMap H.property.1 data) ih
      _ = (h (n + 1)).val := rfl

end XL4
end Christodoulou.Bondi
