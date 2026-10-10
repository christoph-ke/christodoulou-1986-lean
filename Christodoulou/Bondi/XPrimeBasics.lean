module
public import Christodoulou.Frozen.Bondi.InitialSize
public import Christodoulou.Frozen.Bondi.InitialBound
public import Christodoulou.Frozen.Bondi.MemXPrimeBall
public import Christodoulou.Frozen.Bondi.TranslatedDataField
import Christodoulou.Bondi.IterationBounds
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Characterizations and translation helpers for X′

The finite initial-data supremum characterizes its bounds. The X′ sum bound implies
the X bound, and translation of C¹ data preserves its radial derivative on the strip.
-/

public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi
namespace XPB

/-- The exact initial size is nonnegative and characterizes all initial bounds. -/
theorem initialSize_characterization (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data) :
    0 ≤ initialSize data hdata ∧ ∀ d : ℝ,
      InitialBound data d ↔ initialSize data hdata ≤ d := by
  obtain ⟨d, hd, hlub⟩ := XIt.isDecaySlice_exists_data_bound data hdata
  have heq : initialSize data hdata = d := hlub.csSup_eq (range_nonempty _)
  rw [heq]
  refine ⟨hd, fun b => ⟨fun hb => hlub.2 ?_, fun hb r => (hlub.1 ?_).trans hb⟩⟩
  · rintro _ ⟨r, rfl⟩
    exact hb r
  · exact mem_range_self r

/-- The weighted sum bound makes the unweighted sum bound redundant. -/
theorem memXPrimeBall_iff (T : ℝ≥0) (x : ℝ) (H : C(ℝ≥0 × ℝ≥0, ℝ)) :
    MemXPrimeBall T x H ↔
      (∀ u : ℝ≥0, u ≤ T → ContDiffOn ℝ 1
        (fun z : ℝ => H (u, z.toNNReal)) (Ici 0)) ∧
      ContinuousOn (fun p : ℝ × ℝ => derivWithin
        (fun z : ℝ => H (p.1.toNNReal, z.toNNReal)) (Ici 0) p.2)
        (Icc 0 (T : ℝ) ×ˢ Ici 0) ∧
      ∀ u : ℝ≥0, u ≤ T → ∀ r : ℝ≥0,
        primeWeight u r ^ 3 * |H (u, r)| +
          primeWeight u r ^ 4 * |radialDerivative H u r| ≤ x := by
  constructor
  · intro hH
    exact ⟨hH.1.1, hH.1.2.1, hH.2⟩
  · rintro ⟨hC, hD, hbound⟩
    refine ⟨⟨hC, hD, ?_⟩, hbound⟩
    intro u hu r
    have hw : 1 + (r : ℝ) ≤ primeWeight u r := by
      dsimp only [primeWeight]
      exact le_add_of_nonneg_right (div_nonneg u.coe_nonneg (by norm_num))
    exact (add_le_add
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) hw 3) (abs_nonneg _))
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) hw 4) (abs_nonneg _))).trans (hbound u hu r)

/-- The translated seed agrees with the unclamped formula on the strip. -/
theorem translatedDataField_apply (T : ℝ≥0) (data : C(ℝ≥0, ℝ))
    (u r : ℝ≥0) (hu : u ≤ T) :
    translatedDataField T data (u, r) = data (r + u / 2) := by
  change data (r + min u T / 2) = data (r + u / 2)
  rw [min_eq_left hu]

/-- The translated seed agrees with real translation at nonnegative radii. -/
lemma translatedDataField_real_apply (T : ℝ≥0) (data : C(ℝ≥0, ℝ))
    (u : ℝ≥0) (hu : u ≤ T) (z : ℝ) (hz : 0 ≤ z) :
    translatedDataField T data (u, z.toNNReal) = data (z + (u : ℝ) / 2).toNNReal := by
  rw [translatedDataField_apply T data u z.toNNReal hu]
  congr 1
  apply NNReal.coe_injective
  have hzshift : 0 ≤ z + (u : ℝ) / 2 :=
    add_nonneg hz (div_nonneg u.coe_nonneg (by norm_num))
  simp only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_ofNat,
    Real.coe_toNNReal z hz, Real.coe_toNNReal (z + (u : ℝ) / 2) hzshift]

/-- The radial derivative of the translated seed is the translated data derivative. -/
lemma translatedDataField_derivWithin (T : ℝ≥0) (data : C(ℝ≥0, ℝ))
    (hdata : IsDecaySlice data) (u : ℝ≥0) (hu : u ≤ T) (z : ℝ) (hz : 0 ≤ z) :
    derivWithin (fun s : ℝ => translatedDataField T data (u, s.toNNReal)) (Ici 0) z =
      derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) (z + (u : ℝ) / 2) := by
  have hshift : MapsTo (fun s : ℝ => s + (u : ℝ) / 2) (Ici 0) (Ici 0) :=
    fun s hs => add_nonneg hs (div_nonneg u.coe_nonneg (by norm_num))
  have hd := (hdata.1.1.differentiableOn one_ne_zero _ (hshift hz)).hasDerivWithinAt
  have hcomp := hd.comp z ((hasDerivAt_id z).add_const ((u : ℝ) / 2)).hasDerivWithinAt
    hshift
  have hseed : HasDerivWithinAt
      (fun s : ℝ => translatedDataField T data (u, s.toNNReal))
      (derivWithin (fun s : ℝ => data s.toNNReal) (Ici 0) (z + (u : ℝ) / 2))
      (Ici 0) z := by
    simpa only [Function.comp_def, mul_one] using hcomp.congr_of_mem
      (fun s hs => translatedDataField_real_apply T data u hu s hs) hz
  exact hseed.derivWithin (uniqueDiffOn_Ici 0 z hz)

end XPB

/-- Enlarging the radius preserves membership in the X′ ball. -/
theorem MemXPrimeBall.mono {T : ℝ≥0} {x y : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXPrimeBall T x H) (hxy : x ≤ y) : MemXPrimeBall T y H := by
  apply (XPB.memXPrimeBall_iff T y H).2
  exact ⟨hH.1.1, hH.1.2.1, fun u hu r => (hH.2 u hu r).trans hxy⟩

/-- An X′ ball lies in the X ball with the same radius. -/
theorem MemXPrimeBall.toMemXBall {T : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXPrimeBall T x H) : MemXBall T x H := hH.1

/-- Restricting the time strip preserves membership in the X′ ball. -/
theorem MemXPrimeBall.of_le {T T' : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXPrimeBall T x H) (hT : T' ≤ T) : MemXPrimeBall T' x H := by
  apply (XPB.memXPrimeBall_iff T' x H).2
  refine ⟨fun u hu => hH.1.1 u (hu.trans hT), hH.1.2.1.mono ?_,
    fun u hu r => hH.2 u (hu.trans hT) r⟩
  intro p hp
  exact ⟨⟨hp.1.1, hp.1.2.trans (show (T' : ℝ) ≤ T from hT)⟩, hp.2⟩

end Christodoulou.Bondi
