module
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.IsCharacteristic
public import Christodoulou.Frozen.Bondi.LinearSource
import Christodoulou.Frozen.Bondi.IsCharacteristicStrictAntiOn
import Christodoulou.Frozen.Bondi.CoefficientYLipschitz
import Christodoulou.Bondi.LinearStepBasic
import Christodoulou.Bondi.LinearODE
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Shared helpers for Theorem 2

Generic calculus, slice-local coefficient estimates, and Picard iteration used in the
reconstruction of Theorem 2. These helpers consume the preceding analytic results.
-/

public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi
namespace XT2H

/-- Extend an interior derivative to the closed interval by the fundamental theorem of calculus. -/
theorem closed_derivative {T : ℝ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt f (g t) t) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt f (g t) (Icc 0 T) t := by
  have he (v : ℝ) (hv : v ∈ Icc 0 T) :
      f v = f 0 + ∫ s in (0 : ℝ)..v, g s := by
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hv.1
      (hf.mono (Icc_subset_Icc_right hv.2))
      (fun s hs => hd s ⟨hs.1, hs.2.trans_le hv.2⟩)
      ((hg.mono (Icc_subset_Icc_right hv.2)).intervalIntegrable_of_Icc hv.1)
    linarith only [hi]
  exact ((LinODE.primitive_deriv hg ht).const_add (f 0)).congr he (he t ht)

/-- Every time slice of a classical solution on the strip is continuously differentiable. -/
theorem classical_slice {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H) (u : ℝ≥0) (hu : u ≤ u₀) :
    ContDiffOn ℝ 1 (fun s : ℝ => H (u, s.toNNReal)) (Ici 0) := by
  simpa only [Function.comp_def, id_eq, Real.toNNReal_coe] using hH.1.comp
    (contDiffOn_const.prodMk contDiffOn_id)
    (fun s hs => (show ((u : ℝ), s) ∈ Icc 0 (u₀ : ℝ) ×ˢ Ici 0 from
      ⟨⟨u.coe_nonneg, hu⟩, hs⟩))

/-- The radial derivative of a classical solution is continuous on the closed strip. -/
theorem classical_radial_continuous {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H) :
    ContinuousOn (fun p : ℝ × ℝ => derivWithin
      (fun s : ℝ => H (p.1.toNNReal, s.toNNReal)) (Ici 0) p.2)
      (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) := by
  rcases eq_or_lt_of_le u₀.coe_nonneg with hz | hpos
  · have hu0 : u₀ = 0 := NNReal.coe_eq_zero.mp hz.symm
    subst u₀
    have hc : ContinuousOn (fun p : ℝ × ℝ => derivWithin
        (fun s : ℝ => H (0, s.toNNReal)) (Ici 0) p.2) (Icc 0 (0 : ℝ) ×ˢ Ici 0) :=
      ((classical_slice hH 0 le_rfl).continuousOn_derivWithin
      (uniqueDiffOn_Ici 0) le_rfl).comp continuousOn_snd (fun p hp => hp.2)
    apply hc.congr
    intro p hp
    have hp0 : p.1 = 0 := le_antisymm hp.1.2 hp.1.1
    simp only [hp0, Real.toNNReal_zero]
  · let S : Set (ℝ × ℝ) := Icc 0 (u₀ : ℝ) ×ˢ Ici 0
    let F : ℝ × ℝ → ℝ := fun p => H (p.1.toNNReal, p.2.toNNReal)
    have hc : ContinuousOn (fun p => (fderivWithin ℝ F S p) (0, 1)) S :=
      (hH.1.continuousOn_fderivWithin
        ((uniqueDiffOn_Icc hpos).prod (uniqueDiffOn_Ici 0)) le_rfl).clm_apply continuousOn_const
    apply hc.congr
    intro p hp
    have hd := (hH.1.differentiableOn one_ne_zero p hp).hasFDerivWithinAt
    have hr : HasDerivWithinAt (fun s : ℝ => F (p.1, s))
        ((fderivWithin ℝ F S p) (0, 1)) (Ici 0) p.2 :=
      by simpa only [Function.comp_def, id_eq] using
        hd.comp_hasDerivWithinAt (t := S) p.2
          ((hasDerivWithinAt_const p.2 (Ici 0) p.1).prodMk (hasDerivWithinAt_id p.2 (Ici 0)))
          (fun s hs => ⟨hp.1, hs⟩)
    exact hr.derivWithin (uniqueDiffOn_Ici 0 p.2 hp.2)

/-- A classical solution satisfies the linear equation along each closed characteristic. -/
theorem classical_characteristic_derivative {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H)
    (hclass : IsClassicalSolution u₀ H) {v : Icc (0 : ℝ) u₀} {r : ℝ≥0}
    {χ : ℝ → ℝ} (hχ : IsCharacteristic hH v r χ) {t : ℝ}
    (ht : t ∈ Icc 0 (v : ℝ)) :
    HasDerivWithinAt (fun s : ℝ => H (s.toNNReal, (χ s).toNNReal))
      (linearCoeff hH t.toNNReal (χ t).toNNReal * H (t.toNNReal, (χ t).toNNReal) +
        linearSource hH t.toNNReal (χ t).toNNReal) (Icc 0 (v : ℝ)) t := by
  have hcχ := HasDerivWithinAt.continuousOn hχ.2
  have hcH : ContinuousOn (fun s : ℝ => H (s.toNNReal, (χ s).toNNReal))
      (Icc 0 (v : ℝ)) := H.continuous.comp_continuousOn
        (continuous_real_toNNReal.continuousOn.prodMk
          (continuous_real_toNNReal.comp_continuousOn hcχ))
  apply closed_derivative hcH
    (((XStep.continuousOn_linearCoeff hχ).mul hcH).add (XStep.continuousOn_linearSource hχ)) _ ht
  intro s hs
  have hsT : s < (u₀ : ℝ) := hs.2.trans_le v.2.2
  have hsχ : 0 < χ s := by
    have hlt := hχ.strictAntiOn ⟨hs.1.le, hs.2.le⟩ ⟨v.2.1, le_rfl⟩ hs.2
    rw [hχ.1] at hlt
    exact r.coe_nonneg.trans_lt hlt
  let F : ℝ × ℝ → ℝ := fun p => H (p.1.toNNReal, p.2.toNNReal)
  have hmem : Icc 0 (u₀ : ℝ) ×ˢ Ici 0 ∈ 𝓝 (s, χ s) :=
    prod_mem_nhds (Icc_mem_nhds hs.1 hsT) (Ici_mem_nhds hsχ)
  have hfd : HasFDerivAt F (fderiv ℝ F (s, χ s)) (s, χ s) :=
    ((hclass.1.differentiableOn one_ne_zero (s, χ s)
    ⟨⟨hs.1.le, hsT.le⟩, hsχ.le⟩).differentiableAt hmem).hasFDerivAt
  let L := fderiv ℝ F (s, χ s)
  have hfst : HasDerivAt (fun z => F (z, χ s)) (L (1, 0)) s :=
    by simpa only [Function.comp_def, id_eq] using
      hfd.comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hasDerivAt_const s (χ s)))
  have hsnd : HasDerivAt (fun z => F (s, z)) (L (0, 1)) (χ s) :=
    hfd.comp_hasDerivAt (χ s) ((hasDerivAt_const (χ s) s).prodMk (hasDerivAt_id (χ s)))
  have hcurve := hfd.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk ((hχ.2 s ⟨hs.1.le, hs.2.le⟩).hasDerivAt
      (Icc_mem_nhds hs.1 hs.2)))
  have hu : s.toNNReal < u₀ := by exact_mod_cast (show (s.toNNReal : ℝ) < u₀ by
    rw [Real.coe_toNNReal _ hs.1.le]; exact hsT)
  have hpde := hclass.2.2 s.toNNReal (Real.toNNReal_pos.mpr hs.1) hu
    (hH.isSlice _ hu.le) (χ s).toNNReal (Real.toNNReal_pos.mpr hsχ)
  simp only [Real.coe_toNNReal _ hs.1.le, Real.coe_toNNReal _ hsχ.le] at hpde
  change deriv (fun z => F (z, χ s)) s -
    1 / 2 * gBar (H.curry s.toNNReal) (hH.isSlice _ hu.le) (χ s).toNNReal *
      deriv (fun z => F (s, z)) (χ s) = _ at hpde
  rw [hfst.deriv, hsnd.deriv] at hpde
  have he : L (1, charField hH s (χ s)) =
      linearCoeff hH s.toNNReal (χ s).toNNReal * H (s.toNNReal, (χ s).toNNReal) +
        linearSource hH s.toNNReal (χ s).toNNReal := by
    have hev : (1, charField hH s (χ s)) = ((1, 0) : ℝ × ℝ) +
        charField hH s (χ s) • ((0, 1) : ℝ × ℝ) := by ext <;> simp
    rw [hev, map_add, map_smul, smul_eq_mul]
    simp only [charField, linearCoeff, linearSource, derivGBarX,
      ite_eq_right (ne_of_gt (Real.toNNReal_pos.mpr hsχ)), gX, gBarX, hBarX,
      min_eq_left hu.le, Real.coe_toNNReal _ hsχ.le]
    linear_combination hpde
  change HasDerivAt (fun z => H (z.toNNReal, (χ z).toNNReal))
    (L (1, charField hH s (χ s))) s at hcurve
  rw [he] at hcurve
  exact hcurve

/-- The field constant in time with radial profile equal to the slice at `u`. -/
@[expose] noncomputable def sliceField (H : C(ℝ≥0 × ℝ≥0, ℝ)) (u : ℝ≥0) : C(ℝ≥0 × ℝ≥0, ℝ) :=
  ⟨fun p => H (u, p.2), H.continuous.comp (continuous_const.prodMk continuous_snd)⟩

/-- Every time slice of `sliceField H u` equals the slice of `H` at `u`. -/
theorem sliceField_curry (H : C(ℝ≥0 × ℝ≥0, ℝ)) (u t : ℝ≥0) :
    (sliceField H u).curry t = H.curry u := by
  ext r
  rfl

/-- A time slice of an X-ball field defines a constant field in a zero-width X-ball. -/
theorem sliceField_memXBall {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (u : ℝ≥0) (hu : u ≤ u₀) :
    MemXBall 0 x (sliceField H u) := by
  refine ⟨fun _ _ => hH.1 u hu, ?_, fun _ _ r => hH.2.2 u hu r⟩
  exact ((hH.1 u hu).continuousOn_derivWithin (uniqueDiffOn_Ici 0) le_rfl).comp
    continuousOn_snd (fun p hp => hp.2)

/-- Localize the frozen coefficient Lipschitz bounds to one time slice. -/
theorem coefficient_slice_lipschitz {u₀ : ℝ≥0} {x : ℝ}
    {H K : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (hK : MemXBall u₀ x K)
    (u : ℝ≥0) (hu : u ≤ u₀) {y : ℝ}
    (hy : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |H (u, r) - K (u, r)| ≤ y) (r : ℝ≥0) :
    |gBarX hH u r - gBarX hK u r| ≤ 4 * π * x * y / (1 + (r : ℝ)) ∧
    |derivGBarX hH u r - derivGBarX hK u r| ≤
      2 * π * x * (2 + π * x ^ 2) * y / (1 + (r : ℝ)) ^ 2 ∧
    |linearSource hH u r - linearSource hK u r| ≤
      π * x ^ 2 * (13 / 6 + π * x ^ 2) * y / (1 + (r : ℝ)) ^ 3 := by
  have hc := coefficient_y_lipschitz (sliceField_memXBall hH u hu)
    (sliceField_memXBall hK u hu) (fun _ _ r => hy r) 0 r
  have he := hc.2.2
  simpa only [gBarX, gX, derivGBarX, linearSource, linearCoeff, hBarX,
    min_eq_left hu, sliceField_curry] using he

/-- Bound the difference-equation remainder by the weighted field difference. -/
theorem remainder_bound {u₀ : ℝ≥0} {x : ℝ}
    {H K : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (hK : MemXBall u₀ x K)
    (u : ℝ≥0) (hu : u ≤ u₀) {y : ℝ} (hy0 : 0 ≤ y)
    (hy : ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |H (u, r) - K (u, r)| ≤ y)
    (r : ℝ≥0) :
    |(gBarX hH u r - gBarX hK u r) / 2 *
        derivWithin (fun s : ℝ => K (u, s.toNNReal)) (Ici 0) r +
      (linearCoeff hH u r - linearCoeff hK u r) * K (u, r) +
      linearSource hH u r - linearSource hK u r| ≤
      (π * x ^ 2 * (37 / 6 + 2 * π * x ^ 2)) * y / (1 + (r : ℝ)) ^ 3 := by
  let w := 1 + (r : ℝ)
  let S := K (u, r)
  let q := derivWithin (fun s : ℝ => K (u, s.toNNReal)) (Ici 0) r
  have hw : 0 < w := by dsimp [w]; positivity
  have hw1 : 1 ≤ w := by dsimp [w]; linarith only [r.coe_nonneg]
  have hbudget := hK.2.2 u hu r
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
  obtain ⟨hg, ha, hf⟩ := coefficient_slice_lipschitz hH hK u hu hy r
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

/-- Continuous majorants and Picard iteration force a bounded nonnegative function to vanish. -/
theorem majorant_picard_zero {T : ℝ≥0} {F : ℝ≥0 → ℝ≥0 → ℝ} {M K : ℝ}
    (hF : ∀ v : ℝ≥0, v ≤ T → ∀ r, 0 ≤ F v r)
    (hbound : ∀ v : ℝ≥0, v ≤ T → ∀ r, F v r ≤ M)
    (hstep : ∀ (v : ℝ≥0), v ≤ T → ∀ φ : ℝ → ℝ, ContinuousOn φ (Icc 0 (v : ℝ)) →
      (∀ s : ℝ≥0, s ≤ v → ∀ r, F s r ≤ φ s) →
      ∀ r, F v r ≤ K * ∫ s in (0 : ℝ)..(v : ℝ), φ s) :
    ∀ v : ℝ≥0, v ≤ T → ∀ r, F v r = 0 := by
  have hiter : ∀ n : ℕ, ∀ v : ℝ≥0, v ≤ T → ∀ r,
      F v r ≤ M * (K * (v : ℝ)) ^ n / (n.factorial : ℝ) := by
    intro n
    induction n with
    | zero => simpa only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one] using hbound
    | succ n ih =>
      intro v hv r
      have hi := hstep v hv (fun s : ℝ => M * K ^ n / (n.factorial : ℝ) * s ^ n)
        (by fun_prop) (fun s hs r => by
          have hb := ih s (hs.trans hv) r
          convert hb using 1; ring) r
      rw [intervalIntegral.integral_const_mul, integral_pow] at hi
      have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
      convert hi using 1
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        zero_pow (Nat.succ_ne_zero n), sub_zero]
      field_simp
      ring
  intro v hv r
  have ht := (FloorSemiring.tendsto_pow_div_factorial_atTop (K * (v : ℝ))).const_mul M
  have hzero : F v r ≤ 0 := by
    apply ge_of_tendsto (by simpa only [mul_zero] using ht)
    exact Filter.Eventually.of_forall (fun n => by simpa only [mul_div_assoc] using hiter n v hv r)
  exact le_antisymm hzero (hF v hv r)

/-- Membership in an X-ball is monotone in its radius. -/
theorem memXBall_mono_radius {u₀ : ℝ≥0} {x y : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (hxy : x ≤ y) : MemXBall u₀ y H :=
  ⟨hH.1, hH.2.1, fun u hu r => (hH.2.2 u hu r).trans hxy⟩

end XT2H
end Christodoulou.Bondi
