module
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
import Christodoulou.Frozen.Bondi.LinearStepMapApply
import Christodoulou.Frozen.Bondi.LinearStepClassical
import Christodoulou.Frozen.Bondi.HasDerivWithinAtLinearStep
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi
open Christodoulou.Radial

namespace XFix

private theorem abs_le_of_memXBall {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H)
    (u : ℝ≥0) (hu : u ≤ u₀) (r : ℝ≥0) :
    |H (u, r)| ≤ x * (1 + (r : ℝ)) ^ (-3 : ℤ) := by
  have hb := hH.2.2 u hu r
  have hw : 0 < (1 + (r : ℝ)) ^ 3 := by positivity
  have hle : (1 + (r : ℝ)) ^ 3 * |H (u, r)| ≤ x :=
    (le_add_of_nonneg_right (by positivity)).trans hb
  rw [zpow_neg, zpow_ofNat, ← div_eq_mul_inv]
  exact (le_div_iff₀ hw).2 (by simpa only [mul_comm] using hle)

private theorem isClassicalSolution_of_linearStepMap_eq_of_pos {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H) (hu₀ : 0 < u₀)
    (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data s.toNNReal) (Ici 0))
    (hfix : linearStepMap hH data = H) :
    IsClassicalSolution u₀ H := by
  have hval (u r : ℝ≥0) : linearStep hH data u r = H (u, r) := by
    rw [← linearStepMap_apply, hfix]
  obtain ⟨htime, _, hc1⟩ := linearStep_classical hH hu₀ data hdata
  refine ⟨?_, ⟨x, abs_le_of_memXBall hH⟩, ?_⟩
  · simpa only [hval] using hc1
  · intro u hu huT hs r hr
    have huR : (0 : ℝ) < u := hu
    have huTR : (u : ℝ) < u₀ := huT
    have hrR : (0 : ℝ) < r := hr
    have ht := (htime u huT.le r).hasDerivAt (Icc_mem_nhds huR huTR)
    have hq := (hasDerivWithinAt_linearStep hH data hdata u r).hasDerivAt
      (Ici_mem_nhds hrR)
    simp only [hval] at ht hq
    rw [ht.deriv, hq.deriv]
    have hgb : gBarX hH u r = gBar (H.curry u) hs r := by
      simp only [gBarX, min_eq_left huT.le]
    have hg : gX hH u r = g (H.curry u) hs r := by
      simp only [gX, min_eq_left huT.le]
    have hm : hBarX u₀ H u r = mean (H.curry u) r := by
      simp only [hBarX, min_eq_left huT.le]
    simp only [linearSource, linearCoeff, derivGBarX, ite_eq_right (ne_of_gt hr),
      hgb, hg, hm]
    ring

private theorem isClassicalSolution_zero_of_memXBall {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall 0 x H) :
    IsClassicalSolution 0 H := by
  refine ⟨?_, ⟨x, abs_le_of_memXBall hH⟩, ?_⟩
  · have hslice := hH.1 0 le_rfl
    have hcomp : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => H (0, p.2.toNNReal))
        (Icc 0 (0 : ℝ) ×ˢ Ici 0) :=
      hslice.comp contDiffOn_snd (fun p hp => hp.2)
    apply hcomp.congr
    intro p hp
    have hp0 : p.1 = 0 := le_antisymm hp.1.2 hp.1.1
    simp only [hp0, Real.toNNReal_zero]
  · intro u _ hu
    exact (not_lt_of_ge (bot_le : (0 : ℝ≥0) ≤ u) hu).elim


theorem isClassicalSolution_of_linearStepMap_eq {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hH : MemXBall u₀ x H)
    (data : C(ℝ≥0, ℝ))
    (hdata : ContDiffOn ℝ 1 (fun s : ℝ => data s.toNNReal) (Ici 0))
    (hfix : linearStepMap hH data = H) :
    IsClassicalSolution u₀ H := by
  rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0) ≤ u₀) with hzero | hpos
  · subst u₀
    exact isClassicalSolution_zero_of_memXBall hH
  · exact isClassicalSolution_of_linearStepMap_eq_of_pos hH hpos data hdata hfix

end XFix

end Christodoulou.Bondi
