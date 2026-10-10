module

public import Christodoulou.Frozen.Bondi.MemXBall
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.TangentCone.Real



public section

open Set
open scoped NNReal

namespace Christodoulou.Bondi


noncomputable def invOnePlusCube : C(ℝ≥0 × ℝ≥0, ℝ) :=
  ⟨fun p => (1 + (p.2 : ℝ)) ^ (-3 : ℤ), by
    exact (continuous_const.add (NNReal.continuous_coe.comp continuous_snd)).zpow₀
      (-3) (fun p => Or.inl (ne_of_gt
        (add_pos_of_pos_of_nonneg zero_lt_one p.2.coe_nonneg)))⟩

private theorem invOnePlusCube_lift (u : ℝ≥0) {s : ℝ} (hs : 0 ≤ s) :
    invOnePlusCube (u, s.toNNReal) = (1 + s) ^ (-3 : ℤ) := by
  change (1 + (s.toNNReal : ℝ)) ^ (-3 : ℤ) = _
  rw [Real.coe_toNNReal s hs]

private theorem derivWithin_invOnePlusCube (u : ℝ≥0) {s : ℝ} (hs : 0 ≤ s) :
    derivWithin (fun t : ℝ => invOnePlusCube (u, t.toNNReal)) (Ici 0) s =
      -3 * (1 + s) ^ (-4 : ℤ) := by
  have hne : 1 + s ≠ 0 := ne_of_gt (by positivity)
  have hd : HasDerivAt (fun t : ℝ => (1 + t) ^ (-3 : ℤ))
      (-3 * (1 + s) ^ (-4 : ℤ)) s := by
    simpa [Function.comp_def] using (hasDerivAt_zpow (-3) (1 + s) (Or.inl hne)).comp s
      ((hasDerivAt_id s).const_add 1)
  exact (hd.hasDerivWithinAt.congr_of_mem
    (fun t ht => invOnePlusCube_lift u ht) hs).derivWithin (uniqueDiffOn_Ici 0 s hs)

/-- `H(u, r) = (1 + r)⁻³` lies in the closed `X`-ball of radius `4` on every strip: the `H`-term
`(1 + r)³ (1 + r)⁻³ = 1` and the derivative term `(1 + r)⁴ · 3 (1 + r)⁻⁴ = 3`. -/
theorem memXBall_invOnePlusCube (u₀ : ℝ≥0) : MemXBall u₀ 4 invOnePlusCube := by
  refine ⟨?_, ?_, ?_⟩
  · intro u _
    have hc : ContDiffOn ℝ 1 (fun s : ℝ => (1 + s) ^ (-3 : ℤ)) (Ioi (-1)) := by
      simp only [zpow_neg]
      apply ((contDiffOn_const.add contDiffOn_id).pow 3).inv
      intro s hs
      have hs' : -1 < s := hs
      exact pow_ne_zero 3 (ne_of_gt (by change 0 < 1 + s; linarith only [hs']))
    have hsub : Ici (0 : ℝ) ⊆ Ioi (-1) := by
      intro s hs
      exact lt_of_lt_of_le (by norm_num) hs
    exact (hc.mono hsub).congr
      (fun s hs => invOnePlusCube_lift u hs)
  · have hc : ContinuousOn (fun p : ℝ × ℝ => -3 * (1 + p.2) ^ (-4 : ℤ))
        (Icc 0 (u₀ : ℝ) ×ˢ Ici 0) := by
      apply continuousOn_const.mul
      apply (continuous_const.add continuous_snd).continuousOn.zpow₀
      intro p hp
      exact Or.inl (ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one hp.2))
    exact hc.congr (fun p hp => derivWithin_invOnePlusCube p.1.toNNReal hp.2)
  · intro u _ r
    rw [derivWithin_invOnePlusCube u r.coe_nonneg]
    change (1 + (r : ℝ)) ^ 3 * |(1 + (r : ℝ)) ^ (-3 : ℤ)| +
      (1 + (r : ℝ)) ^ 4 * |-3 * (1 + (r : ℝ)) ^ (-4 : ℤ)| ≤ 4
    have hpos : 0 < 1 + (r : ℝ) := by positivity
    rw [abs_mul, abs_of_pos (zpow_pos hpos (-3)), abs_of_pos (zpow_pos hpos (-4))]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), zpow_neg]
    field_simp
    nlinarith only [hpos]

end Christodoulou.Bondi
