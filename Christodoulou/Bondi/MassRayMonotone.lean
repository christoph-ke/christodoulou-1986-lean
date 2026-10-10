module
public import Christodoulou.Frozen.Bondi.HasDerivAtMassCharacteristic
public import Christodoulou.Frozen.Bondi.MemXBallIsSlice
public import Christodoulou.Frozen.Bondi.ContinuousGBarX
public import Christodoulou.Frozen.Bondi.GBarXOfLe
public import Christodoulou.Frozen.Bondi.GXOfLe
public import Christodoulou.Frozen.Bondi.GPos
public import Christodoulou.Frozen.Bondi.BondiMassSpec
public import Christodoulou.Bondi.XBallContinuity
public import Christodoulou.Bondi.GBarBasic
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Mass is nonincreasing along incoming light rays

Joint continuity of mass on the closed physical strip gives continuity along each backward
characteristic, including its endpoints and the centre. The sealed characteristic derivative
is nonpositive at interior times, so mass is antitone on the whole characteristic interval.
The terminal mass is therefore bounded by its initial value and the initial Bondi mass.
-/

public section

open Set Real
open scoped NNReal

namespace Christodoulou.Bondi

namespace XMR

/-- Joint continuity of mass on the closed physical strip, including the centre. -/
theorem continuousOn_mass_strip {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hX : MemXBall u₀ x H) (hs : ∀ v : ℝ≥0, IsSlice (H.curry v)) :
    ContinuousOn (fun p : ℝ≥0 × ℝ≥0 => mass (H.curry p.1) (hs p.1) p.2)
      (Iic u₀ ×ˢ (univ : Set ℝ≥0)) := by
  have hn (p : ℝ≥0 × ℝ≥0) : gX hX p.1 p.2 ≠ 0 :=
    (g_pos (H.curry (min p.1 u₀))
      (hX.isSlice (min p.1 u₀) (min_le_right _ _)) p.2).ne'
  have hr : Continuous (fun p : ℝ≥0 × ℝ≥0 => (p.2 : ℝ) / 2) := by fun_prop
  have hc := hr.mul ((continuous_const (y := (1 : ℝ))).sub
    ((continuous_gBarX hX).div (continuous_gX hX) hn))
  apply hc.continuousOn.congr
  intro p hp
  change mass (H.curry p.1) (hs p.1) p.2 =
    (p.2 : ℝ) / 2 * (1 - gBarX hX p.1 p.2 / gX hX p.1 p.2)
  rw [gBarX_of_le hX hp.1 (hs p.1), gX_of_le hX hp.1 (hs p.1)]
  rfl

/-- Continuity of mass along a characteristic on its whole closed time interval. -/
theorem continuousOn_mass_characteristic {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hX : MemXBall u₀ x H)
    (hs : ∀ v : ℝ≥0, IsSlice (H.curry v)) {u₁ : Icc (0 : ℝ) u₀}
    {r₁ : ℝ≥0} {χ : ℝ → ℝ} (hχ : IsCharacteristic hX u₁ r₁ χ) :
    ContinuousOn (fun s : ℝ => mass (H.curry (Real.toNNReal s)) (hs (Real.toNNReal s))
      (Real.toNNReal (χ s))) (Icc 0 (u₁ : ℝ)) := by
  have hcχ : ContinuousOn χ (Icc 0 (u₁ : ℝ)) :=
    fun t ht => (hχ.2 t ht).continuousWithinAt
  have hp : ContinuousOn (fun s : ℝ => (Real.toNNReal s, Real.toNNReal (χ s)))
      (Icc 0 (u₁ : ℝ)) :=
    continuous_real_toNNReal.continuousOn.prodMk
      (continuous_real_toNNReal.comp_continuousOn hcχ)
  exact (continuousOn_mass_strip hX hs).comp hp (fun t ht =>
    ⟨Real.toNNReal_le_iff_le_coe.mpr (ht.2.trans u₁.property.2), mem_univ _⟩)

/-- Derivative comparison on the closed characteristic interval. -/
theorem antitoneOn_mass_characteristic_of_hasDerivAt {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} (hX : MemXBall u₀ x H)
    (hs : ∀ v : ℝ≥0, IsSlice (H.curry v)) {u₁ : Icc (0 : ℝ) u₀}
    {r₁ : ℝ≥0} {χ : ℝ → ℝ} (hχ : IsCharacteristic hX u₁ r₁ χ)
    (hd : ∀ t : ℝ, 0 < t → t < u₁ →
      HasDerivAt (fun s : ℝ => mass (H.curry (Real.toNNReal s)) (hs (Real.toNNReal s))
          (Real.toNNReal (χ s)))
        (-(π / g (H.curry (Real.toNNReal t)) (hs (Real.toNNReal t))
          (Real.toNNReal (χ t))) * xi (H.curry (Real.toNNReal t))
          (hs (Real.toNNReal t)) (Real.toNNReal (χ t)) ^ 2) t) :
    AntitoneOn (fun s : ℝ => mass (H.curry (Real.toNNReal s)) (hs (Real.toNNReal s))
        (Real.toNNReal (χ s))) (Icc 0 (u₁ : ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 (u₁ : ℝ))
    (continuousOn_mass_characteristic hX hs hχ)
  · intro t ht
    rw [interior_Icc] at ht
    exact (hd t ht.1 ht.2).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(hd t ht.1 ht.2).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (div_nonneg pi_pos.le (g_pos _ _ _).le)) (sq_nonneg _)

/-- Mass is nonincreasing along an incoming light ray, including both time endpoints. -/
theorem antitoneOn_mass_characteristic {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H) (hX : MemXBall u₀ x H)
    (hs : ∀ v : ℝ≥0, IsSlice (H.curry v)) {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hX u₁ r₁ χ) :
    AntitoneOn (fun s : ℝ => mass (H.curry (Real.toNNReal s)) (hs (Real.toNNReal s))
        (Real.toNNReal (χ s))) (Icc 0 (u₁ : ℝ)) := by
  exact antitoneOn_mass_characteristic_of_hasDerivAt hX hs hχ
    (fun t ht htu =>
      Christodoulou.Bondi.hasDerivAt_mass_characteristic hH hX hs hχ ht htu)

/-- Endpoint and Bondi-mass bounds from characteristic monotonicity. -/
theorem mass_terminal_le_initial_le_bondiMass
    {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hX : MemXBall u₀ x H) (hs : ∀ v : ℝ≥0, IsSlice (H.curry v))
    {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hX u₁ r₁ χ)
    (hmono : AntitoneOn (fun s : ℝ =>
      mass (H.curry (Real.toNNReal s)) (hs (Real.toNNReal s))
        (Real.toNNReal (χ s))) (Icc 0 (u₁ : ℝ))) :
    mass (H.curry (Real.toNNReal (u₁ : ℝ))) (hs (Real.toNNReal (u₁ : ℝ))) r₁ ≤
      mass (H.curry 0) (hs 0) (Real.toNNReal (χ 0)) ∧
    mass (H.curry 0) (hs 0) (Real.toNNReal (χ 0)) ≤
      bondiMass (H.curry 0) (hs 0) := by
  constructor
  · have hm := hmono ⟨le_rfl, u₁.2.1⟩ ⟨u₁.2.1, le_rfl⟩ u₁.2.1
    simpa only [hχ.1, Real.toNNReal_coe, Real.toNNReal_zero] using hm
  · exact le_csSup (bondiMass_spec (H.curry 0) (hs 0)).1 ⟨_, rfl⟩

/-- The endpoint and Bondi-mass corollary for a classical solution. -/
theorem mass_terminal_le_initial_le_bondiMass_of_classicalSolution
    {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H) (hX : MemXBall u₀ x H)
    (hs : ∀ v : ℝ≥0, IsSlice (H.curry v))
    {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hX u₁ r₁ χ) :
    mass (H.curry (Real.toNNReal (u₁ : ℝ))) (hs (Real.toNNReal (u₁ : ℝ))) r₁ ≤
      mass (H.curry 0) (hs 0) (Real.toNNReal (χ 0)) ∧
    mass (H.curry 0) (hs 0) (Real.toNNReal (χ 0)) ≤
      bondiMass (H.curry 0) (hs 0) := by
  exact mass_terminal_le_initial_le_bondiMass hX hs hχ
    (antitoneOn_mass_characteristic hH hX hs hχ)

end XMR

end Christodoulou.Bondi
