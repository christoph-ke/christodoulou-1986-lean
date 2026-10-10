module
public import Christodoulou.Frozen.Bondi.IsIncomingRay
public import Christodoulou.Frozen.Bondi.ReflectedRay
public import Christodoulou.Frozen.Bondi.IsClassicalSolution
public import Christodoulou.Frozen.Bondi.IsClassicalSolutionIsSlice
public import Christodoulou.Frozen.Bondi.MemXBall
public import Christodoulou.Frozen.Bondi.CharField
public import Christodoulou.Frozen.Bondi.GBarX
public import Christodoulou.Frozen.Bondi.GBarXPos
public import Christodoulou.Frozen.Bondi.LipschitzWithGBarX
public import Christodoulou.Frozen.Bondi.IsPicardLindelofCharField
public import Christodoulou.Frozen.Bondi.IsCharacteristic
public import Christodoulou.Frozen.Bondi.AntitoneOnMassCharacteristic
public import Christodoulou.Frozen.Bondi.Mass
public import Christodoulou.Frozen.Bondi.MonotoneMass
public import Christodoulou.Bondi.BondiTheorem
public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Incoming rays and mass monotonicity after reflection

Incoming rays start at time zero and stop at the centre or the end of the strip.
A private clamped continuation supplies existence; ODE uniqueness fixes the stopping time.
The time-clamp bridge transfers the sealed characteristic mass theorem to strip slices.
Radial mass monotonicity applies to the outgoing section of the reflected ray.
-/

public section

open Set MeasureTheory Filter Topology Real
open scoped NNReal

namespace Christodoulou.Bondi

open Christodoulou.Radial

namespace XFC

private def IsForwardCharacteristic {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (r₀ : ℝ≥0) (χ : ℝ → ℝ) : Prop :=
  χ 0 = r₀ ∧ ∀ t ∈ Icc (0 : ℝ) u₀, HasDerivWithinAt χ (charField hH t (χ t)) (Icc 0 (u₀ : ℝ)) t

private theorem exists_isForwardCharacteristic {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (r₀ : ℝ≥0) :
    ∃ χ : ℝ → ℝ, IsForwardCharacteristic hH r₀ χ := by
  have hP := isPicardLindelof_charField hH ⟨0, le_rfl, u₀.coe_nonneg⟩ r₀ 0
  obtain ⟨χ, hχ₀, hχ⟩ := hP.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨χ, hχ₀, hχ⟩

private theorem IsForwardCharacteristic.strictAntiOn {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} {hX : MemXBall u₀ x H} {r₀ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsForwardCharacteristic hX r₀ χ) : StrictAntiOn χ (Icc 0 (u₀ : ℝ)) := by
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
    (HasDerivWithinAt.continuousOn hχ.2)
    (fun t ht => (hχ.2 t (interior_subset ht)).mono interior_subset)
  intro t ht
  exact mul_neg_of_neg_of_pos (by norm_num)
    (gBarX_pos hX t.toNNReal (χ t).toNNReal)

private theorem IsForwardCharacteristic.physicalSet_at_zero {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} {hX : MemXBall u₀ x H} {r₀ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsForwardCharacteristic hX r₀ χ) {t : ℝ}
    (ht : t ∈ Icc 0 (u₀ : ℝ)) (hz : χ t = 0) :
    {s : ℝ | s ∈ Icc 0 (u₀ : ℝ) ∧ 0 ≤ χ s} = Icc 0 t := by
  ext s
  constructor
  · intro hs
    refine ⟨hs.1.1, ?_⟩
    by_contra hn
    have hlt := hχ.strictAntiOn ht hs.1 (lt_of_not_ge hn)
    rw [hz] at hlt
    linarith [hs.2]
  · intro hs
    have hsu : s ∈ Icc 0 (u₀ : ℝ) := ⟨hs.1, hs.2.trans ht.2⟩
    exact ⟨hsu, by simpa only [hz] using hχ.strictAntiOn.antitoneOn hsu ht hs.2⟩

private theorem IsForwardCharacteristic.physicalSet_interval {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} {hX : MemXBall u₀ x H} {r₀ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsForwardCharacteristic hX r₀ χ) :
    ∃ t ∈ Icc 0 (u₀ : ℝ),
      {s : ℝ | s ∈ Icc 0 (u₀ : ℝ) ∧ 0 ≤ χ s} = Icc 0 t ∧
      (t < u₀ → χ t = 0) := by
  by_cases hend : 0 ≤ χ u₀
  · refine ⟨u₀, ⟨u₀.coe_nonneg, le_rfl⟩, ?_, by intro h; exact False.elim (lt_irrefl _ h)⟩
    ext s
    constructor
    · exact fun hs => hs.1
    · intro hs
      exact ⟨hs, hend.trans (hχ.strictAntiOn.antitoneOn hs ⟨u₀.coe_nonneg, le_rfl⟩ hs.2)⟩
  · have hzero : 0 ≤ χ 0 := by rw [hχ.1]; exact r₀.coe_nonneg
    obtain ⟨t, ht, hz⟩ := intermediate_value_Icc' u₀.coe_nonneg
      (HasDerivWithinAt.continuousOn hχ.2) ⟨(lt_of_not_ge hend).le, hzero⟩
    exact ⟨t, ht, hχ.physicalSet_at_zero ht hz, fun _ => hz⟩


theorem exists_isIncomingRay {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : MemXBall u₀ x H) (r₀ : ℝ≥0) :
    ∃ u₁ : ℝ, ∃ χ : ℝ → ℝ, IsIncomingRay hH r₀ u₁ χ := by
  obtain ⟨χ, hχ⟩ := exists_isForwardCharacteristic hH r₀
  obtain ⟨t, ht, hphysical, hzero⟩ := hχ.physicalSet_interval
  refine ⟨t, χ, ht, hχ.1, ?_, ?_⟩
  · intro s hs
    have hsp := (show s ∈ {s : ℝ | s ∈ Icc 0 (u₀ : ℝ) ∧ 0 ≤ χ s} from
      hphysical.symm ▸ hs)
    exact ⟨hsp.2, (hχ.2 s hsp.1).mono (Icc_subset_Icc_right ht.2)⟩
  · by_cases he : t = u₀
    · exact Or.inl he
    · exact Or.inr (hzero (lt_of_le_of_ne ht.2 he))

private theorem incoming_strictAntiOn {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} {hH : MemXBall u₀ x H} {r₀ : ℝ≥0}
    {b : ℝ} {χ : ℝ → ℝ} (hχ : IsIncomingRay hH r₀ b χ) :
    StrictAntiOn χ (Icc 0 b) := by
  exact strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
    (HasDerivWithinAt.continuousOn (fun t ht => (hχ.2.2.1 t ht).2))
    (fun t ht => ((hχ.2.2.1 t (interior_subset ht)).2).mono interior_subset)
    (fun t _ => mul_neg_of_neg_of_pos (by norm_num)
      (gBarX_pos hH t.toNNReal (χ t).toNNReal))

private theorem eqOn_initial {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {b : ℝ} {χ₁ χ₂ : ℝ → ℝ}
    (hd₁ : ∀ t ∈ Icc 0 b, HasDerivWithinAt χ₁ (charField hH t (χ₁ t)) (Icc 0 b) t)
    (hd₂ : ∀ t ∈ Icc 0 b, HasDerivWithinAt χ₂ (charField hH t (χ₂ t)) (Icc 0 b) t)
    (hinit : χ₁ 0 = χ₂ 0) : EqOn χ₁ χ₂ (Icc 0 b) := by
  have hLip (t : ℝ) :
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
  exact ODE_solution_unique_of_mem_Icc_right
    (s := fun _ => univ) (fun t _ => (hLip t).lipschitzOnWith)
    (HasDerivWithinAt.continuousOn hd₁)
    (fun t ht => (hd₁ t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)) (fun _ _ => mem_univ _)
    (HasDerivWithinAt.continuousOn hd₂)
    (fun t ht => (hd₂ t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)) (fun _ _ => mem_univ _) hinit

private theorem incoming_eqOn_min {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} {hH : MemXBall u₀ x H} {r₀ : ℝ≥0}
    {u₁ u₂ : ℝ} {χ₁ χ₂ : ℝ → ℝ}
    (h₁ : IsIncomingRay hH r₀ u₁ χ₁) (h₂ : IsIncomingRay hH r₀ u₂ χ₂) :
    EqOn χ₁ χ₂ (Icc 0 (min u₁ u₂)) := by
  apply eqOn_initial
  · intro t ht
    exact ((h₁.2.2.1 t ⟨ht.1, ht.2.trans (min_le_left _ _)⟩).2).mono
      (Icc_subset_Icc_right (min_le_left _ _))
  · intro t ht
    exact ((h₂.2.2.1 t ⟨ht.1, ht.2.trans (min_le_right _ _)⟩).2).mono
      (Icc_subset_Icc_right (min_le_right _ _))
  · exact h₁.2.1.trans h₂.2.1.symm

private theorem incoming_end_not_lt {u₀ : ℝ≥0} {x : ℝ}
    {H : C(ℝ≥0 × ℝ≥0, ℝ)} {hH : MemXBall u₀ x H} {r₀ : ℝ≥0}
    {u₁ u₂ : ℝ} {χ₁ χ₂ : ℝ → ℝ}
    (h₁ : IsIncomingRay hH r₀ u₁ χ₁) (h₂ : IsIncomingRay hH r₀ u₂ χ₂) :
    ¬ u₁ < u₂ := by
  intro hlt
  rcases h₁.2.2.2 with he | hz
  · exact (not_lt_of_ge h₂.1.2) (he ▸ hlt)
  · have heq : χ₁ u₁ = χ₂ u₁ := incoming_eqOn_min h₁ h₂
      ⟨h₁.1.1, by simp [min_eq_left hlt.le]⟩
    have hneg := incoming_strictAntiOn h₂ ⟨h₁.1.1, hlt.le⟩
      ⟨h₂.1.1, le_rfl⟩ hlt
    have hnonneg := (h₂.2.2.1 u₂ ⟨h₂.1.1, le_rfl⟩).1
    rw [← heq, hz] at hneg
    exact (not_lt_of_ge hnonneg) hneg

namespace IsIncomingRay


theorem unique {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {r₀ : ℝ≥0} {u₁ u₂ : ℝ} {χ₁ χ₂ : ℝ → ℝ}
    (h₁ : IsIncomingRay hH r₀ u₁ χ₁) (h₂ : IsIncomingRay hH r₀ u₂ χ₂) :
    u₁ = u₂ ∧ EqOn χ₁ χ₂ (Icc 0 u₁) := by
  have he : u₁ = u₂ := le_antisymm
    (le_of_not_gt (incoming_end_not_lt h₂ h₁))
    (le_of_not_gt (incoming_end_not_lt h₁ h₂))
  refine ⟨he, ?_⟩
  simpa only [he, min_self] using incoming_eqOn_min h₁ h₂

/-- The incoming ray is the (backward) characteristic through each of its points (t, χ(t)). -/
theorem isCharacteristic {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {r₀ : ℝ≥0} {u₁ : ℝ} {χ : ℝ → ℝ} (hχ : IsIncomingRay hH r₀ u₁ χ)
    (t : Icc (0 : ℝ) u₀) (ht : (t : ℝ) ≤ u₁) :
    IsCharacteristic hH t (Real.toNNReal (χ t)) χ := by
  refine ⟨(Real.coe_toNNReal _ (hχ.2.2.1 t ⟨t.2.1, ht⟩).1).symm, ?_⟩
  intro s hs
  exact ((hχ.2.2.1 s ⟨hs.1, hs.2.trans ht⟩).2).mono (Icc_subset_Icc_right ht)

end IsIncomingRay

/-- The time clamp preserves the X-ball. -/
private theorem memXBall_clampExt {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hX : MemXBall u₀ x H) : MemXBall u₀ x (XBT.clampExt u₀ H) := by
  obtain ⟨h1, h2, h3⟩ := hX
  refine ⟨fun u hu => ?_, ?_, fun u hu r => ?_⟩
  · have : (fun s : ℝ => XBT.clampExt u₀ H (u, Real.toNNReal s)) =
        fun s : ℝ => H (u, Real.toNNReal s) := by
      funext s; simp [XBT.clampExt_apply, min_eq_left hu]
    rw [this]; exact h1 u hu
  · refine h2.congr fun p hp => ?_
    have hle : Real.toNNReal p.1 ≤ u₀ := Real.toNNReal_le_iff_le_coe.mpr hp.1.2
    have : (fun s : ℝ => XBT.clampExt u₀ H (Real.toNNReal p.1, Real.toNNReal s)) =
        fun s : ℝ => H (Real.toNNReal p.1, Real.toNNReal s) := by
      funext s; simp [XBT.clampExt_apply, min_eq_left hle]
    simp only [this]
  · have : (fun s : ℝ => XBT.clampExt u₀ H (u, Real.toNNReal s)) =
        fun s : ℝ => H (u, Real.toNNReal s) := by
      funext s; simp [XBT.clampExt_apply, min_eq_left hu]
    rw [this, XBT.clampExt_apply, min_eq_left hu]; exact h3 u hu r

private theorem gBar_congr_slice {h h' : C(ℝ≥0, ℝ)} (e : h = h') (hh : IsSlice h) (hh' : IsSlice h')
    (r : ℝ≥0) : gBar h hh r = gBar h' hh' r := by subst e; rfl

private theorem mass_congr_slice {h h' : C(ℝ≥0, ℝ)} (e : h = h') (hh : IsSlice h) (hh' : IsSlice h')
    (r : ℝ≥0) : mass h hh r = mass h' hh' r := by subst e; rfl

private theorem gBarX_clampExt {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hX : MemXBall u₀ x H) (u r : ℝ≥0) :
    gBarX (memXBall_clampExt hX) u r = gBarX hX u r :=
  gBar_congr_slice (XBT.clampExt_curry_of_le H (min_le_right u u₀)) _ _ r

/-- Characteristics transfer to the clamped extension. -/
private theorem isCharacteristic_clampExt {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hX : MemXBall u₀ x H) {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ}
    (hχ : IsCharacteristic hX u₁ r₁ χ) :
    IsCharacteristic (memXBall_clampExt hX) u₁ r₁ χ := by
  refine ⟨hχ.1, fun t ht => ?_⟩
  have : charField (memXBall_clampExt hX) t (χ t) = charField hX t (χ t) := by
    unfold charField; rw [gBarX_clampExt]
  rw [this]; exact hχ.2 t ht

/-- The sealed mass theorem transfers to strip slices via the time clamp. -/
private theorem antitoneOn_mass_characteristic_clamped {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H) (hX : MemXBall u₀ x H)
    {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} {χ : ℝ → ℝ} (hχ : IsCharacteristic hX u₁ r₁ χ) :
    AntitoneOn (fun s : ℝ => mass (H.curry (min (Real.toNNReal s) u₀))
        (hH.isSlice _ (min_le_right _ _)) (Real.toNNReal (χ s))) (Icc 0 (u₁ : ℝ)) := by
  have hK := Christodoulou.Bondi.antitoneOn_mass_characteristic
    (XBT.isClassicalSolution_clampExt hH)
    (memXBall_clampExt hX) (XBT.isSlice_clampExt hH) (isCharacteristic_clampExt hX hχ)
  intro a ha b hb hab
  have := hK ha hb hab
  have e : ∀ s : ℝ, mass ((XBT.clampExt u₀ H).curry (Real.toNNReal s))
      (XBT.isSlice_clampExt hH _) (Real.toNNReal (χ s)) =
      mass (H.curry (min (Real.toNNReal s) u₀)) (hH.isSlice _ (min_le_right _ _))
        (Real.toNNReal (χ s)) := by
    intro s
    exact mass_congr_slice (by ext r; rfl) _ _ _
  simpa only [e] using this

namespace IsIncomingRay


theorem antitoneOn_mass {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H) (hX : MemXBall u₀ x H) {r₀ : ℝ≥0} {u₁ : ℝ} {χ : ℝ → ℝ}
    (hχ : IsIncomingRay hX r₀ u₁ χ) :
    AntitoneOn (fun s : ℝ => mass (H.curry (min (Real.toNNReal s) u₀))
        (hH.isSlice _ (min_le_right _ _)) (Real.toNNReal (χ s))) (Icc 0 u₁) := by
  exact antitoneOn_mass_characteristic_clamped hH hX
    (XFC.IsIncomingRay.isCharacteristic hχ ⟨u₁, hχ.1⟩ le_rfl)

end IsIncomingRay

/-- m is nondecreasing (in r) on the terminal-time section u = u₁ of the reflected ray; when
the ray reaches the centre (χ(u₁) = 0) this section is the whole outgoing light ray u = u₁, r ≥
0 (the monotonicity of m in r at fixed u, [P] p. 344, (4.4)–(4.5)). Stated for arbitrary u₁, χ,
with m on the clamped strip slice; for an incoming ray the clamps are the identity there. -/
theorem monotoneOn_mass_reflectedRay_outgoing {u₀ : ℝ≥0} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    (hH : IsClassicalSolution u₀ H) (u₁ : ℝ) (χ : ℝ → ℝ) :
    MonotoneOn (fun p : ℝ × ℝ => mass (H.curry (min (Real.toNNReal p.1) u₀))
        (hH.isSlice _ (min_le_right _ _)) (Real.toNNReal p.2))
      {p | p ∈ reflectedRay u₁ χ ∧ p.1 = u₁} := by
  intro p hp q hq hpq
  have htime : p.1 = q.1 := hp.2.trans hq.2.symm
  dsimp only
  simp only [htime]
  exact monotone_mass _ _ (Real.toNNReal_mono hpq.2)

end XFC

end Christodoulou.Bondi
