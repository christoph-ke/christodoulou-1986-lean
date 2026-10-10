module
public import Christodoulou.Frozen.Bondi.TranslatedDataField
public import Christodoulou.Frozen.Bondi.MemXPrimeBall
public import Christodoulou.Frozen.Bondi.IsDecaySlice
public import Christodoulou.Frozen.Bondi.InitialBound
import Christodoulou.Bondi.XPrimeBasics
import Christodoulou.Frozen.Bondi.MemXPrimeBallIff
import Christodoulou.Frozen.Bondi.TranslatedDataFieldApply
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-!
# The translated seed in X′

Translation of the initial data gives the X′ seed with the same sum bound, using the frozen
X′ characterization and translated-field evaluation gates.
-/

public section

open Set Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi
namespace XPS

/-- Translation of the initial data gives an X′ seed with the same sum bound. -/
theorem translatedDataField_memXPrimeBall {T : ℝ≥0} {d : ℝ}
    (data : C(ℝ≥0, ℝ)) (hdata : IsDecaySlice data) (hbound : InitialBound data d) :
    MemXPrimeBall T d (translatedDataField T data) := by
  apply (Christodoulou.Bondi.memXPrimeBall_iff T d (translatedDataField T data)).2
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    have hshift : MapsTo (fun s : ℝ => s + (u : ℝ) / 2) (Ici 0) (Ici 0) :=
      fun s hs => add_nonneg hs (div_nonneg u.coe_nonneg (by norm_num))
    exact (hdata.1.1.comp (contDiffOn_id.add contDiffOn_const) hshift).congr
      (fun s hs => XPB.translatedDataField_real_apply T data u hu s hs)
  · have hc := hdata.1.1.continuousOn_derivWithin (uniqueDiffOn_Ici 0) (by norm_num)
    have hshift : Continuous (fun p : ℝ × ℝ => p.2 + p.1 / 2) := by fun_prop
    apply (hc.comp hshift.continuousOn (fun p hp =>
      add_nonneg hp.2 (div_nonneg hp.1.1 (by norm_num)))).congr
    intro p hp
    have hu : p.1.toNNReal ≤ T := by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal _ hp.1.1]
      exact hp.1.2
    dsimp only [Function.comp_def]
    rw [XPB.translatedDataField_derivWithin T data hdata p.1.toNNReal hu p.2 hp.2,
      Real.coe_toNNReal _ hp.1.1]
  · intro u hu r
    rw [Christodoulou.Bondi.translatedDataField_apply T data u r hu, radialDerivative,
      XPB.translatedDataField_derivWithin T data hdata u hu r r.coe_nonneg]
    simpa only [primeWeight, NNReal.coe_add, NNReal.coe_div, NNReal.coe_ofNat,
      ← add_assoc] using hbound (r + u / 2)

end XPS
end Christodoulou.Bondi
