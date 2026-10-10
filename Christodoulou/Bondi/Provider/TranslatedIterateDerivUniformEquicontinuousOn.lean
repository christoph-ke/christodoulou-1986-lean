module
public import Christodoulou.Frozen.Bondi.TranslatedDataField
public import Christodoulou.Frozen.Bondi.MemXBall
public import Christodoulou.Frozen.Bondi.LinearStepMap
public import Christodoulou.Frozen.Bondi.IsDecaySlice
public import Mathlib.Topology.UniformSpace.Equicontinuity
import Christodoulou.Bondi.TranslatedEquicontinuity



public section

open Set MeasureTheory Real Filter Topology
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem translated_iterate_deriv_uniformEquicontinuousOn {T : ℝ≥0}
    {x : ℝ}
    {data : C(ℝ≥0, ℝ)}
    (hdata : IsDecaySlice data := by assumption)
    (h : ℕ → C(ℝ≥0 × ℝ≥0, ℝ) := by assumption)
    (hb : ∀ n, MemXBall T x (h n) := by assumption)
    (hzero : h 0 = translatedDataField T data := by assumption)
    (hstep : ∀ n, h (n + 1) = linearStepMap (hb n) data := by assumption) :
    UniformEquicontinuousOn (fun n (p : ℝ × ℝ) => derivWithin
      (fun z : ℝ => h n (p.1.toNNReal, z.toNNReal)) (Ici 0) p.2)
      (Icc 0 (T : ℝ) ×ˢ Ici 0) :=
  XTE.translated_iterate_deriv_uniformEquicontinuousOn data hdata h hb hzero hstep

end Christodoulou.Bondi.Provider
