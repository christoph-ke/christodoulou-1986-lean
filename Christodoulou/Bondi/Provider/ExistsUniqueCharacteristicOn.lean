module
public import Christodoulou.Frozen.Bondi.IsCharacteristic
public import Christodoulou.Frozen.Bondi.CurveExtension
import Christodoulou.Frozen.Bondi.ExistsIsCharacteristic
import Christodoulou.Frozen.Bondi.IsCharacteristicEqOn



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem existsUnique_characteristicOn {u₀ : ℝ≥0} {x : ℝ} {H : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H} {u₁ : Icc (0 : ℝ) u₀} {r₁ : ℝ≥0} :
    ∃! χ : Icc (0 : ℝ) (u₁ : ℝ) → ℝ, IsCharacteristic hH u₁ r₁ (curveExtension u₁ χ) := by
  obtain ⟨χ, hχc⟩ := exists_isCharacteristic hH u₁ r₁
  -- the extension of the restriction agrees with χ on [0, u₁]
  have hext : ∀ t ∈ Icc (0 : ℝ) u₁,
      curveExtension u₁ (fun s : Icc (0 : ℝ) u₁ => χ s) t = χ t := by
    intro t ht
    simp only [curveExtension, Set.projIcc_of_mem _ ht]
  have hspec : IsCharacteristic hH u₁ r₁ (curveExtension u₁ (fun s : Icc (0 : ℝ) u₁ => χ s)) := by
    refine ⟨?_, fun t ht => ?_⟩
    · rw [hext _ ⟨u₁.2.1, le_rfl⟩]; exact hχc.1
    · have h := hχc.2 t ht
      rw [hext t ht]
      exact h.congr_of_mem (fun s hs => hext s hs) ht
  refine ⟨fun s => χ s, hspec, fun ψ hψ => ?_⟩
  funext s
  have := IsCharacteristic.eqOn hψ hspec s.2
  calc ψ s = curveExtension u₁ ψ s := by simp [curveExtension, Set.projIcc_of_mem _ s.2]
    _ = curveExtension u₁ (fun s : Icc (0 : ℝ) u₁ => χ s) s := this
    _ = χ s := hext s s.2

end Christodoulou.Bondi.Provider
