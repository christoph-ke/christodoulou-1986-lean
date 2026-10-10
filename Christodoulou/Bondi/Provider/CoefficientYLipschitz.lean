module
public import Christodoulou.Frozen.Bondi.MemXBall
public import Christodoulou.Frozen.Bondi.HBarX
public import Christodoulou.Frozen.Bondi.GX
public import Christodoulou.Frozen.Bondi.GBarX
public import Christodoulou.Frozen.Bondi.DerivGBarX
public import Christodoulou.Frozen.Bondi.LinearSource
import Christodoulou.Bondi.FieldLipschitz



public section

open Set MeasureTheory Real
open scoped NNReal

namespace Christodoulou.Bondi.Provider
open Christodoulou.Radial Christodoulou.Bondi

theorem coefficient_y_lipschitz {u₀ : ℝ≥0}
    {x : ℝ}
    {H K : C(ℝ≥0 × ℝ≥0, ℝ)}
    {hH : MemXBall u₀ x H}
    {hK : MemXBall u₀ x K}
    {y : ℝ}
    (hy : ∀ u : ℝ≥0, u ≤ u₀ → ∀ r : ℝ≥0, (1 + (r : ℝ)) ^ 3 * |H (u, r) - K (u, r)| ≤ y :=
      by assumption)
    {u r : ℝ≥0} :
    |hBarX u₀ H u r - hBarX u₀ K u r| ≤ y / (1 + (r : ℝ)) ∧
    |gX hH u r - gX hK u r| ≤ 4 * π * x * y / (1 + (r : ℝ)) ^ 2 ∧
    |gBarX hH u r - gBarX hK u r| ≤ 4 * π * x * y / (1 + (r : ℝ)) ∧
    |derivGBarX hH u r - derivGBarX hK u r| ≤
      2 * π * x * (2 + π * x ^ 2) * y / (1 + (r : ℝ)) ^ 2 ∧
    |linearSource hH u r - linearSource hK u r| ≤
      π * x ^ 2 * (13 / 6 + π * x ^ 2) * y / (1 + (r : ℝ)) ^ 3 :=
  XLip.coefficient_y_lipschitz hH hK hy u r

end Christodoulou.Bondi.Provider
