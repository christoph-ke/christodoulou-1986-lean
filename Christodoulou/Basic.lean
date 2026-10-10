module

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-! A compilation check for the Lean/Mathlib setup, independent of the project theorem. -/

namespace Christodoulou

example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

end Christodoulou
