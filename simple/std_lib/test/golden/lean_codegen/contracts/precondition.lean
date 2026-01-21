/-
  Generated from Simple language
  Module: TestContracts
-/

import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic

namespace TestContracts

-- Function with contract
def divide (a : Int) (b : Int) : Int :=
  a / b

-- Theorems
theorem divide_pre (a : Int) (b : Int) :
  b != 0 := by
  sorry

theorem divide_post (a : Int) (b : Int) (result : Int) :
  result * b = a := by
  sorry

end TestContracts
