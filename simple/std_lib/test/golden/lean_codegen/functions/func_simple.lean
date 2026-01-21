/-
  Generated from Simple language
  Module: TestFunctions
-/

import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic

namespace TestFunctions

-- Function definitions
def add (a : Int) (b : Int) : Int :=
  (a + b)

def isPositive (n : Int) : Bool :=
  (n > 0)

def factorial (n : Int) : Int :=
  if n <= 1 then 1 else n * factorial (n - 1)

-- Theorems
theorem factorial_pre (n : Int) :
  n >= 0 := by
  sorry

theorem factorial_post (n : Int) (result : Int) :
  result >= 1 := by
  sorry

end TestFunctions
