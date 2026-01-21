/-
  Generated from Simple language
  Module: TestTraits
-/

import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic

namespace TestTraits

-- Type classes
class Eq (T : Type) where
  eq : T -> T -> Bool

class Comparable (T : Type) where
  compare : T -> T -> Int

-- Instances
instance : Eq Int where
  eq := fun a b => a == b

end TestTraits
