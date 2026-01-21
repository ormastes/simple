/-
  Generated from Simple language
  Module: TestTypes
-/

import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic

namespace TestTypes

-- Type definitions
structure Point where
  x : Int
  y : Int
deriving Repr

structure Person where
  name : String
  age : Int
  active : Bool
deriving Repr

end TestTypes
