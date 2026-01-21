/-
  Generated from Simple language
  Module: TestEnums
-/

import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic

namespace TestEnums

-- Type definitions
inductive Color where
  | Red : Color
  | Green : Color
  | Blue : Color
deriving Repr, DecidableEq

inductive Result (T : Type) (E : Type) where
  | Ok : T -> Result T E
  | Err : E -> Result T E
deriving Repr, DecidableEq

inductive Option (T : Type) where
  | Some : T -> Option T
  | None : Option T
deriving Repr, DecidableEq

end TestEnums
