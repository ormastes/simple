-- BorrowCheckerSafety.lean
-- Foundation types for borrow checking verification.
--
-- This module provides the core type definitions and safety properties
-- for verifying borrow checker correctness. It defines borrow kinds,
-- memory places, regions (lifetimes), and proves fundamental safety
-- properties such as the absence of mutable aliasing.

-- Borrow kinds
inductive BorrowKind where
  | shared    : BorrowKind
  | mutable   : BorrowKind
  | move_     : BorrowKind
  deriving Repr, DecidableEq

-- Place element
inductive PlaceElem where
  | field     : Nat → PlaceElem
  | deref     : PlaceElem
  | index     : Nat → PlaceElem
  deriving Repr, DecidableEq

-- Place in memory
structure Place where
  local : Nat
  projections : List PlaceElem
  deriving Repr, DecidableEq

-- A borrow
structure Borrow where
  place : Place
  kind : BorrowKind
  region : Nat
  deriving Repr, DecidableEq

-- Region (lifetime)
structure Region where
  id : Nat
  start_point : Nat
  end_point : Nat
  deriving Repr, DecidableEq

-- Borrow set
structure BorrowSet where
  borrows : List Borrow
  deriving Repr

-- No mutable aliasing
def NoMutableAliasing (bs : BorrowSet) : Prop :=
  ∀ b1 b2 : Borrow,
    b1 ∈ bs.borrows → b2 ∈ bs.borrows →
    b1.place = b2.place →
    b1.kind = BorrowKind.mutable →
    b1 = b2

-- All lifetimes valid
def LifetimesValid (bs : BorrowSet) (regions : List Region) : Prop :=
  ∀ b : Borrow,
    b ∈ bs.borrows →
    ∃ r : Region, r ∈ regions ∧ r.id = b.region

-- Borrow set is safe
def BorrowSet.isSafe (bs : BorrowSet) (regions : List Region) : Prop :=
  NoMutableAliasing bs ∧ LifetimesValid bs regions

-- Empty borrow set is safe
theorem empty_borrow_set_safe (regions : List Region) :
    BorrowSet.isSafe ⟨[]⟩ regions := by
  constructor
  · intro b1 b2 h1 _ _ _
    exact absurd h1 (List.not_mem_nil _)
  · intro b h
    exact absurd h (List.not_mem_nil _)
