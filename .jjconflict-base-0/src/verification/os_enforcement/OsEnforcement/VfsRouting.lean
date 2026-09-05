/-
  OsEnforcement.VfsRouting — pure model of the SimpleOS VFS handle table
  (handle → owning-mount routing), and a sorry-free proof that a handle routes
  to the mount that OPENED it — never mount[0] — and that a released handle is
  no longer routable (master plan §21 / lane INT-2).

  Source of truth (INT-2 — 2026-07-27):
    src/os/kernel/fs/vfs_handle_table.spl
      struct VfsHandleEntry { vfs_handle: u64, mount_index, mount_path,
        driver_handle }
      struct VfsHandleTable { entries: [VfsHandleEntry], next_handle: u64 }
        next_handle starts at 1; VFS handles are never reused.
      register(mount_index, mount_path, driver_handle) -> u64
        appends an entry keyed by a globally-unique vfs_handle, returns it.
      lookup(vfs_handle) -> resolve to owning (mount, driver_handle); found:false
        with mount_index = VFS_HANDLE_NO_MOUNT (-1) on a miss.
      release(vfs_handle) -> drop the entry (double-close returns false).

  The bug this fixes (from the file header): the old VFS routed EVERY handle op
  to `self.mounts[0]` ("Simplified: use first mount"), so a file opened on mount
  B was read/written against mount A — silent cross-filesystem corruption. The
  table makes each op resolve to the mount that issued the handle.

  Modelling notes
  ===============
  An entry is `(handleId, mountIndex, driverHandle)` as `Nat`s; a table pairs the
  entry list with the monotonically-increasing `nextHandle` (starting at 1).
  `register` appends a fresh entry and returns its handle.  `lookup` is the
  first-match `List.find?`; `release` filters the entry out.  The freshness
  invariant `Fresh` (every stored handle id `< nextHandle`) is what guarantees the
  newly-registered handle cannot collide with an older entry — it is preserved by
  `register` (`fresh_register`).  Core Lean 4 only (List/Nat/Bool, no Mathlib).

  Headline theorems (SPipe manual layer):
    OsEnforcement.handle_routes_to_owning_mount   (VR1)
    OsEnforcement.distinct_handles_distinct_routing (VR2)
    OsEnforcement.released_handle_not_routable     (VR3)
  Gate: `cd src/verification/os_enforcement && lake build`.
-/

namespace OsEnforcement

-- ============================================================
-- § 1  Model — entries, table, register / lookup / release
-- ============================================================

/-- One open-file description: a VFS handle bound to its owning mount and the
    driver-local handle. -/
structure Entry where
  handleId     : Nat
  mountIndex   : Nat
  driverHandle : Nat
  deriving Repr, DecidableEq

/-- The handle table: the entry list plus the next handle to hand out. -/
structure Table where
  entries    : List Entry
  nextHandle : Nat
  deriving Repr

/-- The empty table (source: `next_handle` starts at 1). -/
def Table.empty : Table := { entries := [], nextHandle := 1 }

/-- `register t mountIdx drv` mirrors `register(...)`: append a fresh entry keyed
    by `t.nextHandle` and return the updated table together with that handle. -/
def register (t : Table) (mountIdx drv : Nat) : Table × Nat :=
  let h := t.nextHandle
  ({ entries := t.entries ++ [⟨h, mountIdx, drv⟩], nextHandle := t.nextHandle + 1 }, h)

/-- `lookup t h` mirrors `lookup(vfs_handle)`: the first entry whose handle id
    matches, or `none` (the found:false / mount_index = -1 miss). -/
def lookup (t : Table) (h : Nat) : Option Entry :=
  t.entries.find? (fun e => e.handleId == h)

/-- `mountIndexOf t h` mirrors `mount_index_of`: the owning mount, or `none`. -/
def mountIndexOf (t : Table) (h : Nat) : Option Nat :=
  (lookup t h).map (·.mountIndex)

/-- `release t h` mirrors `release(vfs_handle)`: drop the entry for `h`. -/
def release (t : Table) (h : Nat) : Table :=
  { t with entries := t.entries.filter (fun e => e.handleId != h) }

/-- Freshness invariant: every stored handle id is below the next handle to hand
    out — so a newly-registered handle cannot alias an existing entry. -/
def Fresh (t : Table) : Prop := ∀ e ∈ t.entries, e.handleId < t.nextHandle

-- ============================================================
-- § 2  Supporting lemmas (core Lean, no Mathlib)
-- ============================================================

/-- `beq` on `Nat` reflects `≠` into `false`. -/
theorem beq_false_of_ne {a b : Nat} (h : a ≠ b) : (a == b) = false := by
  cases hb : a == b with
  | false => rfl
  | true  => exact absurd (eq_of_beq hb) h

/-- Under `Fresh`, none of the stored entries match the next (fresh) handle. -/
theorem find?_entries_fresh (t : Table) (hf : Fresh t) :
    t.entries.find? (fun e => e.handleId == t.nextHandle) = none := by
  rw [List.find?_eq_none]
  intro x hx
  simp [beq_false_of_ne (Nat.ne_of_lt (hf x hx))]

-- ============================================================
-- § 3  register / lookup facts under the freshness invariant
-- ============================================================

/-- Under `Fresh`, looking up the just-registered handle returns exactly the new
    entry — it routes to the mount that opened it. -/
theorem lookup_register (t : Table) (mountIdx drv : Nat) (hf : Fresh t) :
    lookup (register t mountIdx drv).1 (register t mountIdx drv).2
      = some ⟨t.nextHandle, mountIdx, drv⟩ := by
  unfold lookup register
  simp only
  rw [List.find?_append, find?_entries_fresh t hf]
  simp

/-- `register` preserves the freshness invariant. -/
theorem fresh_register (t : Table) (mountIdx drv : Nat) (hf : Fresh t) :
    Fresh (register t mountIdx drv).1 := by
  unfold Fresh register
  simp only
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact Nat.lt_succ_of_lt (hf e h)
  · rw [List.mem_singleton] at h
    subst h
    exact Nat.lt_succ_self _

-- ============================================================
-- § 4  The routing invariants — VR1 .. VR3
-- ============================================================

/-- VR1 — handle_routes_to_owning_mount:
    an op on a freshly-registered handle routes to the mount that opened it, NOT
    mount[0]. -/
theorem handle_routes_to_owning_mount (t : Table) (mountIdx drv : Nat)
    (hf : Fresh t) :
    mountIndexOf (register t mountIdx drv).1 (register t mountIdx drv).2
      = some mountIdx := by
  unfold mountIndexOf
  rw [lookup_register t mountIdx drv hf]
  rfl

/-- VR2 — distinct_handles_distinct_routing:
    register two handles for two different mounts; each routes to ITS OWN mount.
    A handle issued by mount B never resolves to mount A. -/
theorem distinct_handles_distinct_routing (t : Table)
    (mA drvA mB drvB : Nat) (hf : Fresh t) :
    mountIndexOf (register (register t mA drvA).1 mB drvB).1 (register t mA drvA).2
        = some mA
      ∧ mountIndexOf (register (register t mA drvA).1 mB drvB).1
          (register (register t mA drvA).1 mB drvB).2 = some mB := by
  have hf1 : Fresh (register t mA drvA).1 := fresh_register t mA drvA hf
  constructor
  · -- handle A (= t.nextHandle) still routes to mount A after B is registered
    unfold mountIndexOf lookup register
    simp only
    rw [List.find?_append, List.find?_append, find?_entries_fresh t hf]
    simp
  · -- handle B routes to mount B
    have hB := lookup_register (register t mA drvA).1 mB drvB hf1
    unfold mountIndexOf
    rw [hB]
    rfl

/-- VR3 — released_handle_not_routable:
    after releasing `h`, a lookup of `h` fails — no stale routing survives. -/
theorem released_handle_not_routable (t : Table) (h : Nat) :
    lookup (release t h) h = none := by
  unfold lookup release
  simp only
  rw [List.find?_eq_none]
  intro e he
  rw [List.mem_filter] at he
  have hbne : (e.handleId != h) = true := he.2
  rw [bne_iff_ne] at hbne
  simp [beq_false_of_ne hbne]

-- Axiom audit (must report no sorryAx)
#print axioms handle_routes_to_owning_mount
#print axioms released_handle_not_routable

end OsEnforcement
