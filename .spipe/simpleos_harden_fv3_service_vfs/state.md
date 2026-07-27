# Lane FV3 — More formal invariants (master plan §21.3)

Status: **DONE — all 12 theorems sorry-free, gate GREEN.**

Extended the core-Lean-4 project at `src/verification/os_enforcement/`
(toolchain leanprover/lean4:v4.30.0, empty package manifest = NO Mathlib,
offline) with two new sorry-free modules, each modeling a REAL invariant from
landed SimpleOS code. Matched the namespace `OsEnforcement` and the
ContainerIsolation / DeviceGrant idiom (core `List`/`Nat`/`Bool` only).

## Gate result

```
cd src/verification/os_enforcement && lake build
✔ [6/8] Built OsEnforcement.VfsRouting
✔ [7/8] Built OsEnforcement
Build completed successfully (8 jobs).
EXIT=0
```

- ZERO errors, ZERO warnings.
- `grep -niE 'sorry|admit'` on both new files → only the two `-- must report no
  sorryAx` audit comments (no real `sorry`/`admit`).
- `#print axioms` (one theorem per module, checked at build time):
  - `restart_drops_stale_grants` → **does not depend on any axioms**
  - `restart_denied_at_cap` → `[propext]`
  - `handle_routes_to_owning_mount` → `[propext, Classical.choice, Quot.sound]`
  - `released_handle_not_routable` → `[propext, Quot.sound]`
  - **No `sorryAx` anywhere.** (Classical.choice/propext/Quot.sound come from the
    core `List.find?` / `simp` lemmas — standard, not a proof hole.)

## Files touched (exclusive paths only)

- `src/verification/os_enforcement/OsEnforcement/ServiceRestart.lean` (new)
- `src/verification/os_enforcement/OsEnforcement/VfsRouting.lean` (new)
- `src/verification/os_enforcement/OsEnforcement.lean` (added 2 import lines only)
- `.spipe/simpleos_harden_fv3_service_vfs/state.md` (this file)

No commit / no push (left in working copy per lane instructions).

## Module 1 — ServiceRestart.lean

Models `src/os/services/service_manifest.spl` (`on_restart`, `should_restart`).

Model:
- `Policy` = inductive `never | onFailure | always` (the POLICY_* string
  constants).
- `Service = { name : Nat, version : Nat, grantedHandles : List Nat,
  restartCount : Nat, maxRestarts : Nat, policy : Policy }`. `name`/`version`
  are opaque identity ids; `grantedHandles` are the held device/secret grant ids.
- `onRestart s = { s with grantedHandles := [], restartCount := restartCount+1 }`
  — mirrors `on_restart`'s clear-grants + increment (state→Restarting elided as
  it is not part of the invariant).
- `shouldRestart p c m = match p | never => false | _ => decide (c < m)` —
  mirrors `should_restart(policy, restart_count, max_restarts)`.

Theorems (all closed):
- **SR1 `restart_drops_stale_grants`** — `∀ s, (onRestart s).grantedHandles = []`
  (§21: a restarted service retains NO stale grants). `by rfl`.
- **SR2 `never_never_restarts`** — `shouldRestart never c m = false` for all c,m.
- **SR2 `restart_denied_at_cap`** — `m ≤ c → shouldRestart p c m = false` for
  EVERY policy (restart-storm bound; never was never restarting).
- **SR2 `restart_allowed_below_cap`** — `p ≠ never → c < m →
  shouldRestart p c m = true` (below-cap on_failure/always DO restart).
- **SR3 `restart_preserves_identity`** — `(onRestart s).name = s.name ∧
  .version = s.version ∧ .grantedHandles = []` (only grants cleared).

## Module 2 — VfsRouting.lean

Models `src/os/kernel/fs/vfs_handle_table.spl` (handle→mount routing, lane INT-2:
the fix for the old "Simplified: use first mount" `self.mounts[0]` bug).

Model:
- `Entry = { handleId : Nat, mountIndex : Nat, driverHandle : Nat }`.
- `Table = { entries : List Entry, nextHandle : Nat }`; `Table.empty` has
  `nextHandle = 1` (source reserves 0 as invalid).
- `register t mountIdx drv = (⟨entries ++ [⟨nextHandle,mountIdx,drv⟩],
  nextHandle+1⟩, nextHandle)` — append a fresh entry, return its VFS handle.
- `lookup t h = entries.find? (·.handleId == h)` (first-match, `none` on miss).
- `mountIndexOf t h = (lookup t h).map (·.mountIndex)`.
- `release t h = { t with entries := entries.filter (·.handleId != h) }`.
- `Fresh t := ∀ e ∈ entries, e.handleId < nextHandle` — the freshness invariant
  that makes a newly-issued handle collision-free; preserved by `register`
  (`fresh_register`, proved).

Theorems (all closed):
- **VR1 `handle_routes_to_owning_mount`** — under `Fresh t`,
  `mountIndexOf (register t mountIdx drv).1 (register t mountIdx drv).2
   = some mountIdx`. An op on a registered handle routes to the mount that
  opened it, NOT mount[0].
- **VR2 `distinct_handles_distinct_routing`** — register handle A for mount A,
  then handle B for mount B; A routes to `some mA` and B routes to `some mB`.
  A handle from mount B never resolves to mount A.
- **VR3 `released_handle_not_routable`** — `lookup (release t h) h = none`
  (no stale routing after close).

Supporting lemmas: `beq_false_of_ne`, `find?_entries_fresh`,
`lookup_register`, `fresh_register` (all sorry-free).

## Blocked rows

NONE. All 5 (SR) + 7 (VR incl. supporting lemmas) theorems closed sorry-free.

## Resume / re-verify command

```
cd src/verification/os_enforcement && lake build
grep -niE 'sorry|admit' OsEnforcement/ServiceRestart.lean OsEnforcement/VfsRouting.lean | grep -vi sorryAx
```
