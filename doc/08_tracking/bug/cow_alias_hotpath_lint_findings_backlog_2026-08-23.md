# COW-alias hot-path lint findings backlog

**Date:** 2026-08-23
**Status:** OPEN — 297 of 299 findings unremediated; rule is warn-level, not gating
**Detector:** `PERF-COW-001/002/003`, `src/compiler/35.semantics/lint/cow_alias_hotpath.spl`
**Class:** `doc/08_tracking/bug/value_semantics_cow_alias_perf_class_2026-08-21.md`

## What was measured

The new authoring-time lint was run over every non-vendored `.spl` file under
`src/` (15,213 files) on 2026-08-23:

| code | shape | count |
|---|---|---|
| `PERF-COW-001` | take / mutate / store-back round trip | 129 |
| `PERF-COW-002` | by-value helper store-back | 170 |
| `PERF-COW-003` | `.keys()`/`.values()` on a loop-invariant receiver in a loop | **0** |
| | **total** | **299** |

`PERF-COW-003 = 0` independently corroborates the class doc's "zero KEYSINLOOP"
remediation result, now confirmed across all of `src/`, not only `src/compiler`.

By root:

| root | findings | covered by `check-cow-alias-hotpath.shs`? |
|---|---|---|
| `src/lib` | 191 | yes |
| `src/os` | 77 | **no** |
| `src/app` | 15 | **no** |
| `src/compiler_rust` (`.spl` files under the seed tree) | 9 | **no** |
| `src/compiler` | 7 | yes (all 7 are the ratchet's current baseline) |

The 101 findings in `src/os`, `src/app` and `src/compiler_rust` are debt the
push-time ratchet has never been able to see, because its scan root is
`src/compiler/**`. Over the roots both tools do cover, they agree row for row.

## Heaviest single files

| findings | file |
|---|---|
| 41 | `src/os/services/container/container_manager.spl` |
| 19 | `src/lib/common/svmg/ref_vm.spl` |
| 18 | `src/lib/nogc_async_mut/engine/physics/backend_gpu/gpu_solver.spl` |
| 17 | `src/lib/nogc_async_mut/fs_driver/fat32_file_ops.spl` |
| 15 | `src/os/port/sqlite/sqlite_vfs_impl.spl` |
| 12 | `src/lib/common/ui/draw_ir_v3_emit_full.spl` |
| 11 | `src/lib/nogc_sync_mut/js/engine/interpreter_native.spl` |
| 9 | `src/os/desktop/_DesktopShell/shell_workspace_methods.spl` |
| 9 | `src/lib/gc_async_mut/web/browser_session_loading.spl` |
| 8 | `src/lib/nogc_async_mut/actor_scheduler.spl` |

## Fixed in the landing commit (2 files, 10 findings)

- `src/lib/common/js/engine/interpreter_types.spl` — 7 × `PERF-COW-001`.
  `create_env`, `set_var` and `define_var` each took a parallel table into a
  local, pushed, and stored it back, so **every JS variable write and every
  environment creation deep-copied the whole table**. Fixed by pushing through
  the owning fields.
- `src/app/interpreter/async_runtime/mailbox.spl` — 3 × `PERF-COW-002`.
  `select` removed the matched message with `self.Q = remove_at(self.Q, i)`; the
  private `remove_at` helper additionally rebuilt the array element by element
  through an aliased `result = result.push(..)` rebind, so a single selective
  receive was O(n²) in queue length. Fixed with in-place shift-down + pop through
  each owning field; the by-value helper became dead and was removed.

Both are pinned by mechanism (shape absent) in
`test/01_unit/compiler/lint/cow_alias_hotpath_product_fixes_spec.spl`; reverting
either source edit alone re-reds that spec (verified: 3 passed / 2 failed in each
single-revert run).

## Why the rest were NOT mass-edited

Every one of the remaining 289 sites needs the same judgement the two fixed ones
got: whether the store-back is an accidental alias or a genuine rebuild, and
whether an in-place equivalent preserves ordering and aliasing semantics exactly.
`self.xs = self.xs.slice(...)` (the `llm_dashboard` collectors' trim, for
example) is a true match for the shape but the rebuild is inherent to `slice`, so
"fixing" it mechanically would churn code for no gain. A blanket rewrite would be
exactly the kind of semantics-risking mass edit the class doc warns against.

## Proposed remediation order

1. `src/os/services/container/container_manager.spl` (41) and
   `container_storage.spl` (7) — one owner, one review, 48 findings.
2. `src/lib/nogc_async_mut/actor_scheduler.spl` (8) and `fat32_file_ops.spl` (17)
   — both are per-operation hot paths where the collection grows with load.
3. `src/lib/nogc_sync_mut/js/engine/interpreter_native.spl` (11) — same defect
   family as the `interpreter_types.spl` fix already landed.
4. Widen `scripts/check/check-cow-alias-hotpath.shs`'s scan root beyond
   `src/compiler/**` once the `src/os` / `src/app` population is baselined, so
   the 101 currently-invisible findings become ratcheted rather than merely
   reported.

## Coverage gap found on the way

`src/app/interpreter/async_runtime/mailbox.spl` had **no spec referencing it**
anywhere in `test/` before this change. The fix therefore ships with a mechanism
pin but no behavioural test of `Mailbox.select` itself. TODO: add a behavioural
spec for selective receive (match-out-of-order, ordering of survivors, priority
queue interaction).

## Pre-existing test-tree divergence stepped over at landing (recorded per vcs.md)

`sh scripts/check/check-test-tree-divergence-delta.shs origin/main HEAD` returned
`PASS — 3 pre-existing offender(s), 0 introduced by this range`. The base verdict
was already `FAIL — 857 diverged vs 854 baselined (3 new, 0 fixed-but-still-baselined);
1 mirror-only`. None of the three was introduced here; the full pre-existing
offender list is the `log_modes` / `mcp` integration cluster
(`integration:app/app_mcp_intensive_spec.spl`, `check_log_modes_spec.spl`,
`cli_log_modes_spec.spl`, `feature_gen_log_modes_spec.spl`,
`itf_log_modes_spec.spl`, `linkers_log_modes_spec.spl`,
`llm_dashboard_log_modes_spec.spl`, `mcp_stdio_integration_spec.spl`, …), left to
its owning lane.
