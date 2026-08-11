# Half-landed fixes across the duplicate test trees — census + repairs (Q14)

**Status:** OPEN — 26 half-landed fixes identified, 15 repaired and landed.
The guard recommended at the bottom of this document is now IMPLEMENTED
(`879108c80c2`); see "Guard — landed" below.
**Measured against:** committed tree at `origin/main` = `9072192c4ff` (never the
shared working copy). Repairs landed on later tips; shas listed below.
**Predecessor:** `duplicate_test_tree_merge_worklist_2026-08-09.md` (v3),
`vmm_kernel_memory_specs_test_local_shims_not_product_2026-08-04.md`,
repair commit `b4c4382e0c5`.

## The defect class

`test/01_unit` ≡ `test/unit`, `test/02_integration` ≡ `test/integration`,
`test/03_system` ≡ `test/system`, `test/05_perf` ≡ `test/perf` are duplicate
trees and **both execute** — `test_runner_new` has no path allowlist, default
root `test/`, recursive. An agent that greps, finds one hit, fixes it, and marks
the bug FIXED leaves the other leg live and broken.

A bug doc that says FIXED while the defect is still live on the twin is worse
than an open bug: it removes the defect from every future search.

## Divergence census — all four root pairs

Blob-sha compare of the committed tree; no line-content heuristic involved.

| root pair | common | divergent |
|---|---|---|
| `01_unit` ↔ `unit` | — | 789 |
| `02_integration` ↔ `integration` | — | 84 |
| `03_system` ↔ `system` | — | 62 |
| `05_perf` ↔ `perf` | — | 24 |
| **total** | **9,999** | **959** |

Cross-check: 789 + 62 = 851 for the two roots the v3 worklist covered, which is
its independently derived 851 exactly.

## Classification histogram

Discriminator: a commit whose subject matches `^(fix|repair|bug)[(:]` that
touched one leg and is absent from the other leg's history.

| class | pairs | share |
|---|---|---|
| **HALF-LANDED FIX** (fix commit on exactly ONE leg) | **26** | 2.7% |
| — numbered-leg-only repaired | 19 | |
| — legacy-leg-only repaired | 7 | |
| both legs got independent fix commits | 0 | 0% |
| DRIFT (no fix commit on either leg) | 933 | 97.3% |

The 933 DRIFT pairs are the pre-existing content divergence catalogued by the v3
worklist (`genuine-merge` / `adopt-superset` classes). They are a merge problem,
not a live-defect problem, and are out of scope here.

**INTENTIONAL divergence: none found.** No pair carried a comment, header, or
commit message asserting the legs are meant to differ. The duplication is
accidental in every case examined.

## Bug docs whose FIXED status is only half-true

124 bug docs marked FIXED/RESOLVED name a spec path that is currently divergent.
Of those, the ones naming a path in the half-landed-fix set — i.e. where the
FIXED claim is demonstrably false on one executing leg:

| bug doc | spec named | note |
|---|---|---|
| `vmm_kernel_memory_specs_test_local_shims_not_product_2026-08-04.md` | `os/kernel/ipc/execve_spec.spl` | **second** half-truth in the same doc; `vmm_vma_spec` was the first (`b4c4382e0c5`) |
| `pool_linked_list_push_fails_complex_indexed_field_receiver_2026-08-07.md` | `lib/nogc_async_mut_noalloc/collections/linked_list_spec.spl` | legacy leg was a skipped stub — **REPAIRED** |
| `for_loop_variable_leaks_into_enclosing_scope_2026-08-04.md` | `app/interpreter/perf_spec.spl` | legacy leg 14 asserts vs 67 — **REPAIRED** |
| `frontend_single_item_use_braces_import_crash_2026-07-29.md` | `compiler/hir/resolve_import_symbols_spec.spl` | legacy leg 11 asserts vs 97 |
| `hir_get_symbol_id_zero_returns_nil_2026-07-29.md` | `compiler/hir/resolve_import_symbols_spec.spl` | same leg |
| `resolve_import_symbols_spec_field_and_wiring_repair_2026-07-29.md` | `compiler/hir/resolve_import_symbols_spec.spl` | same leg |
| `source_fixture_spec_unescaped_interpolation_and_content_drift_2026-07-20.md` | `compiler/hir/resolve_import_symbols_spec.spl` | same leg |
| `sspec_expect_eq_to_equal_false_silently_wrong_2026-07-17.md` | `compiler/hir/resolve_import_symbols_spec.spl` | same leg |
| `dotq_tail_position_in_bool_returning_fns_2026-08-09.md` | `app/app_mcp_intensive_spec.spl` | 41+/41- both directions |
| `only_compiled_dead_tag_sweep_2026-07-03.md` | `app/app_mcp_intensive_spec.spl` | same pair |
| `wm_mouse_wheel_events_dropped_2026-07-05.md` | `os/drivers/input/ps2_mouse_spec.spl` | legacy leg 39 asserts vs 115 |
| `undeclared_imported_symbols_census.md` | `os/compositor/wm_action_applier_spec.spl`, `lib/common/window_protocol/input_translator_spec.spl` | |
| `value_type_writeback_family_audit_2026-08-09.md` | `compiler/backend/interpreter_backend_spec.spl` | legacy leg 38 asserts vs 52 |
| `test_tree_divergence_sample{2,4,6,7,8}_15_triage_2026-08-0*.md` | various | a concurrent reconciliation campaign; see below |

`pool_linked_list...` and `for_loop_variable...` are the sharpest: the legacy leg
was a *skipped stub* / *assertion-free file* that executed and reported a pass.

## Concurrent campaign — do not duplicate

Commits `c4f837be41e`, `04d06aa0c8a`, `2231908bc32`, `e42d44f800e`,
`45df29b8cba` are `fix(test): reconcile N diverged test-tree pairs (sample K)`.
Another session is already reconciling the DRIFT population in samples of ~11,
with triage docs `test_tree_divergence_sample{2,4,6,7,8}_15_triage`. This
document deliberately does **not** touch those pairs. Coordinate before
extending into the 933-pair DRIFT set.

## Repairs landed

Every repair adopts the leg that received the fix commit, verbatim, and is
verified by running **both** legs. No assertion was weakened, skipped, or
softened.

| # | spec | commit | verdict (both legs) |
|---|---|---|---|
| 1 | `os/kernel/memory/pmm_spec.spl` | `540f803bfa7` | 22 total, 22 passed, 0 failed |
| 2 | `lib/nogc_async_mut_noalloc/collections/linked_list_spec.spl` | `5bee7af561e` | 2 total, 2 passed, 0 failed |
| 3 | `compiler/borrow/borrow_check_spec.spl` | `45118ef2938` | 11 total, 11 passed, 0 failed |
| 4 | `app/interpreter/perf_spec.spl` | `b108b447fc1` | 41 total, 41 passed, 0 failed |
| 5 | `os/drivers/input/ps2_keyboard_spec.spl` | see below | 43 total, 43 passed, 0 failed |

`pmm_spec` is the exact recurrence of the vmm defect: the numbered leg had been
changed to construct the real `os.kernel.memory.pmm.PhysMemManager`, while the
legacy leg still declared a test-local `_TestPhysMemManager` shim with its own
`total_memory` / `free_memory` / `used_pages`. The product methods were untested
on that leg for four days while the bug doc read FIXED.

`scripts/check/test_tree_divergence_baseline.txt` is trimmed by one line per
converged pair, as `b4c4382e0c5` did.

## Second repair wave (2026-08-10) — 8 more converged

Every one verified by running **both** legs and reading the real verdict line.
No assertion was weakened, skipped or softened anywhere in this wave.

| # | spec | commit | verdict (both legs) |
|---|---|---|---|
| 6 | `os/drivers/input/ps2_mouse_spec.spl` | `e57b019ca2d` | 42 total, 42 passed, 0 failed |
| 7 | `compiler/hir/resolve_import_symbols_spec.spl` | `6f66d2a6c98` | 27 total, 27 passed, 0 failed |
| 8 | `compiler/lint/stub_impl_spec.spl` | `c8b688dbee4` | 60 total, 60 passed, 0 failed |
| 9 | `compiler/mono/monomorphize_integration_spec.spl` | `6908bc797cd` | **18 total, 17 passed, 1 failed — RED, left RED** |
| 10 | `lib/common/window_protocol/input_translator_spec.spl` | `f6a6145ad4d` | 8 total, 8 passed, 0 failed |
| 11 | `compiler/backend/interpreter_backend_spec.spl` | `0e8a8cc87bc` | 13 total, 13 passed, 0 failed |
| 12 | `os/kernel/ipc/execve_spec.spl` | `6788fd65c4c` | 8 total, 8 passed, 0 failed |
| 13 | `os/compositor/wm_action_applier_spec.spl` | `b5119f4889e` | **1 total, 0 passed, 1 failed (zero-examples) — RED, pre-existing** |

Three of these needed a genuine merge rather than adoption:

- **`monomorphize_integration_spec`** was inverted — the LEGACY leg held the
  only real oracle, and it had never run there (a stale `use std.test.*` made
  the whole file report `executed=0 ... reason=unresolved-module`), while the
  numbered leg had deleted the oracle outright. Merged: numbered leg's import
  removal + legacy leg's oracle. It is now RED against a real driver
  regression — filed as
  `doc/08_tracking/bug/driver_hir_pipeline_error_guard_regressed_to_raw_errors_len_2026-08-10.md`.
- **`wm_action_applier_spec`** — the numbered leg gained five `it` blocks the
  legacy leg lacked, but the legacy leg held the ONLY coverage of
  `Compositor.create_windows_from_shared_scene`. Adoption would have deleted
  it; the merged file has 18 blocks, a superset of both. Both legs are RED for
  an unrelated pre-existing reason (`vulkan_order_env_get` not found makes the
  file report `zero-examples`) — filed as
  `doc/08_tracking/bug/wm_action_applier_spec_dead_on_both_legs_vulkan_order_env_get_2026-08-10.md`.
  This was verified as PRE-EXISTING by running the unmodified committed content
  of both legs at the base first.
- **`stub_impl_spec`** — the legacy leg's three unique contexts assert the
  PRE-WP-8 semantics and directly contradict the product (they expect
  `pass_do_nothing("intentional")` to warn and `_noop_load` to be exempt; the
  product now does the opposite). Adopting the numbered leg is correct; keeping
  them would have re-asserted deleted behaviour.

`execve_spec` and `resolve_import_symbols_spec` looked like genuine merges from
the diffstat but are not: in both cases the `it`-name sets are identical (or the
legacy set is a strict subset) and every apparent deletion is a call site the
numbered leg rewrote into a better form.

## Still remaining

- `lib/common/format_spec.spl` (24+/0-) — **CONTESTED**, deliberately untouched.
  A prior agent's sync of this file was clobbered mid-session; it needs a writer
  who can confirm no other session is active on it.
- The remaining sites named in the census table above that neither wave reached.

## Guard — landed

`879108c80c2` implements the extension recommended below. `--base` + `--ref`
now intersect the outgoing `git diff --name-only` with the pair table and fail
when a range edits one leg and leaves the twin untouched AND divergent; a
one-leg edit that CONVERGES the pair passes, so the concurrent reconciliation
campaign is unaffected. pre-push records the range base alongside the pushed
sha and passes both. Proven non-vacuous with planted fixtures (base control
PASS `half-landed: 0 checked, 0`; one-leg-divergent fixture FAIL with
`1 checked, 1 half-landed` and `0 new, 0 fixed-but-still-baselined`, i.e. the
new check was the only thing that fired; converging fixture `1 checked, 0`).

Also worth recording: the "8 mirror-only (6 unallowlisted)" caveat at the
bottom of this document is **no longer reproducible** — the base control on
2026-08-10 reads `PASS — 5732 pairs checked, ... 2 mirror-only (all
allowlisted)`, exit 0. It was fixed upstream between the two waves.

## Guard recommendation

**Yes — extend `scripts/check/check-test-tree-divergence.shs`, do not build a
new guard.** It already reads committed content via `git ls-tree`/`cat-file`,
already has the baseline mechanism, already has the right verdict convention,
and is already wired into the pre-push path.

The extension is narrow: today the guard fails only on *new* divergence relative
to the baseline. It should additionally fail when **a commit in the outgoing
range edits one leg of a baselined pair without editing the other**. That is the
half-landed-fix signature exactly, and it is the case the current guard is blind
to — a baselined pair stays baselined no matter how far the legs drift apart.

Cost:
- ~30 lines: intersect `git diff --name-only <base>..<tip>` with the pair table;
  for each hit, assert the twin path is also in the diff.
- Runtime: negligible — it reads the diff already computed, not the 9,999-pair
  content scan (which is the 2-minute part).
- False-positive risk: real, for the concurrent sample-reconciliation campaign,
  which lands one-leg edits *by design* when adopting a superset. Mitigation: the
  guard should pass when the edit makes the pair **converge** (post-edit blob
  shas equal), which is precisely what a correct reconciliation does. A one-leg
  edit that leaves the pair divergent is the thing to block.

The deeper fix is to delete one tree, but 739 pairs are genuine merges, so that
is blocked on the merge campaign and is not this guard's job.

## Caveat on the guard's current state

`check-test-tree-divergence.shs` FAILs at the origin base with
`8 mirror-only (6 unallowlisted)`. That is **pre-existing**, introduced by
`d67e01062aa` ("fix(guards): test-tree divergence guard now fails on
unallowlisted mirror-only paths"), and is unrelated to the repairs here. Every
repair above was verified with a control run on the base first; each landed with
`0 new, 0 fixed-but-still-baselined`.
