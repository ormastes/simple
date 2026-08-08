# Lane GLOBALSWEEP — containment sweep for the module-global write-visibility defect

Date: 2026-07-27
Defect (root-caused by lane GLOBAL): **a module-global written inside a function is not
observable to any helper that function subsequently calls; the write commits only when the
writing function returns.** Arrays and scalars, both engines, in the spec-runner context.

Lane SMPFIX proved it on `src/os/kernel/smp/percpu.spl` (`percpu_init` filled `g_percpu` with
32 entries, then `percpu_store_entry` saw an empty global and published a 1-entry table).

This lane is containment: find and repair every other site with the same shape.

## Method

Scanner: `build/gsweep_scan.py` (throwaway, gitignored). For every owned `.spl` under `src/**`
(excluding `src/compiler_rust/**`, `src/runtime/vendor/**`, `src/compiler/**` and the live-lane
paths listed in the task), it finds module-level `var` globals, then per function finds the
first write to each global (assignment, index-assign, or a mutating method) and reports any
call *after* that write to a same-module function that transitively reads the same global.

**Scanner validated against the known true positive**: run against `git show
HEAD:src/os/kernel/smp/percpu.spl` it reports exactly
`percpu_init write@38 global=g_percpu -> callee=percpu_store_entry @55`, and nothing else.

Corpus: 10,963 files, 503 with module globals, 1,943 globals.
**Candidates: 199 raw / 159 unique** (`build/gsweep_candidates.txt`, `build/gsweep_candidates.json`).

## Classification summary

| Class | Count | Notes |
|---|---|---|
| Hazardous (repaired) | 16 sites across 6 files | see below |
| Hazardous (deferred) | ~14 | listed under Deferred |
| Benign | ~95 | value already passed as an argument; or callee only writes; or the parent's write is immediately superseded by the callee's write to the same slot |
| Uncertain / not individually judged | ~34 | low blast radius (app/, tooling); left for a follow-up pass |

Counts after the first two buckets are estimates from directory-level triage, not a
line-by-line reading of all 159 — stated as such deliberately.

## Repaired sites

Ordered by blast radius.

### 1. `src/os/kernel/fd_table.spl` — kernel FD table (worst site found)

The dominant hotspot: 60+ raw candidates. **Baseline spec: 18 of 20 examples failing**; only
the two negative "reject invalid input" examples passed — the same signature as percpu
(10/14). Mechanism confirmed from the failure text (`expected -9 to equal 0`, i.e. EBADF:
descriptors left `FD_TYPE_FREE`).

| Writer | Global(s) | Callee that read them stale | Consequence |
|---|---|---|---|
| `fd_set` | `fd_objects`, `of_*` | `_fd_mirror_from_object` | **worst**: mirror saw the pre-write `fd_objects[idx]==0`, took the `obj == 0` branch and cleared the fd to `FD_TYPE_FREE` — `fd_set` silently failed to open ANY descriptor, including stdio |
| `fd_activate_task` | `fd_active_owner`, `fd_context_enabled`, `fd_context_initialized/owners` | `_fd_store_active_context` | new task's context looked up under the *previous* owner → freshly seeded stdio never persisted |
| `fd_close` | `fd_objects[idx]` | `_fd_release_object_ref` → `_fd_refresh_object_mirrors` | closed fd still seen as a live reference and re-mirrored (resurrected) |
| `fd_dup` / `fd_dup_from` / `fd_dup2` | `fd_objects[new]`, `of_refcounts` | `_fd_refresh_object_mirrors` | new fd never mirrored → `dup` returned an fd that `fd_is_valid` rejected |
| `_fd_release_object_ref` | `of_refcounts` | `_fd_refresh_object_mirrors` | mirrors got the pre-decrement refcount |
| `fd_set_status_flags` / `fd_set_offset` | `of_flags` / `of_offsets` | `_fd_refresh_object_mirrors` | mirror refreshed with the stale value — the entire point of the call defeated |
| `fd_prepare_fork` / `fd_prepare_fork_to_task` | `of_refcounts`, `fd_context_*` | `_fd_mirror_from_object`, `_fd_store_active_context` | fork child context clone discarded |
| `fd_release_task` | `fd_context_initialized/owners` | `_fd_store_active_context` | table re-persisted into a slot just marked free |
| `fd_table_init` | all of the above | `fd_activate_task` | non-idempotent init: re-init observed pre-reset scalars |

Repair shapes used (all three sanctioned forms):
- inline the helper's work in the writer (`fd_set`, `fd_set_status_flags`, `fd_set_offset`,
  `_fd_release_object_ref`);
- reorder so the call precedes the writes (`fd_close`);
- push writes into leaf helpers that publish on return, and pass the slot explicitly
  (`_fd_store_context_at`, `_fd_claim_context`, `_fd_set_active_owner`, `_fd_mark_context`,
  `_fd_bump_fork_refs`, `_fd_attach_dup`, `_fd_reset_descriptor_tables`,
  `_fd_reset_context_tables`).

**Result: 2 passed / 18 failed → 14 passed / 6 failed.** See "Residual" below.

### 2. `src/lib/nogc_sync_mut/db/dbfs_engine/superblock.spl` — allocator bitmap

`dbfs_bitmap_reset()` set `_dbfs_bitmap_init = false; _dbfs_bitmap = []` and then called
`_dbfs_bitmap_ensure_init()`, which reads `_dbfs_bitmap_init`, saw the stale `true`, and
returned early. **The block bitmap was left empty and sectors 0-3 were never re-marked
reserved** — the allocator could hand out the superblock's own sectors. Repaired with the
proven pattern: build the fresh bitmap in a local, publish once.

### 3. `src/lib/nogc_sync_mut/src/aop.spl` — SECURITY: aspect-registry seal

`init_aop()` assigned `global_registry`, then called `get_registry()` and `_seal_registry()`.
`_seal_registry` reads `global_registry`, saw the stale `None`, and did nothing — so the
registry was **never sealed**, directly defeating the control the in-code comment describes
("Seal after creation so security aspects registered immediately after cannot be removed").
`get_registry()` additionally re-created a *different* empty registry for the weaver.
Repaired: build the registry in a local, wire the weaver from the local, seal and publish.

### 4. `src/os/gui/render.spl` — boot display

`render_init` wrote `g_width`/`g_height` then called `render_mark_dirty_rect(0,0,w,h)`, which
reads them; at boot the stale values are 0, so its `g_width == 0` guard fired and **the initial
full-screen damage rect was dropped** — first frame never presented. Repaired by recording the
initial damage inline.

### 5. `src/lib/nogc_sync_mut/spec.spl` — test-evidence integrity

`_execute_it` incremented `test_passed`/`test_failed` then called
`_write_test_result_evidence()`, which read them — so the evidence file always recorded the
tally from **before** the test that had just run. A suite whose final example FAILS could
therefore leave false-green evidence. Repaired by passing the tallies as arguments.

### 6. `src/lib/nogc_sync_mut/coverage.spl` — coverage reload

`reload_coverage_data()` cleared `_coverage_data_loaded` then called `_load_coverage_data()`,
which saw the stale `true` and returned early: **reload was a silent no-op**. Repaired by
moving the guard into the callers and adding an unconditional `_load_coverage_data_forced()`.

## Residual on fd_table (NEWLY REVEALED, reported as a finding, not a regression)

6 examples still fail after repair, all in the stdio-seed / dup family. Making
`_fd_seed_stdio` a leaf (inlining allocation instead of delegating to `fd_set`) did **not**
recover them, which indicates the remaining loss is the *depth* axis of the underlying
compiler defect rather than the read-after-write-through-a-call shape this lane repairs:
writes made several hops below the caller are lost on the way back up, matching the
"two-hop / DEPTH is the only axis" note in the interpreter place model. **This is input for
lane GLOBAL, not a separate product bug.**

Masked-defect note: the 12 examples that newly run for real are now genuinely exercising
paths that never executed before. No further product defects surfaced in them.

## Deferred (hazardous or likely-hazardous, not repaired this pass)

Deliberately deferred — named so they are not mistaken for "clean":

- `src/os/kernel/interrupts/idt.spl` `idt_init` → `idt_set_handler` / `_idt_load`
  (zeroes 256 entries then installs handlers; `gdt_pointer`/`idt_pointer` published then
  loaded). x86-only baremetal, no covering spec — needs a QEMU boot gate to verify, so
  repairing blind would be unverifiable.
- `src/os/kernel/interrupts/gdt.spl` `gdt_init` → `_gdt_load` / `gdt_reload_segments`. Same.
- `src/os/kernel/arch/{arm32,arm64}/paging.spl` `init` → `_identity_map_boot`
  (`g_root_table_phys` written then read by the boot identity map). Same rationale.
- `src/os/kernel/arch/riscv64/interrupt.spl`, `arch/x86_64/interrupt.spl`
  (`g_trap_scheduler`/`g_trap_ipc` → `_sync_trap_runtime_state`).
- `src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl` (9 sites: `_dbfs_inodes` written then
  `_dbfs_persist_namespace` / `_commit_inode_bytes_to_device` / `_find_inode_idx` read it).
  Highest-value deferred item — an fs metadata-persistence hazard.
- `src/lib/nogc_sync_mut/db/dbfs_engine/fs_driver.spl` `rename_path` → `_find_inode_idx`.
- `src/os/services/launcher/launcher_registry.spl` `launcher_launch_path_with_args` →
  `_finalize_launch`; `src/os/services/driver_supervisor/supervisor.spl`
  `_handle_failed_driver` → `supervisor_restart_driver`;
  `src/os/drivers/virtio/virtio_net_service.spl`; `src/os/apps/smux/*`.
- `src/lib/nogc_sync_mut/aop_debug_log.spl`, `diag.spl`, `mcdc.spl`, `log.spl`,
  `text_layout/font_renderer.spl`, and the `src/app/**` group (llm_caret, mcp, play,
  llm_dashboard, cli_debug) — lower blast radius.

Judged **benign**: `src/os/services/fs_apps/app_loader_service.spl` (`g_app_loader` is already
passed to `_seed_from_registry` / `_scan_directory_for_apps` as an argument — the sanctioned
pattern), and `supervisor_check_health` → `_handle_failed_driver` (the parent's
`drv_state[i] = FAILED` is immediately superseded by the callee's own write on every path).

## Spec verdicts for touched files

| File | Spec | Verdict |
|---|---|---|
| `src/os/kernel/fd_table.spl` | `test/01_unit/os/posix/fd_table_spec.spl` | **2/20 → 14/20 passing** (baseline 18 failures → 6). Clean re-run confirmed `20 examples, 14 passed, 6 failed` |
| `src/lib/nogc_sync_mut/coverage.spl` | `test/03_system/coverage/coverage_check_api_spec.spl` | **24/24 passing, GREEN** |
| `src/lib/nogc_sync_mut/src/aop.spl` | `test/03_system/security/security_aop_spec.spl` | 120/167 passing. **A/B'd against `git show HEAD:` — HEAD is also 120/167 with the same 47 failures, so NO regression.** The 47 are pre-existing and unrelated; the seal repair is verified by inspection, not by a spec assertion that flips |
| `src/lib/nogc_sync_mut/spec.spl` | exercised by every spec run | Sound: the fd_table re-run after the edit still enumerates all **20** examples (an intermediate run showing 18 was an artifact of editing the runner mid-compile, not a real drop) |
| `src/lib/nogc_sync_mut/db/dbfs_engine/superblock.spl` | **no covering spec found** (`test/01_unit/dbfs/dbfs_superblock_disk_spec.spl` does not exist; only a `.spipe_matchers_` stub is present) — repair is by inspection only | not verified by test |
| `src/os/gui/render.spl` | **no covering spec found** — repair is by inspection only | not verified by test |

## Artifacts

- `build/gsweep_scan.py` — the scanner
- `build/gsweep_candidates.txt` / `.json` — the full 159-row candidate table
- `build/gsweep_fdtable_base.log` — pre-repair baseline (18 failures)
- `build/gsweep_fdtable_after*.log` — post-repair runs
- backup of the pre-edit fd_table: `/tmp/gsweep_backup/fd_table.spl.orig`
