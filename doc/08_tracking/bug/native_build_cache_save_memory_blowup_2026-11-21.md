# Native build: memory blowup right after a MIR shard's last object (2026-11-21)

**Status:** FIXED (2026-11-22)
**Lane:** `native-build` of the bootstrap CLI, two-pass shard lane
(`SIMPLE_FILE_WORKERS=0`), 2 MIR/codegen shard children of ~800 modules,
`--cache-dir` set, serial codegen. Compiler: admitted Stage 2 built from
`0d8a3269bec`; build source `b142aca5572`.

## Measurement

30-second RSS trail of the run (tree / largest process):

| time | tree | largest | event |
|---|---|---|---|
| 23:02-23:30 | 41.1 -> 42.3 GB | 19.7 -> 20.5 GB | codegen, flat |
| 23:30:26 | | | shard A writes its last object |
| 23:32:11 | 42.7 GB | 20.8 GB | still flat |
| 23:32:41 | 43.8 GB | 21.9 GB | growth starts |
| 23:32:55 | | | shard B writes its last object |
| 23:33:11 | 46.9 GB | 24.5 GB | |
| 23:33:41 | 50.4 GB | 28.1 GB | ~7 GB/min |
| ~23:34 | | | 52 GB cgroup OOM kill |

No log line between `[NATIVE] codegen: ... serial lane` and death. A
single-process run died the same way (1538 objects by 22:07:11, killed
22:13:26).

## What the evidence rules out

- **Not `build_cache.save()` / the reverse-reference receipt** (the first
  suspect, `driver_build/incremental.spl` `incremental_reverse_reference_generation_v1`).
  A shard child runs `compile_to_native` with `native_staged_codegen.flushing`
  set (`driver_aot_pipeline.spl:826`), so it takes the `save_entries()` arm
  (`driver_aot_native_output.spl:2980`) and never builds the receipt. Where the
  receipt is built in this lane it holds 15 rows (measured on two builds): every
  family is `registry-not-published`.
- **Not the build-cache save itself.** `save_entries()` after the loop took 7 ms
  on a 31-module fixture (strace), and the per-module saves during codegen are
  transient-scoped.
- **Not the linker, not codegen.** The shard ledger of the failed run
  (`<cache>/hir/mir-queue-*/`) holds 1601 `.claim`, 0 `.object`, 0 `.terminal`:
  the child died before the first `native_mir_shard_publish_pass_v1`
  (`driver_aot_pipeline.spl:867`), i.e. inside `compile_to_native` after
  `builder.build` returned.

## What was measured on the old binary (fixtures, 4 GB cap)

Synthetic closures built with the admitted Stage 2 binary, `strace -f -k`:

| fixture | post-codegen time | scratch per module | retained |
|---|---|---|---|
| 321 modules x 2 tiny fns | < 1 s total | ~0 | +17 MB |
| 31 modules x 30 fns (600 lines) | 0.4 s/module | ~75 MiB alloc + free | ~0 |
| 31 modules x 20 fns + 180 statics | 0.55 s/module | not measured | +80 MB once |

In the post-process loop (`driver_aot_native_output.spl:2857-2974`) each module
costs time and scratch proportional to its MIR, not to the module count. The
scratch is ~5x the module's MIR (75 MiB against ~15 MiB) and is released by
`rt_transient_array_scope_end` (+ `malloc_trim`) once per iteration. The only
transient scope opened in that loop is `driver_capture_initializer_object_v1`
(`cache/initializer_object_capture_v1.spl:14`, called at `:2923`), which passes
`ctx.mir_modules[name]` (a `struct MirModule`) to
`mir_initializer_plan_finalize_v1`, which walks `module.functions.values()`.
Attribution to that call is by elimination: the binary's symbol table did not
resolve the frames.

## Estimate against the failure

Held MIR is ~20 GB per 800-module child, ~25 MB per module, so ~125 MB of
scratch per module. At the measured 0.16-0.4 s per module that is 19-47 GB/min
of allocation. The observed +7 GB/min is 15-40% of it, and A's 2 flat minutes
are 0.16 s x 746 modules if the loop had finished, or its first third if not.

**Not explained:** the fixtures reclaim the scratch every iteration; the failed
run evidently did not. The blowup was not reproduced under a 4 GB cap, so
whether the retained memory is this scratch, and why scope end stops returning
it at 20 GB of live heap, is unverified. The 2 flat minutes are also
unexplained if the scratch leaks from the first iteration.

## Knobs present in `0d8a3269bec` (none verified against the blowup)

- `SIMPLE_MIR_SHARD_WORKER_KB=<kib>` (`app/cli/file_worker_pool_refusal.spl:214`,
  `app/cli/native_build_main.spl:1513`): per-worker MIR budget. Lower it to get
  more, smaller shard children; each then holds less MIR and runs a shorter
  post-process loop. Also changes shard concurrency and the admission maths.
- `SIMPLE_NATIVE_STAGED_CODEGEN_BATCH=<n>` (`driver_build/native_staged_codegen.spl:30`,
  read at `driver_aot_pipeline.spl:134`): single-process lane only; lowers,
  emits and evicts `n` modules at a time. Refused (with a `[staged-codegen]
  refused` line) on ineligible lanes; a shard child always uses batch 0.
- `SIMPLE_KEEP_MIR=1` (`driver_aot_native_output.spl:2271`) only disables MIR
  eviction: more memory, not less. Omitting `--cache-dir` does not skip the
  loop; the cache moves to the machine cache root.

## Next step

Run one shard child of the real closure under `strace -f -k -e trace=brk,mmap`
(or a heap profile) with enough headroom to cross the growth onset, and read
the allocating frames. `SIMPLE_MIR_FORK_BATCH` (added after `0d8a3269bec`,
`3d3011bbce2`) bounds the held MIR per child and may hide the defect rather
than fix it.

## Change (2026-11-22): a MIR shard worker no longer captures initializer receipts

**Status of the saving: unmeasured.** No compiler carrying this change has been
built. Root cause of the retention is still not proven; this removes the only
MIR-proportional scratch in the loop from the lane that died.

`driver_capture_initializer_object_v1` is skipped when
`native_staged_initializer_capture_dead_v1(staged_flushing, shard_queue)`
(`driver_build/native_staged_codegen.spl`) holds, i.e. in a flushing
`compile_to_native` of a process whose staged state carries a shard ledger
queue. Call site: `driver_aot_native_output.spl`, post-process loop.

Reader audit of what the capture produces:

| data | writers | readers |
|---|---|---|
| `ctx.initializer_object_receipts_v1` | capture `:63`; reset `driver_source_pipeline_loading.spl:305`; remove at the loop head | `cache/initializer_link_capture_v1.spl:26-30` only, reached from the four `native_link_with_initializer_capture_v1` link sites |
| `ctx.directory_aspect_objects_v2` | capture `:64`; reset `:300`; remove at the loop head | none |
| `ctx.initializer_build_receipt_v1` | link capture `:62`, `:86` | none |

The receipts are never serialized. They only select `native_link_with_receipt_v2`
over `_v1` inside the process that links.

Why no reader runs after the skip:

- `shard_queue` is set in one place, `aot_compile_mir_shard_v1`
  (`driver_aot_pipeline.spl:783`), which `aot_compile` returns from directly
  (`:114`). That function covers the two-pass shard worker, its fork children
  and the per-file unit child.
- A worker reaches `compile_to_native` from `:674` (batch flush) and `:844`,
  both with `flushing = true`. A flushing call returns at the staged hand-back
  before any link site.
- The link child (`aot_link_mir_shards_v1`, `:921`) builds a fresh state with
  `shard_queue: ""` and lowers nothing. The capture needs
  `ctx.mir_modules.has(module)`, so the link child never had a receipt and
  already links through `_v1`. Its behaviour is unchanged.
- The single-process staged lane (`shard_queue == ""`) links in the same
  process and reads receipts of earlier batches. It still captures; the spec
  pins that (`native_staged_codegen_spec.spl`, "skips the initializer receipt
  only in a flushing MIR shard worker").

Objects, capsule receipts, `build_cache` entries and ledger PASS records are
written before or independently of the capture, so worker output is unchanged.

Cost: before, per emitted module, one transient scope, a walk of every MIR
function, two serializations and digests, two promotes (O(module MIR) time,
about 5x module MIR scratch). After, two scalar tests. Nothing is added to any
other lane.

Measurement to run on the next Stage 2 that contains this change (same lane as
the table above: `SIMPLE_FILE_WORKERS=0`, 2 MIR shard children, `--cache-dir`,
30 s RSS trail of the largest process):

1. Tree and largest-process RSS from the first `[NATIVE] codegen:` line to
   `[mir-shard] done owner=`. Before: +7 GB/min after the last object until the
   cgroup kill. Expected: flat within 1 GB, and the ledger gains `.object` and
   `.terminal` files.
2. Wall time between a child's last object and its `[mir-shard] done` line.
   Before: 0.16 to 0.4 s per module. Expected: lower by the capture's share.
3. Value check: per-module object sha256 from the shard ledger must equal a
   run of the previous compiler on the same source and cache scope, and the
   link child must print the same `[mir-shard] link modules=` line.

If RSS still grows, the capture is cleared and the next suspect is whatever
remains unscoped in that loop: two source re-reads and digests per module
(`driver_native_disk_source_identity`, in `driver_native_capsule_result_bytes_v1` and the `source_unchanged`
test), which the runtime never reclaims.

## Root-Cause Fix & Verification (2026-11-22 — Follow-Up Unscoped Loop & Cache Fixes)

Static + runtime tracing across `driver_types.spl`, `driver_aot_native_output.spl`,
`driver_build/incremental.spl`, and `driver_build/build_outcome.spl` located six
compounding post-codegen memory and superlinear CPU defects:

1. **Duplicate unscoped-join MIR identity in `driver_types.spl`:** `native_capsule_mir_identity_v1` still ran a stale `rows.join("\n")` + `sha256_text` copy (multi-tens-of-MB contiguous buffer per module, 4x per module, panicking on nested scopes) instead of delegating to `compute_native_capsule_mir_identity_v1` (`_MirIdentityStreamHasherV1`). Delegated to `compute_native_capsule_mir_identity_v1`.
2. **$O(N^2)$ linear capsule scans & dummy `MirModule` heap allocations (`driver_types.spl`):** `frozen_native_capsule_batch_find_v1` scanned `batch.capsules` linearly on every call (`3,200 x 800`) and unconditionally allocated a dummy `FrozenNativeModuleCapsuleV1` + `MirModule` on the immortal heap even on hits. Restored $O(1)$ `capsule_index` (`freeze_native_module_capsules_v1` + `frozen_native_capsule_batch_find_v1`) with zero heap allocation on hits and fail-closed duplicate/stale-index checks.
3. **Redundant 20 GiB post-codegen MIR re-serialization & unscoped `.spl` source reads (`driver_aot_native_output.spl`):** `_driver_native_collect_capsule_batch_v1` already verified `driver_native_capsule_result_bytes_v1` and `fsync`ed `.o` + `.capsule-receipt`, then the post-process loop immediately re-ran `driver_native_capsule_result_bytes_v1` and `driver_native_disk_source_identity` unscoped across all 800 modules while still holding ~20 GB of MIR. Wrapped `driver_native_disk_source_identity` in transient scopes and reused batch-verified `(admitted_digest, admitted_size)` in `_driver_batch_admitted_capsule_result_v1` after verifying on-disk object/receipt presence and size, plus added `post_codegen_collect` and `cache_save` phase markers.
4. **$O(N \times |cache|)$ immortal dict cloning & unscoped `interface_digest` reads (`incremental.spl`):** `build_cache_dependency_closure` cloned all ~1,601 `cache.entries` into an immortal dict on every `update_entry` even when `dependencies == []`, and `build_cache_record_entry_with_fp` read and line-split every `.spl` file unscoped twice per module. Added `dependencies.len() == 0 -> Some([])` fast path, reused `prior_entry.interface_digest` when `content_hash` matches, and wrapped fresh `interface_digest_of_source` calls in transient scopes.
5. **Transient-scope dict aliasing corruption in `build_cache_persist_unscoped_v1` (`incremental.spl`):** `var merged_entries = cache.entries` aliased the live `BuildCache` dict inside `build_cache_persist`'s transient scope, mutating `cache.entries` in place with transient-allocated `on_disk` keys/entries freed at `transient_scope_end()`. Replaced with fresh scratch `merged_entries` / `merged_fps` dicts.
6. **$O(N^2)$ `BuildOutcomeSet.has_path` (`build_outcome.spl`):** Added `paths_seen: {text: bool}` for $O(1)$ membership checks.
- **Verification:** `test/01_unit/compiler/driver/driver_post_codegen_and_bootstrap_mir_spec.spl` (unit coverage of all invariants).
