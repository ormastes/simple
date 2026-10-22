# Stage-2 sanity rejects every self-hosted candidate: SCV snapshot entry collects zero sources (2026-10-22)

**Status:** OPEN — blocks all Stage-2+ bootstrap on `release_phase3` (observed at `84841547934`).
**Impact:** `bootstrap-from-scratch.sh --full-bootstrap` cannot pass the Stage-2
frontend sanity; the Stage-2 binary is rejected, Stage 3/4 unreachable.
**Severity:** release-blocking for the phase-4 full-CLI goal.

## Symptom

Stage 2 native build succeeds (`1482 compiled, 0 cached, 0 failed`, 946 s), then
the wrapper's pinned frontend sanity fails both passes:

```
error: compiler entry 'src/compiler/bootstrap_admission/p2_add.spl' collected zero source files:
  the entry must be a path to a .spl file ... and the path is resolved relative to the current working directory
candidate_frontend_smoke: p2_add-build failed (raw rc=1)
bootstrap-sanity-error: version_status=0 version_output=simple-bootstrap 1.0.0-rc.1 unsupported_status=1 frontend_status=1 candidate_unchanged=true
```

Evidence set (lane attempt 3, 2026-10-22 ~09:16):
`.simple/storage/build/bootstrap/stage3/x86_64-pc-windows-msvc/stage2-sanity.env.frontend-{driver,failure}.log`,
rejected binary preserved at
`.simple/storage/build/bootstrap/stage2/x86_64-pc-windows-msvc/simple.exe.rejected`.

## Reproduction (no lane required)

With the SCV inventory present (`build/scv/source-inventory/CURRENT`, published by
the sanity's own scv_prime step — i.e. the failure is inherent to the sanity flow,
not this checkout's state):

fails in ~5 ms at `phase 1 load_sources`. The same command against the Rust seed
(`bin/simple`, tracked rc.1 binary) passes load_sources and compiles.

## Root-cause refinement (same session, turn 2) — READ THIS FIRST

The SCV snapshot path is a RED HERRING. The actual defect is narrower and
worse: **the self-hosted bootstrap binary cannot read ANY absolute path** —
the snapshot rewrite merely happens to be the thing that feeds it absolute
paths.

Matrix against the preserved rejected Stage-2 binary
(`simple.exe.rejected`, `compile --format=smf <path>`), repo root cwd:

| Entry form                                  | Candidate | Seed |
|---------------------------------------------|-----------|------|
| `src/compiler/bootstrap_admission/p2_add.spl` (relative) | OK (scv_prime proved this at 09:15) | OK |
| `D:\dev\simple\src\...\p2_add.spl` (abs, backslash)      | FAIL | OK |
| `D:/dev/simple/src/.../p2_add.spl` (abs, fwd slash)      | FAIL | OK |
| `C:\Users\...\Temp\p2_short.spl` (abs, short, backslash) | FAIL | OK |
| `C:/Users/.../p2_short.spl` (abs, short, fwd slash)      | FAIL | OK |
| `C:\...\scv-revision-v1-<64hex>\...\p2_add.spl` (long)   | FAIL | OK |

So: relative works, absolute fails, in the SELF-HOSTED binary only; length,
separator style, and directory are irrelevant. The SCV flow is broken only
because it rewrites the entry to an absolute snapshot path
(`driver_source_pipeline_loading.spl:343-392`).

## Suspect chain (candidate-side file open)

`_driver_collect_explicit_compiler_source` (`driver_source_loading.spl:1662`)
→ `_driver_cached_entry_source_scan` (`:825`) → `file_read_nullable`
(`src/lib/nogc_sync_mut/io_runtime.spl:198`) → `file_read_result` →
`FileTextSession.open` (`src/lib/nogc_sync_mut/io/file_text_session.spl:156`):
`io_file_open(host_path_native(path), mode_int)`.

- `host_path_native` (`src/lib/nogc_sync_mut/fs/host_path.spl:155`) is correct
  by inspection for absolute paths (drive passthrough, separator flip,
  `_host_long_path` only past 247 chars).
- `io_file_open` (`src/lib/nogc_sync_mut/sffi/fs.spl:300-309`) borrows
  `rt_string_data(path)` + `rt_string_len(path)` and calls
  `rt_io_file_open(address, count, mode)`.
- `rt_io_file_open` (`src/runtime/runtime_native.c:12281`) copies the bytes
  verbatim (`rt_text_arg_to_path`, `:11669`) and calls `_open`. No absolute-path
  special-casing anywhere — yet absolute opens fail only under the self-hosted
  core-c-bootstrap runtime.

Most probable: a text-ABI/retention difference — `rt_string_data` on a string
produced by the absolute-path route (or `host_path_native`'s replace chains on
drive-letter input) returns a bad pointer/length under the self-hosted text
ABI, so `_open` sees garbage and returns ENOENT. Relative paths never exercise
the drive-letter/separator-flip code shape. Verify with a native probe that
calls `rt_io_file_open` directly on both spellings under the core-c runtime
before touching the C.

The stage-2 candidate is built with `--runtime-bundle core-c-bootstrap`
(transcript: `.simple/storage/build/bootstrap/stage3/x86_64-pc-windows-msvc/stage2-command.transcript`),
so the defect lives in the core-c/runtime_native layer or its text-ABI
registry — the seed's Rust-hosted runtime (`env_process.rs` /
`io_file.rs`) does not show it.

## Evidence chain

1. `SIMPLE_COMPILER_TRACE=1` shows the pipeline received ONE input, rewritten to a
   snapshot path:
   `phase1:load_sources:input:start index=0 path=D:/dev/simple/build/scv/snapshots/scv-revision-v1-28f7afe6.../src/compiler/bootstrap_admission/p2_add.spl`
   then `input:done index=0 loaded=0 total=0` → zero-source gate fires
   (`src/compiler/80.driver/driver_source_pipeline_loading.spl:950-951`).
2. `SIMPLE_NATIVE_BUILD_TRACE_CLOSURE_SCAN_PHASES=1` shows the scan itself RAN for
   the snapshot path: `read:start` → `read:done` → `imports:done` →
   `siblings:done` → `cached_scan:done` → `closure_node:scanned`, then
   `cached_scan:hit` on rescan. So `_driver_cached_entry_source_scan`
   (`driver_source_loading.spl:825`) completed, yet
   `_driver_collect_explicit_compiler_source` (`driver_source_loading.spl:1662`)
   still yielded zero sources — i.e. after `read:done` the collected content was
   empty or the alias list came back empty **only in the self-hosted binary**.
3. The snapshot file exists, is a plain 487-byte ASCII file, and the SEED compiles
   the identical snapshot path successfully:
   `bin/simple compile --format=smf D:/dev/simple/build/scv/snapshots/.../p2_add.spl`
   → `Compiled ... -> t4.smf`. The candidate's own `compile --format=smf` on the
   same absolute snapshot path fails identically at load_sources.
4. p2_add.spl has NO imports, so import-closure resolution cannot explain zero
   aliases; the entry file itself is what fails to materialize as a SourceFile.
5. The rewrite is conditional on `SIMPLE_PACKAGE_INDEX_COLD_INIT` (set in-process
   by the probe) plus `SIMPLE_SCV_SNAPSHOT_ROOT` (set by the native-build
   entrypoint: `src/app/compiler_entrypoint/source_authority.spl:175` and
   `src/app/cli/native_build_warm_receipt.spl:383`), executing
   `driver_source_pipeline_loading.spl:343-392` →
   `native_cold_entry_snapshot_path_v1` + `phase_compatibility_existing_artifact_io_v1`
   admit the snapshot copy, so `cold_entry_input = admitted.canonical_path`.

## Localization

- Rewrite: `src/compiler/80.driver/driver_source_pipeline_loading.spl:343-392`.
- Zero-source gate: same file, lines 950-953.
- Scan that returns empty/alias-less for the snapshot path ONLY under the
  self-hosted binary: `src/compiler/80.driver/driver_source_loading.spl:825-870`
  (`_driver_cached_entry_source_scan`) and `:1662-1670`
  (`_driver_collect_explicit_compiler_source`).
- Suspect: a self-hosted-only behavioral difference in the sosix file-read layer
  or the module-identity/alias path for `build/scv/snapshots/...` paths
  (`_driver_physical_module_identity`, `driver_admitted_epoch_normalize_v1`-style
  normalization). The admitted-epoch read path was checked and excluded: with an
  active epoch and no task, load_sources fails loudly at
  `driver_source_pipeline_loading.spl:206-208`, which is NOT the observed error.

## Notes for the fixing lane

- The sanity is DESIGNED to create this state (scv_prime publishes the inventory,
  then the p2_add probe re-runs the candidate, which rewrites to the snapshot), so
  no in-lane workaround exists; the candidate must read snapshot paths correctly.
- Rebuild cost per fix attempt: Stage-2 native build ~16 min + lane overhead;
  the repro above gives a 5-second signal without a lane.
- Seed comparison is meaningful only with identical env: the seed's JIT demotion
  on the full CLI (`bin/simple`) prints jit-fallback noise but does pass
  load_sources for both the working-tree and snapshot entry paths.

## Update 2026-10-22 (second session)

Fix attempts and evidence gathered after the initial filing:

1. **cdb kernel-level proof (both old and rebuilt candidates)**: breaking on
   `ntdll!NtCreateFile` during the failing repro shows the snapshot path is
   NEVER opened at the kernel (14 opens captured, none for the entry), while
   absolute-path WRITES (SMF output, cache `BLOCKED` markers) succeed. The read
   failure is entirely userland, before `_open`.
2. **Instrumentation landed in `io_file_open`** (`src/lib/nogc_sync_mut/sffi/fs.spl`):
   a guard print of the raw operands fires when `rt_string_len`/`rt_string_data`
   fail to decode the path value. **The print never appears** even when the
   guard must have fired → `eprint` is silently inert in the core-c-bootstrap
   candidate (C-level stderr works; Simple-level `print` works). Any future
   in-candidate diagnostics must use `print`, not `eprint`.
3. **Concat re-materialization fallback** (`path + ""` then retry) does NOT
   rescue the read: same zero-source outcome with no kernel open. The bad value
   is undecodable by the whole text-ABI family (`rt_string_len`,
   `rt_string_data`, and via `rt_to_string` in `rt_string_concat`), only
   language-level interpreter ops see it. The fallback remains in-tree
   (bug-linked, zero hot-path cost) but is not a fix.
4. **Seed aggregate-typing flake** (separate defect exposed by any source
   edit shifting TypeIds): `safety_alias_join` failed deterministically with
   `cannot infer field type ... struct 'ANY' field 'owner_id'` once module
   numbering shifted. Fixed by rewriting the dict iteration as key iteration
   (`for key in first.keys()` + annotated `first[key]`/`second[key]` bindings),
   which the seed infers robustly. Stage-2 now compiles 1485 modules, 0 failed.
5. Net: Stage-2 builds clean with the fixes in, but the pinned frontend
   sanity still rejects the candidate at the zero-source gate. The remaining
   defect is in the self-hosted string representation/ABI (candidate-produced
   text values for absolute paths don't decode under `rt_string_len`/
   `rt_string_data`), i.e. runtime C string-tag territory — see
   `runtime_native.c` `rt_core_as_string` / `rt_string_len` / `rt_to_string`.
   Suspect the tagged-value form produced for these strings by the candidate
   codegen differs from `RT_VALUE_TAG_HEAP` expectations, so every ABI decoder
   misses and the `>= 0x10000` bare-pointer fallback also fails (negative or
   small tagged value).

## Update 2026-10-22 (third session) — text-extern ABI registry is the prime suspect

Deeper findings; the runtime-C string code checks out by inspection
(`rt_string_new` tags with `RT_VALUE_TAG_HEAP` (0x1) and registers;
`rt_core_as_string` decodes tag + registry), so the mis-tagging is not in the
runtime C constructors. The defect class points at the compiler-side
text-extern ABI registry instead:

- `src/compiler/50.mir/text_extern_abi.spl` carries the table that decides,
  per extern name, which `text` operands are expanded to (ptr, len) and which
  stay single tagged words. Its own comments document the exact hazard class:
  - line 110-111: **"the existing r17 producer retains its old table until
    rebuilt; binaries it emits do not qualify this edited registry"** — the
    Rust seed IS such an old producer, so EVERY candidate it compiles embeds
    the seed's stale table.
  - lines 107-109: a missing `rt_io_file_open` row "sent read mode zero as
    path length" (fixed 2026-10-21) — a call silently receiving the wrong
    operand shape produces precisely our symptom: open of an empty/garbage
    path fails before the kernel, read returns nil, zero-source gate fires.
  - lines 231-241: `rt_file_write_text_at` analog — raw char* delivered where
    a tagged handle was expected; `rt_core_string_to_cpath` rejects with
    "tag 0 != heap". Same class, write side, already fixed.
- `rt_path_absolute` (row at line 146) is exercised by the SCV snapshot
  admission and its result (`admitted.canonical_path`) is exactly the value
  the failing entry read consumes. Verify the SEED's embedded table row for
  `rt_path_absolute` and `rt_io_file_open` against the current source table:
  a stale/missing row in the seed-produced candidate would make the snapshot
  canonical path (or the read call) silently malformed while relative
  (working-tree) entries never route through those externs.
- Note the `io_file_open` wrapper in `sffi/fs.spl` passes three i64 operands
  (no `text` at the extern), so the table does NOT govern that wrapper's own
  expansion — the stale-table suspect applies to the DIRECT externs in the
  path pipeline (`rt_path_absolute`, `rt_file_exists` siblings, the
  `rt_dir_*` probes), not to the wrapper.

Next diagnostic step (one Stage-2 rebuild): change the `io_file_open` guard
diagnostic from `eprint` (proven inert in the core-c candidate) to `print`
(stdout works — `[BOOTSTRAP-PHASE]` traces prove it) and dump
`count/address/lang_len/path` at the failure; that distinguishes "guard fired,
value undecodable" from "open reached with garbage pointer and UCRT rejected
it before CreateFileW" (the current leading theory: `ucrtbase!_open` fired
exactly once in a full failing run with `rcx = -1`, consistent with wide
parameter validation failure and no kernel transition).
