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

## Update 2026-10-22 (Linux aarch64 lane): fixed by restoring the two-arg text ABI

This lane's evidence chain (below) diagnosed "the value is undecodable by the
whole ABI family" while retaining the raw three-word `rt_io_file_open` form.
A parallel experiment on the same defect class reached a different conclusion:
the SEED-side `rt_io_file_open(path: text, mode: i64)` declaration is expanded
to the three-word C ABI by the compiler's text-ABI registry
(`src/compiler/50.mir/text_extern_abi.spl`: split row `[0]`, semantic arity 2),
and with that two-arg form the seed interpreter reads the exact fixture bytes
(487/487) and the fresh stage2 candidate's driver collects the entry
(load_sources succeeds, parse phase reached). The raw
`(path_ptr, path_len, mode)` declaration from 9bb344bb1cf bypasses that
expansion and was observed broken on BOTH producers (interpreter: operand-shape
mismatch, fd=-1 for every path; native candidate: every driver file read empty).

Landed fix: 5eccf04d3f0 restores the two-arg declaration and removes the raw
ABI block (superseding the concat-retry fallback of 83548ce08dd, whose own
message concedes it "does not rescue the read"). Companion fixes on the same
lane: 3d407765f1e (rt_transient_heap_promote class-0 exemption now accepts any
registered-immortal object — fixes the SIGABRT "transient retained parser
ownership failed" that surfaced once entry collection worked) and 7265bfe0a11
(runtime build.rs now watches the whole `../../runtime` tree; runtime_native.c
had no rerun-if-changed row and edits to it silently never rebuilt).
If the zero-sources symptom still reproduces after this stack, the next
suspects are the ones named below; otherwise this doc's OPEN status can move
to FIXED pending the full sanity PASS receipt.

## Update 2026-10-22 (Windows lane): STILL REPRODUCES after the two-arg fix

Lane attempt 9 on this host rebuilt the Rust seed and Stage-2 candidate on
`848d89ed504` (5eccf04d3f0 + companions integrated, caches invalidated) and
the pinned sanity failed with the BYTE-IDENTICAL error:

- Stage-2 compile: `rebuilt 1485`, 0 failed.
- Sanity: `compiler entry 'src/compiler/bootstrap_admission/p2_add.spl'
  collected zero source files` (both passes), rejected binary preserved at
  `.simple/storage/build/bootstrap/stage2/x86_64-pc-windows-msvc/simple.exe.rejected`.
- 5-second repro against that fresh rejected binary reproduces identically.

So on the Windows self-hosted native path the two-arg ABI restore did NOT
make the candidate's driver collect the entry, contrary to the Linux-lane
evidence ("load_sources succeeds, parse phase reached"). Either a second
operand-shape defect remains on this path (the cdb findings above still
hold: the entry open never reaches `NtCreateFile`; `ucrtbase!_open` fired
once with `rcx = -1`), or the Windows candidate build did not actually pick
up the restored declaration (the 7265bfe0a11 build.rs watch fix was in this
rebuild, so the runtime C did recompile). Next diagnostic: the `print`-based
`io_file_open` guard dump (eprint is inert in the core-c candidate) to see
the exact operands on this path, then compare the emitted call shape against
`text_extern_abi.spl`'s table for the current seed producer.

## Update 2026-10-22 (late session, lane attempts 10-13): actual read path identified

Three decisive findings from the diagnostic lanes:

1. **The candidate's driver read does NOT go through `rt_io_file_open` /
   `rt_io_file_read_all`.** Ungated C diagnostics in both (failure + the
   487-byte p2_add fixture success marker) are embedded in the candidate
   (verified via `strings`) yet never print. The actual implementation on
   this path is `rt_file_read_text` (`runtime_native.c:12673`) — a
   `fopen(path, "rb")` + `fread` + `rt_string_new` provider that exists
   precisely because the core-c-bootstrap bundle links runtime_native.c and
   NOT runtime.c. Its table row (`text_extern_abi.spl:86`, `Some([0])`) is
   present in BOTH the pure-Simple and Rust (`calls.rs:3162`) registries,
   but the diagnostics placed so far never touched THIS function — instrument
   `rt_file_read_text` next (fprintf on `fopen` failure + `errno` + path
   bytes).

2. **The single `NtCreateFile` hit for the scv-revision path was a metadata
   probe, not a content read.** `rt_file_exists` uses `GetFileAttributesW`,
   which still opens at the kernel — so "the entry opens at the kernel"
   (previous update) was over-read; the content read via `fopen` may still
   never happen or fail instantly.

3. **Uncommitted `.spl` edits are NOT reaching the stage-2 candidate binary.**
   A `print("[fts-open-diag] ...")` added inside
   `FileTextSession.open` (`src/lib/nogc_sync_mut/io/file_text_session.spl`)
   is in the worktree but its literal is ABSENT from the built
   `simple.exe.rejected` (verified via `strings`), while same-session C
   edits in the same lane ARE present (cargo rlib rebuild works). Suspect
   the stage-2 build reads Simple sources through the SCV snapshot /
   frozen source-input capture rather than the live worktree, so Simple-side
   instrumentation is useless until that routing is confirmed. C-runtime
   diagnostics remain reliable.

Next session's fastest path: (a) instrument `rt_file_read_text` (ungated,
fopen-failure dump) and rerun — one lane cycle; (b) in parallel, verify how
the stage-2 native build sources `.spl` files (SCV snapshot vs worktree) so
Simple-level fixes actually reach the candidate.

## Update 2026-10-22 (evening, attempts 20-25): read fixed, parse-phase defect remains

The two-argument open twins (`rt_io_file_open_read/write/append`, C +
Rust) definitively fixed the read path: `load_sources` now reports
`done=1 total=1 succeeded=1` for the snapshot entry on every run. The
failure moved to the parse phase:

```
transient retained parser ownership failed for .../p2_add.spl
[hir-shard] owner=0/1@0 status=CRASH exit=-1073740791   (0xC0000409 fail-fast)
```

This is the defect the parallel lane fixed in the C runtime
(`3d407765f1e`, registered-immortal no-op in `rt_transient_heap_promote`).
Attempts 21-25 ported that exemption to the Rust twin
(`collections.rs:rt_transient_heap_promote`) three ways — exported C
predicate (unlinkable: `runtime_native.c` is not compilable into the Rust
runtime crate, build.rs ~line 459), Rust `is_registered_heap_ptr` +
scope-membership guard, and the exact C mirror (registered heap object ->
no-op). NONE fired: the crash is byte-identical each time.

Leading hypothesis for the next session: the candidate's parse-metadata
arrays are C-runtime heap objects (C tag bits; the candidate links BOTH
runtimes with duplicate symbols and link order decides). The Rust
`value.is_heap()` checks the RUST tag convention, so it returns false for
C-created objects, the exemption never matches, the Rust promote walks C
raw words, and `rt_transient_raw_promote` rejects them. Confirm by
instrumenting the Rust promote to print `value.0` (hex), `is_heap()`, and
`is_registered_heap_ptr()` for the failing roots; if they are C-tagged, the
fix is to classify through the C classifier (`rt_core_transient_classify`
family, which IS linkable — `rt_transient_raw_words` already is) or to
un-shadow the promote symbols across the two runtimes.

## Update: after PR #4133 (merge 05157642057), p2_add regressed to a surface_build crash

On merged HEAD 05157642057 (this lane's stack + PR #4133
windows-stage2-runtime-repairs: twin-based rt_io_file_open_* in fs.spl,
io_file.rs / runtime_native.c repairs), the stage2 sanity now fails on the
FIRST probe: p2_add dies right after `phase=surface_build current=start`
(worker crash → HIR aggregate failure), before any alias-scan/lowering
milestone (SIMPLE_NSCOPE_HIR_TRACE silent). The same p2_add probe PASSED on
this lane's pre-merge stack (e0e6dd8d1c8..e000f4525ef). The
stage2_module_path_naming SEGV bracket from this lane's instrumentation
(fault precedes alias scan; parse/entry-scan stage) still applies — the crash
simply now also reaches p2_add with the merged runtime-repair changes. Treat
the merged runtime-repair surface (fs.spl twins + io_file.rs) as the active
suspect for the surface_build-time worker crash; coordinate with the
#4133 lane before further full-sanity cycles.
## Attempt 26 (2026-10-22) — parse crash GONE; next blocker is SCV inventory drift

Attempt 26 reran the lane with a value-dump diagnostic wrapped around the
Rust `rt_transient_heap_promote` (collections.rs: prints
`[transient-promote-diag] FAIL value is_heap registered` on every false
return). Result:

- The parse-phase crash (`transient retained parser ownership failed`,
  0xC0000409) DID NOT OCCUR. The diagnostic NEVER FIRED (0 lines in every
  `stage2-sanity.env.frontend-*.log`). Conclusion: the exemption port in
  #4133 (exact C mirror: registered heap object -> no-op success) already
  fixed the parse crash; attempts 21-25 were killed by an earlier defect
  before the promote path was ever reached, and the C-tagged-object
  hypothesis above is disproved.
- The failure moved to the SCV admission/materialize step:

  ```
  SCV-E-ADMISSION: snapshot-index-drift:src/lib/nogc_sync_mut/io/file_text_session.spl
  candidate_frontend_smoke: p2_add-build failed (raw rc=1)
  ```

Root cause: the event-maintained source inventory
(`build/scv/source-inventory`, generation 1213, cursor `git_head=aa6cd63e`
= HEAD) carries a ROTTEN entry for that file: `content_digest=67cc6410…`,
`byte_count=17317`. The actual working-tree file (clean in git at HEAD,
`.gitattributes` forces LF) is 16977 bytes, `sha256=4fb92313…`. The
recorded digest matches NO commit in the file's history (verified across
the last 6 commits) — the entry captured uncommitted working-tree dirt at
some past refresh, and no later git event ever rewrote it, so every warm
refresh carried it forward. The fail-closed drift check
(`src/lib/scv/compile_snapshot.spl:430`) caught it exactly as designed.

Fix (operational, sanctioned by the admission gate's own messaging): the
lane's `scv_prime` cold-init step only fires when
`build/scv/source-inventory/CURRENT` is ABSENT
(`scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs:394`).
A rotten-but-present CURRENT makes every run admit warm and fail forever.
Recovery = run the scv_prime command manually with
`SIMPLE_SCV_INVENTORY_COLD_INIT=1` (candidate `native-build
--entry src/compiler/bootstrap_admission/p2_add.spl --runtime-bundle
core-c-bootstrap`), which rebuilds the inventory from Git complete
authority, then rerun the lane.

Follow-up (not done here): consider teaching the lane to auto-cold-init
when the warm admission reports `snapshot-index-drift` instead of looping
warm forever. File as a feature request if this recurs.
