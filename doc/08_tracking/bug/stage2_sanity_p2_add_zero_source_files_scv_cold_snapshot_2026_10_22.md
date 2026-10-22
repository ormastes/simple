# Stage 2 sanity p2_add probe: entry collects zero source files under SCV cold snapshot

Date: 2026-10-22
Status: open, root cause localized to the SCV cold-snapshot entry-admission path; needs a dedicated lane
Severity: P1 (blocks every `--full-bootstrap --stop-after-stage2` sanity admission on this tree)

## Symptom

`scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2 ...`
compiles Stage 2 successfully (1481 modules, candidate produced, `--version` OK,
`run` negative control OK), then the frontend smoke fails the p2_add probe:

```
error: compiler entry 'src/compiler/bootstrap_admission/p2_add.spl' collected zero
source files: the entry must be a path to a .spl file (e.g. 'dir/main.spl'), not a
module path (e.g. 'dir.main'), and the path is resolved relative to the current
working directory
error: HIR aggregate failure; final worker and artifact publication blocked
```

Stage 2 is rejected; no stage3-planner receipt is produced.

## Reproduction (no full bootstrap needed)

From the repo root, with the preserved rejected candidate (any stage2 candidate
reproduces it, including locally built ones):

```sh
C="$PWD/.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected"
SIMPLE_BINARY="$C" SIMPLE_BIN="$C" SIMPLE_BOOTSTRAP_DRIVER="$C" \
SIMPLE_FRONTEND_DELEGATE="$C" SIMPLE_FRONTEND_DELEGATED=1 \
SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_NATIVE_BUILD_FORCE_WORKER=0 SIMPLE_BOOTSTRAP=0 \
SIMPLE_LIB="$PWD/src" SIMPLE_SCV_INVENTORY_COLD_INIT=1 \
"$C" native-build --backend llvm --runtime-bundle core-c-bootstrap \
  --entry-closure --entry src/compiler/bootstrap_admission/p2_add.spl \
  --cache-dir /tmp/probe-cache --mode one-binary --output /tmp/p2_add
```

Fails in ~15 s with the zero-source error. Removing `build/scv` entirely (fresh
single generation) does not change the outcome; `--jobs 1` does not either.

## What the trace shows

With `SIMPLE_NATIVE_BUILD_TRACE_CLOSURE_SCAN_PHASES=1`
(evidence: `probe7-closure-trace.log`):

1. The entry IS resolved into the SCV snapshot and READ SUCCESSFULLY:
   `closure_node:start`, `cached_scan:start`, `read:start`, `read:done`,
   `imports:done`, `siblings:done`, `cached_scan:done`, `closure_node:scanned`
   all reference
   `build/scv/snapshots/scv-revision-v1-*/src/compiler/bootstrap_admission/p2_add.spl`.
2. The snapshot inventory provably contains the file (20 `bootstrap_admission`
   rows; `p2_add.spl` row with sha256 and byte count present in
   `SCV_COMPILE_INVENTORY` and in `build/scv/source-inventory/generations/*.inventory`).
3. A second scan of the same snapshot path (`read:done`) runs inside
   `phase=load_sources`, then `all_sources.len() == 0` fires the fail-closed
   zero-seed error at `src/compiler/80.driver/driver_source_pipeline_loading.spl:950-951`.

So the file is admitted and readable, the first closure scan succeeds, yet the
`load_sources` seed pass ends with zero `SourceFile`s. The empty result can only
come from `_driver_collect_explicit_compiler_source`
(`src/compiler/80.driver/driver_source_loading.spl:1662`) returning `[]`, i.e.
either the cached scan returned `content == ""`
(`_driver_cached_entry_source_scan`, line 825: the SCV admitted-epoch read error
is swallowed at line 838-840 with no diagnostic) or the module-alias pass
dropped the only source. The swallowed epoch error path is the prime suspect:
any `driver_admitted_epoch_read_v1` failure (read-outside-task, source-escape,
source-not-admitted, content-mismatch) silently becomes `""` and surfaces only
as this misleading zero-source message.

## Pre-existing on release_phase3

`driver_source_pipeline_loading.spl`, `driver_source_loading.spl`,
`driver_admitted_epoch.spl`, `driver_source_pipeline_loading.spl` and
`src/compiler/bootstrap_admission/p2_add.spl` are byte-identical to
`release_phase3@origin` (`84841547`). The defect is not merge-introduced; no
full bootstrap sanity admission has passed on this tree since the early-October
SCV/snapshot hardening landed (see also the open `bootstrap_main_closure_pulls_src_os_hir_failures_2026_10_20` P0 and related stage2/stage3 rows in `bug_db.sdn`).

## Landmines fixed on the way to this point (all pre-existing, all in the merge commit)

- 21 malformed/misplaced `@workaround` pragmas across `src/` and `test/`
  (placement rule: pragma must immediately precede code; canonical form
  `bug=<id> [recover=..] [reason=..]`).
- 56 workaround bug IDs missing from `doc/08_tracking/bug/bug_db.sdn`
  (registered in both `bugs` and `bugs_active` tables; CRC32 header recomputed;
  the file carries a `#sdn-crc32:` header that must match the body).
- `src/compiler_rust/native_all/Cargo.toml`: `hosted-webgpu-provider` was never
  enabled for `simple-runtime`, so the `rust-native-all` staticlib/cdylib link
  failed with undefined `rt_webgpu_{upload_pixels,present,compute_draw}` on
  macOS (the Rust twins are compiled out under `native-all-provider`; the
  feature comment documents this feature as the canonical provider lane).
- `src/compiler_rust/Cargo.lock` regenerated offline after the merge unioned
  both sides' `Cargo.toml` dependency edits against the release-side lock.
- Stale git index in the jj-colocated tree recorded `src/app/lsp` as a symlink
  while it is a real directory, which fail-closed the SCV directory-alias
  inventory (`SCV-E-ADMISSION: directory-alias-inventory-invalid`); fixed with
  `git add -A` (jj does not use the index).

## Refined diagnosis (2026-10-22, second instrumentation pass)

The failure is NOT in the SCV snapshot machinery. Instrumenting
`_driver_collect_explicit_compiler_source`
(`src/compiler/80.driver/driver_source_loading.spl:1664`) shows the
snapshot-resolved entry path is passed in correctly, but the scan returns
`content == ""` for every entry. The SCV admitted-epoch path is not active
(no `[epoch-read-fail]` marker), so the empty content comes from the plain
`file_read_nullable(path) -> file_read_result -> FileTextSession.open ->
io_file_open` chain returning `Err` (open returning -1).

Decisive isolation: the SAME Stage-2 candidate binary cannot entry-compile
ANYTHING — `compile /tmp/probe_hello.spl` (a 3-line file, no SCV env, no
bootstrap) fails with the identical zero-source error, while bulk `--source`
loading works (the Stage-2 build itself compiled 1481 modules), and the
freshly rebuilt Rust seed (`src/compiler_rust/target/bootstrap/simple`)
compiles the same file correctly. `--version` and the `run` negative control
work, and small reads through other facades (the workaround refresh reading
`.simple/workarounds.sdn`) work.

## Resolved chain (2026-10-22, third pass — the entry-read path is FIXED)

The zero-source failure is RESOLVED. Chain of distinct seed-codegen defects
found and fixed (all in the merge commit; each verified by candidate
disassembly or lldb backtrace):

1. **`io_file_open` (FIXED)** — `src/lib/nogc_sync_mut/sffi/fs.spl`. The
   manual `rt_string_data`/`rt_string_len` expansion on an `Any`-typed owner
   was re-expanded by the compiler's text-arg expansion table at the
   `rt_io_file_open` call site: the candidate disassembly showed the call
   receiving `rt_string_data(address), rt_string_len(address)` (expansion
   applied to the already-extracted raw pointer) → open always returned -1.
   Binding the result or converting through `[u8]` did NOT change the
   lowering. Fix: declare the extern in text form
   (`extern fn rt_io_file_open(path: text, mode: i64)`, matching
   `compiler/src/codegen/runtime_sffi.rs:2310`) and let the compiler expand
   the text argument itself.
2. **Empty-container promote refusal (FIXED)** —
   `rt_transient_heap_promote` refuses roots that classify as immediates;
   empty arrays (`[]` module globals) and empty text are immediates on the
   core-C runtime, so promoting them returned false and failed the whole
   retained-owner promotion for any input without enum attributes. Fixed with
   vacuous-success `len() == 0` guards in
   `parser_declaration_metadata_promote_transient_owner` and
   `representation_parser_promote_transient_owner_v1`.
3. **NLL `LoanAlias` field-layout SEGV (OPEN — root defect)** — after the
   above, load→parse→MIR succeed; the candidate then SIGSEGVs in
   `NLLChecker.live_aliases` (`ldr [x8, #8]`, x8=nil) reading
   `alias.place.base`. This is the documented inferred-layout defect from
   `doc/08_tracking/bug/native_inferred_loan_alias_field_layout_2026-10-21.md`
   (field read lands at offset +0 `loan_id` instead of +8 `place`). Tried and
   FAILED workarounds: for-in → indexed loop (same crash), same-module
   `loan_alias_place` accessor, and a NEW cross-module accessor
   (`loan_alias_place_cross` in borrow_graph.spl) — the helper's own
   `alias.place` read still mis-infers when compiled in borrow_graph.spl.
   The r17-reported workaround (typed accessor) fixed a same-module CALL SITE;
   here the element load itself appears mis-compiled in this module context.
   ROOT FIX belongs in the seed's native field-layout inference; source
   workarounds are unreliable per call site.

Current state: Stage-2 sanity still cannot admit (borrow_check crash). Do
not deploy the rejected candidate. Repro for item 3 (15 s, no bootstrap):
`simple.rejected compile /tmp/probe_hello.spl` → SIGSEGV in
`compiler.borrow.borrow_check.nll.NLLChecker.live_aliases`; lldb gives the
exact faulting instruction.
