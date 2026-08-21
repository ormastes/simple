# Aspect/dynload lane — plan (authored 2026-08-19)

My plan for this lane, written after re-verifying the tree rather than from memory.

Binary identity at authoring time (stamp before AND after every step below; other
sessions swap this symlink, so an unstamped verdict is worthless):
`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
59645008, 2026-08-18 10:12:23.164167908 +0000.

Machine hazard, measured this session: ~18 GB of 128 GB available, swap 0, and
**33 orphaned `simple` processes holding 92.4 GB**. earlyoom
(`--prefer simple|rustc|cc1 --avoid claude`) SIGTERMs at 10% free and SIGKILLs at
5%; 699 SIGTERMs hit `simple` in 6 hours. Separately the kernel OOM killer took
three claude sessions at 23:30:27 after a memory-guard script set
`oom_score_adj=1000` on them. **Exit 143/137 is an OOM kill, not a verdict** —
re-run, never record. One `simple` process at a time, detached with
`nohup setsid`, never wrapped in `timeout`.

## Position vs origin (re-verified, changed twice during the session)

At 23:47 `ca7c33ecf75` was my ANCESTOR (0 behind / 3 ahead), so no rebase was due.
By 00:xx origin had genuinely moved to **`e347858a954`** and I am now
**12 behind / 3 ahead**. A rebase IS now required. `git ls-remote` is the
authority here, not the local ref.

My 3 commits: `ca7c33ecf75` (base) -> `acd936994ba` (static component table) ->
`5ffd9e20e59` (SIF v1) -> `013f1b33a10` (this session's loader+aspect work).

## What has ACTUALLY landed

| Piece | State | Evidence |
|---|---|---|
| SIF v1 (`80.driver/sif/sif.spl`) | committed, specs green | `5ffd9e20e59`; roundtrip + discrimination specs exit 0 |
| aspect_pack container/catalog/loader | committed, 39 fns, specs 7/7 + 9/9 | `013f1b33a10` |
| segment mapper (one mmap per SEGMENT) | committed, WIRED | `module_loader_compat.spl:15` imports it; `:302` `map_segment`, `:312` `bind_symbol` |
| **smf_mmap_native real native layer** | committed — the real fix | was a Dict fake (`_g_fake_memory`, `native_call_function_0` -> `return 0`); now `rt_mmap_raw`/`rt_mprotect`/`rt_ptr_*` |
| ABI mismatch gate | genuinely wired | compare at `aspect_pack.spl:870`, error `:872`, asserted by defect spec `:240` |

## What is NOT done — stated plainly

**1. Neither SIF nor aspect_pack has a single product caller.** Verified by grep:
`use .*aspect_pack` across `src/**.spl` returns ZERO importers; the only mention
is `aop_group_manifest.spl:39` `aspect_pack_artifacts` commented
"SPEC-FORWARD: no aspect packs yet". SIF likewise has no importer outside its own
directory. Both are spec-proven libraries that nothing calls. This is the same
unwired-code defect class CLAUDE.md documents for `interface_digest_of` and
`smf_manifest_entry_verifies`, and it is the single most important gap in the
lane — passing specs are not the same as being in the load path.

**2. Execution of mapped code is unproven.** `segment_symbol_resolution_spec`
stands at 7/8 with the POSITIVE CONTROL honestly red: this interpreter cannot
invoke a raw `i64` code address (no working pointer cast — `unsupported cast
target type: Pointer` — and no `rt_call_*` extern). Arithmetic, bounds, lifecycle
and the native layer are proven; RUNNING code is not. Filed:
`doc/08_tracking/bug/loader_interpreter_cannot_call_raw_code_address_2026-08-18.md`.

**3. Deliberately not implemented** (recorded, not forgotten): PackRef
`content_hash`/`index_hash`/`signature_policy` (grep: 0 occurrences — no verifier
or signing authority in-tree, an unchecked hash is decoration);
`required_core_public_abi_hash` is carried and round-tripped but NEVER compared
(nothing publishes a core ABI hash, so the gate would be fake); multi-profile
catalogs §9.6; zstd dictionaries / co-load clusters §12.2 (design says optional);
AspectPackIndexCache + `pread`/`WILLNEED` policy §14.1/§15 (needs a file layer
this byte-array module lacks); unload §14.7 (design says not required initially).
§12.1/§23 remain PARTIAL — the pack is a standalone container, not yet a
registered SMF section type.

**4. Lint is INCONCLUSIVE, not green.** `lint-cached.shs` FAILs on every file
including an untouched control, with an unattributed
`undefined field 'config'`. Filed. No lane file's lint result may be quoted as a
pass until that is fixed.

## Order of work

1. **Rebase onto `e347858a954`** and re-verify: the guard verdicts I already hold
   (conflict-tree, markers, tree-size, runtime-API, divergence-delta — all PASS
   for `ca7c33ecf75..013f1b33a10`) are STALE the moment the base moves. Re-run
   all of them with an explicit range; the four that returned
   `ERROR — nothing was checked` did so because this is a linked worktree whose
   `.git` is a file, and exit 2 is never a pass.
2. **Record the 2 pre-existing divergence offenders** in the commit message or a
   `doc/08_tracking/bug/` record. The delta-PASS escape REQUIRES this; an
   unrecorded step-over is a violation even with a clean delta.
3. **Land** via `sh scripts/check/land.shs` — never raw `jj git push`, which
   skips the rules.sdl gates entirely.
4. **Close gap #1 — wire something.** Pick ONE real caller for the segment loader
   path and one for the aspect catalog, and prove it with a spec that fails if the
   wiring is removed. Unwired code is the lane's actual risk, not missing features.
5. **Close gap #2 — prove execution.** Cheapest credible route is an
   `rt_call_ptr_0(addr: i64) -> i64` extern in the C runtime; alternatives are
   making the pointer cast compile, or running the spec in a compiled-mode lane.
6. Only then consider §12.1/§23 (pack as a registered SMF section type). Every
   other unimplemented section stays deliberately unbuilt until something needs it.

## What I will NOT do

Add features from the design doc that nothing calls; run `--update-baseline` on
the no-direct-rt ratchet (197 below baseline is a deliberate reviewed action, not
a drive-by); weaken the positive control to make the board green; or commit any
out-of-lane file (jit_typed_ir, doc_coverage option-route, gui_web reports, Rust
`dispatch_profile`, `persistent_code_cache`) that other lanes authored.

## Update 2026-08-19 — research findings folded in as work items

Source: `doc/01_research/compiler/startup_perf/aspect_dynload_startup_loader_perf_research_2026-08-19.md`
(static reading only, no compiler run). Each item below was re-verified by me at
file:line before being written down.

### W1. W^X violation — DONE this session

`native_alloc_exec_memory` mapped `PROT_READ|PROT_WRITE|PROT_EXEC`, handing out a
simultaneously writable+executable page. Forbidden by startup_perf §8.5. The
alloc -> write -> `native_make_executable` sequence
(`segment_mapper.spl:124,129,134`) already grants RX by `mprotect` afterwards, so
`PROT_EXEC` at map time bought nothing. Now maps RW only.

### W2. The segment win is plausibly cancelled by a byte-at-a-time copy — OPEN, highest priority

`native_write_exec_memory` (`smf_mmap_native.spl:157-170`) writes **one byte per
SFFI call** in a `while` loop over `rt_ptr_write_u8`, and `smf_section_bytes`
copies byte-by-byte again before it. So the lane traded O(symbols) syscalls for
O(bytes) SFFI calls. The headline claim — that one-mapping-per-segment is FASTER
— is therefore **not established**, and could be a regression on large sections.
`rt_memcpy` exists but is pointer-typed and unreachable from an `i64` address.
Fix: a bulk `rt_ptr_write_bytes(addr, offset, [u8])`-style extern. **This must be
measured, not assumed, before the lane claims a perf win.**

### W3. Mapped code still cannot execute — OPEN

All four `native_call_function_N` return 0 unconditionally; no `rt_call_ptr_*`
extern exists anywhere in `src/runtime/*.c`. The RED positive control in
`segment_symbol_resolution_spec` is CORRECT and stays red. Cheapest route is an
`rt_call_ptr_0(addr: i64) -> i64` extern. Same root cause as W2: no way to reach
a raw address from Simple except one byte at a time.

### W4. Duplicate loader trees, and the FABRICATING one is the exported one — OPEN

`99.loader/object_mapper.spl:31-58` fabricates addresses arithmetically
(`4096 + gen*256 + len`) rather than mapping anything, and it is the mapper that
`99.loader/__init__.spl:34-38` re-exports. The real one (`segment_mapper.spl`) is
reached only by `module_loader_compat.spl` importing it directly. Any consumer
going through the package's public surface therefore gets the fake. This is the
same class as the `smf_mmap_native` Dict fake fixed this session.

### W5. The "82 .spl opens per run" anchor is REFUTED for the traced case

`doc/10_metrics/startup/startup_perf_check_2026-08-17.md` records `src/lib opens: 0`,
`openat 14`. `.claude/rules/commands.md` states 82 opens / 0 `.smf`. Both cannot be
right; the traced evidence wins for that case. Do not quote the 82 figure as
current without re-tracing the specific program.

### W6. Perf contract §20 has never been measured

§20.1-20.5 (cold-aspect startup, hot path, first use, steady state, config) plus
§15 mapping/I-O policy are this lane's, and there is **no measured number for any
of them**. What exists is instrumentation (`packs_opened`,
`modules_decompressed`, `bytes_decompressed`, `cache_hits`) proving the code takes
the cheap path — not that it is fast. aspect_pack is additionally in-memory only
(no mmap/open) with zero production consumers.

### Revised order

1. W2 (bulk write extern) + measure — without it the lane's perf claim is unproven.
2. W3 (`rt_call_ptr_0`) — turns the red positive control green honestly.
3. W4 (stop exporting the fabricating mapper) — a correctness trap for consumers.
4. Then wiring (gap #1 above), then W6 measurement against §20.

## Update 2 (2026-08-19, later) — W-items closed, and what the work actually found

Binary redeployed TWICE this session: 59645008 (2026-08-18 10:12:23) ->
59695432 (00:53:46) -> 59701088 (01:32:05). Both old binaries backed up beside
the deployed path. Every verdict below is stamped against 59701088 unless said
otherwise.

### W-item status

| item | status |
|---|---|
| W1 W^X (RWX mapping) | **DONE** — maps RW, mprotect RX after write |
| W2 byte-at-a-time write | **DONE, and it inverted twice** — see below |
| W3 mapped code cannot execute | **DONE** — `rt_call_ptr_0`; positive control 8/8, returns 11/22/33 from real mapped code |
| W4 fabricating exported mapper | **DONE** — delegates to the real mapper; 6/6 + 2/2 |
| W5 "82 .spl opens" anchor | **RESOLVED as a scope mismatch, not a contradiction** — the 0-opens trace was an import-free program; stdlib loading is lazy, so opens scale with imports. The universal phrasing is what was wrong |
| W6 §20 never measured | **MEASURED** — and §20 states NO numeric targets anywhere, so there is nothing to measure against. None were invented |

### W2 is the cautionary tale of this lane

The claim "one mapping per SEGMENT beats one per SYMBOL" went: unproven ->
apparently an 11.5x REGRESSION -> finally a 48-164x WIN. Sequence:
1. Per-byte `rt_ptr_write_u8` loop: ~250 MB/s.
2. Bulk `[u8]` extern: **6.6-11.5x SLOWER** (1 MiB: 5.00ms -> 57.4ms). Shipped by
   an agent WITH the measurement recorded; reverted here.
3. All-i64 (`rt_array_data_ptr` + `rt_ptr_write_bytes_raw`): **12.7-41.4 GB/s**,
   48-164x over the loop.
The first attribution ("a no-op extern costs 60ns, so marshalling is free") was
WRONG: `Value::Array` is Arc-wrapped so cloning is O(1); the real cost was the
JIT->interpreter bridge BOXING the array element by element. Only a signature
with no `[u8]` avoids it. **A measured number can be right and its explanation
still wrong** — the fix followed the corrected explanation, not the number.

### The finding that outranks the lane: the interpreter has no threads

`interpreter_extern/concurrency.rs:245-360` runs the closure INLINE and returns a
fake handle. Proven behaviourally: a worker sleeping 500ms had already
incremented before spawn returned. **Every concurrency test on the interpreter
path is vacuous** — a deliberately racy control could not be made to fail. The
native path (real pthreads) does not build here (`llc-20: multiple definition of
local value named 'l11'`), and the two paths take incompatible ABIs for the same
extern. Filed:
`doc/08_tracking/bug/interpreter_thread_spawn_runs_inline_all_concurrency_tests_vacuous_2026-08-19.md`.
This is why §14.6 is NOT built: it would look thread-safe and not be.

### Six pieces of code that looked alive and were not

This is the lane's dominant defect class, not any single feature:
1. `smf_mmap_native.spl` — Dict-simulated fake (`_g_fake_memory`,
   `native_call_function_0` -> `return 0`) behind a header claiming otherwise.
2. `object_mapper.spl` — FABRICATED addresses (`4096 + gen*256 + len`) and was
   the mapper the package publicly re-exported.
3. `loader/smf_mmap_native.spl` — called `exec_memory_allocs_remove/_len`,
   defined NOWHERE, masked because the file never compiled.
4. A "did not read payload" assertion **vacuously true** at `0 < 264` because
   struct-by-value copying discarded the counters it asserted on.
5. `forbidden_io_checker.spl` — spec-green 13/13, **zero callers**, protects
   nothing in a real compile. Found hours after being written.
6. `AtomicBool.compare_exchange` — self-admitted fake, "small race window".
**In every case the specs were green.** Green specs are not evidence of
reachability; only a caller is.

### Duplicate modules are the mechanism

Four duplicate-implementation findings: two `smf_mmap_native.spl` copies, the
`99.loader/loader/` shadow tree (which caused THREE separate defects, including
duplicate `JitInstantiator` type names that made `ModuleLoader` entirely
unrunnable — the interpreter keys registries by BARE TYPE NAME, not module), and
two independent zstd implementations where the "decoder-only" one hid the fact
that the other has an encoder. Unifying the loader trees is still an open
decision and now has three independent pieces of evidence behind it.

### Built since Update 1

§12.1+§23 SMF aspect-pack section, mutation-proven (deleting
`apk_loader_register_pack` flips REQ-APKW-07 red) — `aspect_pack` HAS product
callers now, traced through `module_loader_compat.spl`. §17 ABI gates that SKIP
rather than silently pass when no expectation is set. §5.7 epochs. §5.4-5.5
uniqueness. §9.6 profiles. §12.2 co-load clusters. §14.7 unload with pin/quiesce.
§15 pread I/O + §14.1 index cache. Joinpoint slot-cell patchpoints with a real
atomicity argument (single naturally-aligned 8-byte store; alignment CHECKED not
assumed; ordering explicitly NOT claimed). Content-hash verification with codes
DISJOINT from signature codes. E-APACK008 static checker + temporal seal.
Zip-bomb bound before inflation. Specs: 70+ examples green.

### Not built, and why building would be worse

zstd dictionaries (encoder emits raw/RLE blocks — a dictionary costs 4 bytes and
saves nothing); signature verification under a real trust root (a key shipped
beside the packs is green on attacker-controlled input, strictly worse than no
check); `binding_plan_id` (design names it once, defines it never); `facet<T>()`
sugar (frontend layer; ZERO call sites exist anywhere); §14.2 late states
(needs the runtime loader); §14.6 activation future (see threads, above).
All eight carry acceptance tests naming their blocker in
`test/01_unit/lib/aspect_pack_acceptance_pending_spec.spl`.

### Infrastructure defects found on the way out

- `land.shs` FAILS OPEN: it ran 31 gates, printed "both gates PASS — proceeding
  to push", then ran `jj bookmark set` / `jj git push` which BOTH failed with
  "There is no jj repo in ." — and exited 0. It never checks their exit status.
- The shared `.git/config` is being rewritten with `core.bare = true` (and
  sometimes `core.worktree` pointing at another lane) every few seconds by
  something on this box. While flipped, every lane's guards cannot determine what
  they are checking. The pre-push hook correctly REFUSES; `land.shs` does not.
- The direct-`rt_*` ratchet correctly caught this lane adding 40 call sites in
  non-provider code. Resolved by classifying four FFI-boundary FILES (not the
  directory) as providers.

### Still open

Bootstrap (nothing here is compiled into a pure-Simple compiler — everything is
source-level and seed-interpreted); unifying the duplicate loader trees; signing
key custody; wiring `forbidden_io_checker` into a semantic pass; and the push
itself, blocked repeatedly by the config corruption above.
# Aspect Dynload, HAL Migration, Runtime Boundary, and x86 Bootstrap Plan

**Date:** 2026-08-19  
**Status:** active; corrected after Sol review; implementation and bootstrap
acceptance incomplete; shared Git configuration repaired; bulk cleanup awaits a
fresh exact manifest  
**Merge owner:** `/root`  
**Final reviewers:** Sol/highest-capability reviewer for broad findings, coverage,
performance, repository cleanup, and done marks  
**Audited revision:**
`e3d58a25e733f32d2557936098f849ade1d7df57`

The working tree is changing concurrently. Counts below identify whether they
are historical, committed-tree, or current dirty-tree evidence. Before edits,
regenerate machine-readable censuses pinned to revision plus dirty-patch hash.

## 1. Objective

Deliver the following as one evidence-driven campaign:

1. Fix every currently reproducible test failure that is fixable on this host.
2. Prefer pure-Simple owners over Rust or C implementation paths.
3. Collapse direct `rt_*` use behind one reviewed owner per ABI/symbol family
   and public `hal_*`/`io_*` surfaces, subject to layer, capability-family,
   bare-metal, and bootstrap dependency constraints; remove accidental
   compatibility-family declarations.
4. Remove remaining non-reference Rust HAL work and migrate the remaining C HAL
   implementation to pure Simple without changing observable I/O semantics.
5. Prove C-versus-Simple I/O parity and obtain real 100% branch coverage for the
   scoped C and pure-Simple HAL implementations.
6. Finish startup, component dynload, aspect-pack, facet, interpreter, compiler,
   and loader work; compare retained performance with Bun, Go, Rust, Python,
   Java, and C where the lane is semantically comparable.
7. Produce and deploy a provenance-backed x86_64 Stage 4 bootstrap.
8. Preserve useful concurrent work, then remove only proven stale/wrong agent
   processes, worktrees, branches/bookmarks, locks, and unpublished commits.

This plan does not count a seed-only check, a stale receipt, a tautological test,
an empty coverage denominator, or an unavailable-platform skip as a PASS.

## 2. Frozen shared contracts

- Public hardware and I/O names are `hal_*` and `io_*`.
- A raw `rt_*` symbol may temporarily remain only in its canonical low-level
  provider. Compatibility families re-export that owner; they do not redeclare
  or reimplement the hook.
- The default pure-Simple owner for hosted runtime facades is
  `src/lib/nogc_sync_mut`; other runtime families delegate when semantics match.
- C/Rust reference implementations are test or bootstrap oracles, not the
  production user-facing owner.
- Shared parity helpers are `prepare_hal_fixture`, `run_c_hal_case`,
  `run_simple_hal_case`, `assert_hal_parity`, and
  `assert_hal_branch_coverage`.
- Manual steps use literal `step("inventory runtime boundaries")`,
  `step("compare C and Pure Simple I/O semantics")`,
  `step("measure HAL branch coverage")`, and
  `step("verify x86 bootstrap")`.
- An unfinished oracle fails explicitly with `assert(false)` or `fail(...)`.

## 3. Status snapshot

### 3.1 Tests and ignored work

| Evidence | Current status | Interpretation |
|---|---:|---|
| Historical env-gated audit (2026-08-09) | 27 files: 8 PASS, 19 real FAIL, 0 env-only FAIL | Historical fix queue only; not the current failure count. Current-tree audit already shows some rows repaired/stale. |
| Intentional dropped case | 1 Metal failure-injection case | Record as unavailable/dropped, never PASS. |
| Startup/ExecIR focused run on current dirty tree | 23 passed, 0 failed, 0 skipped | Covers four focused specs only; not a full-suite result. |
| Stage-binary runnable guard | 8 failed/crashed invocations out of 12 across 4 binaries | Artifact/runtime failures, separate from spec-file count. |
| Checked-in `summary.txt` receipts | 10,720 files, zero recorded fail/skip/ignore/pending | Stale Windows-origin receipts; historical only. |

Static raw-line census (not executable-scenario counts; comments/fixtures and
duplicated legacy/canonical test trees inflate these values): 216 `skip` lines,
93 `pending(...)`, 8 `ignore_it`, 4 ignore
annotations, 1 skip annotation, 5 `pass_todo`, 143 intentional no-op pass
variants, 788 tautology shapes, and 3 confirmed empty executable `it` bodies.
The relevant compiler subset contains 54 pending lines, 2 ignore annotations,
1 skip annotation, 9 no-op pass variants, and 144 tautologies. The relevant
runtime/HAL subset contains 33 pending lines, no explicit ignore/skip marker,
28 no-op pass variants, 119 tautologies, and 18 validated platform-gated
vacuous lines. Non-vendor Rust test-like files contain 29 `#[ignore]` markers.
Before implementation acceptance, generate a deduplicated manifest that reports
unique executable specs, duplicate mirror rows, failed spec files, failed
invocations, pending scenarios, ignored scenarios, unavailable rows, and source
comments/fixtures separately.

Authoritative failure sources:

- `doc/08_tracking/bug/gated_specs_are_tautology_shells_2026-08-09.md`
- `doc/08_tracking/bug/stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`
- `doc/08_tracking/test/expect_vacuity_gate_full_corpus_census.md`

### 3.2 `rt_*` boundary census

The first audit captured the following **unpinned historical dirty-tree lexical
snapshot**, excluding repository-declared vendor paths and bundled third-party
runtime headers. It is useful for area proportions only. It is neither the
audited-revision census nor the mutable-tree completion denominator.

| Area | Lexical `rt_*` tokens |
|---|---:|
| `src/compiler` | 5,403 |
| `src/lib` | 12,448 |
| `src/os` | 5,382 |
| `src/runtime` | 9,448 |
| `src/compiler_rust` | 31,654 |
| **Total** | **64,335** |

The current dirty-tree Sol review found **4,277 anchored direct pure-Simple
`extern fn rt_*` declarations**: 797 in `src/compiler` and 3,480 in `src/lib`.
It also found 32,061 current Rust-tree lexical tokens; 31,654 is the earlier
historical dirty-tree value above. The 64,335 total is not a callsite count and includes
comments and checked-in source artifacts.

Highest-repeat candidate declarations are `rt_env_get` (108 files),
`rt_file_read_text` (103), `rt_file_exists` (72 real declarations; two additional
comment examples were excluded), `rt_file_write_text` (41),
`rt_file_delete` (32), `rt_process_run` (29), and
`rt_time_now_unix_micros` (28). These are the first consolidation wave.

Before the first migration patch, add a checked-in census command and manifest
pinned to revision plus dirty-patch hash. It must report lexical tokens,
anchored declarations, unique symbols, semantic callsites, C/Rust definitions,
and files separately so these categories cannot be mixed again.

### 3.3 Rust, C, and pure-Simple HAL

Audited HAL scope: `src/os/kernel/arch`, `src/os/kernel/arch_adapt`,
`src/lib/nogc_sync_mut/hal`, and `src/compiler_rust/lib/std/src/bare/hal`.

| Implementation | Files | LOC | Status |
|---|---:|---:|---|
| Pure Simple `.spl` | 195 | 23,442 | Current dirty-tree scope, including `riscv_shared/fpga_orchestration.spl`; canonical direction, but several implementations remain partial. |
| C `.c` | 20 | 14,924 | Migration remains substantial. |
| C headers `.h` | 16 | 1,665 | Must shrink with the C implementation boundary. |
| Rust `.rs` HAL implementation | 0 | 0 | No owned Rust HAL implementation remains in this audited scope. |

The remaining C concentration is Cosmos/OpenSSD ARM32 (15 files/9,052 LOC),
RISC-V64 boot/runtime shims (3 files/4,804 LOC), Cortex-M33 (1 file/1,044
LOC), and a 24-line RISC-V32 boot shim. Rust files in the I/O parity benchmark
remain reference oracles, not HAL production implementations.

Known pure-Simple HAL gaps include the hard-coded 64-byte RISC-V64 cacheline,
module-local rather than cross-layer ZICBOM capability state, sentinel rather
than real DTB parsing in `hal_smp_init_from_bytes`, and seven known direct arch
imports outside the intended boundary.

### 3.4 HAL coverage and C/Simple I/O parity

No trustworthy HAL branch-coverage percentage exists today.
`build/coverage/coverage.sdn` reports 100% with zero files, zero decisions, and
zero paths and is invalid evidence. One `# @cover` target names a deleted
`src/lib/nogc_sync_mut/hal/mmio.spl`; markers are targets, not measurement.

Reusable parity assets already exist:

- `test/perf/io_parity/io_parity_simple.spl`
- `test/perf/io_parity/io_parity_ref.c`
- `test/perf/io_parity/io_parity_ref.rs`
- `test/perf/io_parity/run_io_parity_benchmarks.shs`

They cover checksum parity for `read_text`, `mmap_text`, and `append_at`, plus
startup timing. They do not cover the HAL branch denominator and must be
extended rather than relabelled.

Coverage acceptance is split into two truthful claim levels:

- **Host-executable branch coverage:** exact admitted source files, nonzero
  branch denominator, compiler/toolchain and instrumentation recorded, every
  branch hit, reviewed exclusions, and biting sabotage controls.
- **Physical-board contract coverage:** one real-device evidence scenario per
  declared board contract. QEMU, synthetic strings, and CPU-class evidence do
  not count as board-init execution.

Boot/inline-assembly and hardware-only leaves are isolated from host-executable
logic before any 100% claim. If production C is deleted, retain the reviewed C
oracle in a test-only location with hash/provenance, license, build command, and
explicit non-production status until the stabilization window closes.

### 3.5 Aspect/component dynload

Implemented substrate:

- `load_policy`, startup decision, and segment planning under `src/app/startup`.
- Checked dynSMF policy, artifact freshness, stub, ABI, and interface-hash gates
  under `src/os/smf/dynsmf_session.spl`.
- Config parsing/autoload helpers under `src/app/startup/dynsmf_autoload.spl`.
- SCI CLI extension route, registry, help, and completion contracts under
  `src/lib/nogc_sync_mut/composition`.
- Component descriptor parsing and catalog validation under
  `src/lib/common/structural/component/descriptor.spl`.

Partial/not wired:

- `src/app/main.spl` still calls `dynsmf_startup_session(...)`, not the config
  entrypoint.
- The loader-side `load_policy` consumer remains unfinished.
- No app-root stage-0 option-router cutover exists.
- `resolve_component` static/dynamic selection is not implemented.

True aspect/facet dynload remains not started: no implemented `AspectCatalog`,
`AspectPackDirectory`, `SMF_FLAG_ASPECT_PACK`, `facet interface`, `facet impl`,
`bind facet`, `FacetRef`, or `try_facet` surface exists in source and tests.

### 3.6 Startup/interpreter/compiler/loader performance

Current dirty startup work adds ExecIR encode-time arena sizing, a reusable
arena executor, memoized interpreter tier state, and array/slice runtime-local
tagging. Its four focused specs passed 23/23 in this audit. These files are an
active overlapping lane and must not be overwritten.

Five startup-campaign items remain: deploy self-hosted default `bin/simple`,
institutionalize >=5-sample p50/p95/RSS admission, prove full-rebuild static
folding, finish Phase-C app cutover/migration proof, and add Phase-E growth-band
remeasurement.

Retained startup evidence is seed-based and noisy: Simple source-run p50 31 ms,
Bun 31-33 ms, Python 43 ms, and `go run` 245 ms. No accepted native-Simple
lane exists because native build failed; Java is absent from the retained
matrix. These numbers do not prove pure-Simple parity.

### 3.7 x86_64 bootstrap

- Deployed `bin/simple` is still the Rust seed (sha256
  `d3d54fab80199cddb962e07ca1ab655c0cfb8be3594ad4aa615084948116af54`).
- The best retained pure-Simple artifact is an imported, stale Stage 2 archive
  (sha256 `adb24ebf9f3b09fe6baa89278660a898205a123253b3de3233a13ce960b34b1b`).
- No current admitted Stage 3 output is present.
- No provenance-backed Stage 4 artifact or deploy receipt exists.
- Current blockers are Rust-authority compile errors, a symlink/logical-path
  wrapper hazard, concurrent Rust/runtime tree churn, and stale admission paths.

### 3.8 Repository/process state

Repository configuration changed during the audit and temporarily placed
`core.bare=false` plus a lane path in the shared config. After quiescing Git/JJ
activity, the Sol-reviewed repair removed shared `core.bare`/`core.worktree`,
put `core.bare=true` in the bare primary's private `config.worktree`, verified
the GPU and aspect linked roots, and proved all three indexes unchanged. A
timestamped config backup remains under `/mnt/data/worktrees/simple-config-repair.*`.
The earlier registry audit found 443 entries, two missing registrations, and
three locked initializations; the two missing entries were pruned only after preserving
their heads as `rescue/agentrestore-35849c9` and
`rescue/fix-dbl-87d5f016`, and the failed seed checkout was removed only after
confirming commit `1c6c8d4` remained on `codex/gate5r-dir-sync-b791`.
The stale orphaned audit PGID 291105 and runaway cleanup audit groups 343494 and
376108 exited after `TERM`. All broader worktree, branch, commit, and JJ cleanup
remains paused until a fresh exact manifest converges; the earlier bulk counts
are planning evidence, not an authorized deletion list.

## 4. Implementation lanes

### Lane A — Test failure inventory and repair

- Freeze one deterministic manifest and exact compiler/mode/host identity.
- Reconcile all 19 historical rows against current source/receipts, classify
  repaired/stale/unavailable/current, then reproduce each currently failing row
  at most once and group it by shared root cause.
- Claim each category and fix the pure-Simple owner first.
- Replace tautologies, empty examples, and false platform PASS paths with real
  assertions or explicit unavailable status.
- Rerun failed shards only, then one scoped authoritative manifest.

### Lane B — Runtime boundary and alias collapse

- Start with env/file/process/time duplicate ownership.
- Move each hook to one canonical owner; make compatibility families re-export.
- Replace public direct `rt_*` imports with typed `io_*`/`hal_*` calls.
- Track the regenerated pinned-manifest baseline after each wave; a decrease is not
  acceptance unless ABI, error, ownership, and compiled execution stay green.
- Continue with compiler backend/loader and GPU/window/audio/CUDA SFFI groups.

### Lane C — HAL C-to-Simple migration

- Freeze observable contracts from C and current Simple implementations.
- Migrate one architecture/provider at a time: RISC-V32 shim, Cortex-M33,
  RISC-V64 boot/runtime, then Cosmos/OpenSSD ARM32.
- Keep assembly startup only where hardware ABI requires it; document why.
- Delete C owners and headers only after parity and target boot/link evidence.
- Resolve DTB cacheline/SMP parsing and capability-state gaps in their owners.

### Lane D — Real HAL coverage and I/O parity

- Define the exact C and Simple HAL file denominator, source hashes, branch
  model, instrumentation/toolchain, QEMU/board matrix, and reviewed exclusions.
- Extend the existing parity harness with the frozen shared helpers.
- Cover success, each error, boundary sizes, partial I/O, EOF, timeout,
  unsupported operation, invalid handles/addresses, and platform dispatch.
- Add deliberate negative controls proving every oracle and coverage gate bites.
- Require 100% of host-executable branches for both retained C reference and
  pure-Simple owner; zero-denominator coverage is a hard failure. Report
  physical-board contract coverage separately and never blend it into host
  branch coverage.
- Record p50/p95/RSS and byte/checksum parity on identical fixtures.

### Lane E — Startup and component dynload cutover

- Wire real startup entrypoints to dynload config without touching the no-op and
  help fast paths.
- Finish loader-side load-policy consumption.
- Implement `resolve_component` static/dynamic selection and real manifest IDs.
- Cut the app CLI to the SCI extension router/help/completion path.
- Prove extension add/remove changes config/artifact SHA without recompiling or
  relinking the core binary.

### Lane F — Aspect pack and typed facet surface

- Add aspect component IDs through existing checked dynSMF admission first.
- Implement aspect catalog/directory/container flag and loader rejection rules.
- Implement parser, type, lowering, and runtime support for typed facets only
  after a real pack can be admitted and loaded.
- Add cache-key/invalidation coverage for the visible aspect-catalog digest.
- Prove unload/lifetime behavior, stale-generation rejection, concurrent
  first-use single-flight publication, retry/error paths, capability denial,
  ABI/interface/implementation-hash rejection, and post-open digest/TOCTOU
  protection before open-world activation.
- Trace every grammar/loader/runtime acceptance case to selected requirements,
  architecture, detail design, executable SPipe, and generated/manual spec.

### Lane G — Interpreter/compiler/loader optimization

- Preserve and review the current ExecIR arena/tier changes.
- Profile the entire path before leaf tuning.
- Optimize algorithm, allocation/copy, layout, lookup/dispatch, then local code.
- Keep startup, source-run, cached-source, compile, native-run, and loader
  first-load/hot-load lanes separate.
- Compare identical semantics against C, Bun, Go, Rust, Python, and Java with at
  least five samples, p50/p95, max RSS, tool versions, hashes, and checksums.
- Record any remaining parity blocker under `doc/08_tracking/bug`.

### Lane H — x86_64 bootstrap and deployment

- Work from a physical private worktree and freeze Rust/runtime inputs.
- Repair the concrete Rust-authority compile errors before a broad bootstrap.
- Restore or regenerate valid Stage 2/3 admission paths; never relabel the stale
  imported parent as current-source proof.
- Build with `SIMPLE_NO_STUB_FALLBACK=1` and isolated cache paths.
- Require Stage 4 sanity, essential-tool smoke, provenance, post-bootstrap
  acceptance, and deploy receipt before replacing the seed.
- Deploy by atomic replacement with retained rollback binary/receipt. Record
  exact binary identity, compile and run smoke, compiler/lib/MCP/LSP checks,
  MCP integration smoke, and current Stage 2/3 provenance before promotion.

### Lane I — Sol-reviewed repository cleanup

- Preserve the repaired worktree-config ownership; do not reintroduce shared
  `core.bare`/`core.worktree`, clean the bare root, or infer authority from one
  inconsistent command.
- Inventory process/session lifecycle, worktree path existence, dirty state,
  unique unpublished commits, reachability, locks, branches, and bookmarks.
- Maintain an explicit whitelist of the main Codex PID/session and child-agent
  processes. Require UID, ancestry, CWD, and latest lifecycle evidence before
  terminating anything; use `TERM` with a grace/poll period before `KILL` and
  never use broad `pkill`. Preserve active `/root` children
  and any process currently proven active by lifecycle evidence.
- Trial cherry-picks only after ancestry plus patch-id/change-id comparison, in
  an explicit integration worktree. Preserve useful unique commits before
  removal; do not cherry-pick subject-equivalent or already-landed changes.
- Remove only clean or fully preserved stale/wrong worktrees and their
  branches/bookmarks; prune missing metadata and stale locks last.
- Discover each actual JJ root independently and audit its workspace plus
  operation log; `jj status` failing in this root proves nothing about sibling
  JJ workspaces.
- Do not delete unknown history or use broad cleanup as a shortcut.

## 5. Dependencies and parallel ownership

| Lane | May run in parallel with | Hard dependency |
|---|---|---|
| A tests | B, C inventory, E design | Frozen manifest and no repeated green gates |
| B runtime boundary | E/F docs, G measurements | One owner per symbol group |
| C HAL migration | E/F/G | D parity contract before deletion |
| D coverage/parity | E/F | Stable C reference and Simple candidate |
| E component dynload | B non-overlapping files, C/D | Existing dynSMF admission |
| F aspects/facets | C/D/G | E component resolver and real pack admission |
| G performance | C/D/E/F after their correctness gate | Stable executable and identical semantics |
| H bootstrap | Read-only audits only | Quiescent private tree and preceding correctness gates |
| I cleanup | Read-only status work | Sol review and preserved useful history |

Every implementation lane uses isolated files and cache directories. `/root` is
the merge owner. A Sol/highest-capability reviewer must accept broad findings,
manual quality, exclusions, performance claims, coverage denominator, cleanup
targets, and completion marks.

## 6. Acceptance gates

- [ ] All host-fixable manifest failures pass; unavailable rows are explicit.
- [ ] No new `pass_todo`, tautology, empty body, or false environment PASS.
- [ ] Direct pure-Simple `extern fn rt_*` declarations reach the reviewed target
      for each wave, with one canonical owner and no duplicate compatibility
      declaration.
- [ ] No owned Rust HAL implementation remains outside explicitly retained
      reference/bootstrap code.
- [ ] Scoped C HAL implementation is deleted only after pure-Simple replacement
      and target evidence.
- [ ] C/Simple I/O observations match on every fixture and error case.
- [ ] Real HAL coverage reaches 100% of the nonzero host-executable branch
      denominator for both admitted C and Simple providers, with biting negative
      controls; separately, every declared physical-board contract has real-board
      evidence or an explicit unavailable status.
- [ ] Real startup uses dynload config and component resolution.
- [ ] Aspect packs and typed facets have parser/type/loader/runtime coverage.
- [ ] Cross-language perf receipts use comparable work, >=5 samples, p50/p95,
      RSS, hashes, versions, fallback state, and checksum/output parity.
- [ ] A provenance-backed x86_64 Stage 4 passes and is deployed as `bin/simple`.
- [ ] Stage 4 deployment is atomic and rollback-tested; its binary identity,
      current Stage 2/3 provenance, compile/run smoke, and essential-tool smoke
      are retained.
- [ ] The final candidate passes `<runtime> check src/compiler`, `src/lib`,
      `src/app/mcp`, and `src/app/simple_lsp_mcp`, plus the MCP stdio integration
      smoke, with `SIMPLE_NO_STUB_FALLBACK=1` where applicable.
- [ ] Direct-env working/staged guards, numbered/generated-artifact guards,
      SPipe mirror/layout checks, `doc/06_spec` executable-spec count zero, stub
      prevention, requirement traceability, and manual-quality review pass.
- [ ] Dynload/aspect acceptance includes invalidation, unload/lifetime,
      concurrency/single-flight, retry/error paths, ABI/interface/impl-hash and
      post-open digest rejection, plus current requirements/design/spec links.
- [ ] Sol confirms useful commits preserved and only stale/wrong repository and
      process state removed.
- [ ] `$verify` reports `STATUS: PASS`; every acceptance criterion is run at
      most once after its final change.

## 7. Immediate order

1. Keep the repaired Git configuration quiescent; generate a fresh exact
   worktree/branch/JJ manifest before any further history mutation, then use a
   registered private integration worktree without destroying current residue.
2. Preserve the active ExecIR/aspect-dynload changes and any useful unpublished
   commits.
3. Freeze the failing-test and HAL/`rt_*` manifests.
4. Fix stage/Rust-authority blockers and the smallest shared test root causes.
5. Run runtime-boundary and HAL parity/coverage lanes in parallel with dynload
   startup/component work.
6. Implement aspect-pack and typed-facet lanes.
7. Integrate optimization work, record cross-language evidence, then bootstrap
   x86_64 Stage 4.
8. Perform one final Sol review, bounded verify pass, and cleanup.
