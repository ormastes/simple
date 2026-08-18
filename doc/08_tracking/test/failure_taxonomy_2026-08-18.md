# Suite Failure Taxonomy — 2026-08-18 (sharded run)

Triage-only record. No fixes applied. Derived entirely from the existing shard
logs (`shard_02_integration`, `shard_integration`, `u_os`, `u_browser_engine`,
`u_hardware`, `u_std`, `u_compiler_core`) by parsing the per-file `FAIL`
verdict lines and their attached `Error:` line. The suite was **not** re-run.

## 1. Cascade hypothesis — CONFIRMED

| metric | value |
|---|---|
| failing spec FILES (all 7 shards) | **1,373** |
| failing EXAMPLES | **8,092** |
| files where `failed == skipped > 0` (whole-file abort) | **1,121 (81.6%)** |
| examples inside those files | **7,786 (96.2%)** |
| files with `0 passed` (nothing ran at all) | **766** |
| examples per failing file (mean) | 5.9 |

The failed/skipped mirroring in the shard summaries is real and mechanical: a
spec file hits a semantic/load error, the current example is recorded FAILED and
every remaining example in that file is recorded SKIPPED, so the two counters
move together. **~8,000 failed examples are produced by ~1,373 file-level
events, and those collapse to 16 error classes.**

A second multiplier: `test/02_integration/**` and `test/integration/**` are
duplicate mirrored trees, both sharded. 1,050 unique spec paths produce the
1,373 file records; **1,839 of the 8,092 failed examples are the mirror copy of
another failure**. De-duplicating the mirrors, the real failing-example count is
**6,308**.

Per shard (files / examples): 02_integration 459/2472 · integration 329/1826 ·
u_os 454/2726 · u_browser_engine 50/520 · u_hardware 48/165 · u_std 24/369 ·
u_compiler_core 9/14.

Note on log fields: these logs do **not** emit `reason=parse-error`,
`reason=unresolved-module`, `outcome=ERROR`, `executed=0` or `dropped=<n>` as
verdict attributes. `SPEC FILE VERDICT:` lines carry only
`declared>=/executed/passed/failed/dropped`, and **`dropped=0` on every line in
every shard** — zero drops anywhere. The classification below therefore comes
from the `Error:` payload attached to each `FAIL` line, which is the only
root-cause-bearing field present.

## 2. Ranked taxonomy

| # | class | files | examples | cum % | representative error |
|---|---|---|---|---|---|
| 1 | `OBJECT_TYPE_ERASURE` | 761 | 6,048 | 74.7 | ``semantic: method `add_bug` not found on type `object` (receiver value: BugDatabase(bugs: {}, path: /tmp/...))`` / `semantic: undefined field 'keyword': cannot access field on value of type 'object'` |
| 2 | `SUBPROCESS_EXIT_NONZERO` | 320 | 1,149 | 88.9 | `Process exited with code 1` |
| 3 | `MISC_UNCLASSIFIED` | 52 | 223 | 91.7 | `error: compile failed: io: Cannot read "/tmp/simple_run_diagnostics_contract_missing.spl": No such file or directory (os error 2)` |
| 4 | `FUNCTION_NOT_FOUND` | 13 | 127 | 93.3 | ``semantic: function `disable_ffi_screenshots` not found`` |
| 5 | `METHOD_NOT_FOUND_CONCRETE` | 25 | 109 | 94.6 | ``semantic: method `to_bytes` not found on type `str` (receiver value: simple.composition/1)`` |
| 6 | `UNKNOWN_EXTERN` | 32 | 104 | 95.9 | `error: semantic: unknown extern function: mathlib_add` |
| 7 | `ARITY_MISMATCH` | 5 | 77 | 96.8 | `semantic: function expects argument for parameter 'opt_level_i64', but none was provided` |
| 8 | `UNRESOLVED_MODULE` | 73 | 73 | 97.8 | `error: semantic: Cannot resolve module: app.cli_debug.evidence_inspect_v1` |
| 9 | `CLASS_MISSING_FIELD` | 46 | 65 | 98.6 | ``semantic: class `DebugConfig` has no field named `args``` |
| 10 | `INVALID_ASSIGN` | 10 | 42 | 99.1 | `semantic: invalid assignment: cannot index assign value of type array` |
| 11 | `ASSERTION_MISMATCH` | 8 | 30 | 99.4 | `expected  to contain js: file not found` |
| 12 | `GENERIC_SPEC_FAILED` | 2 | 16 | 99.6 | `error: test-runner: spec failed` |
| 13 | `NO_SUMMARY_PARSE` | 10 | 10 | 99.8 | `no parseable pass/fail summary in test output; refusing synthetic pass` |
| 14 | `TRAIT_NOT_IMPLEMENTED` | 7 | 7 | 99.9 | ``error: semantic: type `TestPixelBackend` does not implement required method `report_damage` from trait `CompositorBackend``` |
| 15 | `UNKNOWN_VARIANT_OR_STATIC` | 3 | 5 | 99.9 | `semantic: unknown static method public_none on class AuthorityToken` |
| 16 | `MODULE_MISSING_EXPORT` | 5 | 5 | 100.0 | `error: runtime: Module "timing" does not export 'hybrid_sim'` |
| 17 | `STD_VAR_NOT_FOUND` | 1 | 2 | 100.0 | ``semantic: variable `std` not found`` |

**16 error classes (17 rows incl. a misc bucket) explain 100% of the 8,092
failures; the top 2 explain 88.9%.**

### Representative spec paths per class

1. `test/02_integration/app/bug_tracking_scenario_spec.spl`,
   `test/01_unit/browser_engine/anonymous_block_spec.spl`,
   `test/01_unit/os/apps/coreutils/cat_spec.spl`
2. `test/02_integration/app/add_remove_log_modes_spec.spl`,
   `test/02_integration/app/cli_log_modes_spec.spl`,
   `test/02_integration/app/brief_log_modes_spec.spl`
3. `test/02_integration/app/diagnostics/run_diagnostics_contract_spec.spl`,
   `test/02_integration/app/sspec_maintain_compatibility_spec.spl`
4. `test/02_integration/lib/std/screenshot/screenshot_ffi_spec.spl`,
   `test/02_integration/rendering/simd_parity_spec.spl`
5. `test/02_integration/app/configc/configc_roundtrip_spec.spl`,
   `test/02_integration/fs_driver/multi_mount_test.spl`
6. `test/02_integration/sffi/direction_b_import_roundtrip_spec.spl`,
   `test/02_integration/t32_hw/00_preflight_spec.spl`
7. `test/02_integration/compiler/llvm_compiled_proof_spec.spl`,
   `test/02_integration/svmg/conformance/conformance_suite_spec.spl`
8. `test/02_integration/hardware/rv32gc/rv32_linux_platform_contract_spec.spl`,
   `test/02_integration/ffi_gen/math_migration_test.spl`
9. `test/02_integration/t32_hw/10_session_open_spec.spl` (all 46 are `t32_hw/**`)
10. `test/02_integration/storage/dbfs/dbfs_image_builder_spec.spl`,
    `test/02_integration/storage/nvfs/nvfs_image_builder_spec.spl`

### Class 1 bound (already owned by another agent — mechanism NOT investigated here)

`OBJECT_TYPE_ERASURE` = the ``method X not found on type `object` `` /
`undefined field ... on value of type 'object'` family. **761 files, 6,048
examples, 74.7% of all failures.** Shard split: u_os 340 files ·
02_integration 228 · integration 125 · browser_engine 45 · u_std 16 ·
u_hardware 7 · compiler_core 0. This is the single dominant cause and is being
root-caused separately; counted and bounded here only.

### Class 2 sub-structure

`Process exited with code 1` is an opaque wrapper: the spec shells out to
`bin/simple <cmd>` and asserts on the child. **193 of the 320 files (772
examples, 67% of the class) are `*_log_modes_spec.spl`** — one CLI logging-mode
contract replicated across the CLI surface. The remaining 127 files are mixed
CLI-invocation specs. These are almost certainly a small number (likely 1–3) of
real defects, not 320.

## 3. Four-way classification

**(a) Genuine product defects — 1,268 files / 7,548 examples (93.3%)**
Classes 1, 2, 4, 5, 7, 9, 10, 14, 15, 16, 17. Compiler/interpreter type erasure
(1), CLI log-mode contract (2), missing stdlib/screenshot functions (4),
missing methods on concrete types (5), signature drift on `opt_level_i64` (7),
`DebugConfig.args` field drift (9), `cannot index assign value of type array`
(10), unimplemented trait method (14), enum/static-method drift (15, 16, 17).

**(b) Test-side defects — 141 files / 342 examples (4.2%)**
Class 8 `UNRESOLVED_MODULE` (73 files — specs importing module paths that do not
exist: `hardware.rv32imac.*`, `hardware.rv64gc.*`, `hir_types`,
`test.dbfs.bench_harness`; stale test-only imports, not product regressions),
class 11 `ASSERTION_MISMATCH` (8), class 12 (2), class 13 `NO_SUMMARY_PARSE`
(10 — specs whose output the runner cannot parse; the runner correctly refuses a
synthetic pass), plus most of class 3 (specs referencing `/tmp/...spl` fixtures
they never create).

**(c) Environment limits — excluded from this lane, ~136 examples**
Class 6 `UNKNOWN_EXTERN` (32 files) is largely external-SDK/hardware: the
`t32_hw/**` TRACE32 specs, SFFI specs needing a built `mathlib`, and
`rt_tcp_connect` network externs. Also the QEMU/`qemu-system-x86_64 not found`
and WebGPU/Vulkan adapter probes seen inside class 3. **These should be filtered
out of this lane's denominator, not fixed here.** Note class 9's 46 files are
*all* `t32_hw/**` too — but their error is a real field-drift defect (a), which
would surface on hardware as well.

**(d) Infrastructure / harness artifacts — 12 files, 0 attributed examples**
12 `TERMINATED: child produced no exit status — spawn or reap failure at the
process layer` (5 in 02_integration, 7 in u_os) and 14 timeouts across the
shards. Load-induced: the shard summaries also report `Session setup: 141185ms`
(u_browser_engine) — a fixed ~140–310s per-shard startup, unrelated to the
failures. Not root causes; re-run under lower load before treating any as real.

## 4. Recommended fix order (by examples unblocked)

1. **`object` type erasure** — 6,048 examples (74.7%). Owned by another agent.
   Nothing else on this list is worth sequencing ahead of it; every other fix
   combined is a quarter of the run.
2. **`*_log_modes_spec` CLI contract** — 772 examples (9.5%) from likely one
   defect in the CLI logging-mode handling. Highest ratio of examples-per-fix
   after #1, and independent of #1. **Do this first if #1 is blocked.**
3. **Remaining `Process exited with code 1` CLI specs** — 377 examples.
   Needs the child's stderr captured; the harness currently discards it. Filing
   a harness change to surface child stderr is a prerequisite and is itself a
   cheap high-leverage fix.
4. **`disable_ffi_screenshots` / `set_ffi_refresh` / `set_ffi_output_dir`
   missing (class 4)** — 127 examples, 13 files, one missing screenshot-FFI
   surface. Small, self-contained.
5. **`opt_level_i64` arity drift (class 7)** — 77 examples from 5 files, one
   signature. Trivially small fix, good examples-per-line ratio.
6. **`DebugConfig.args` (class 9)** — 65 examples, one field. Blocks the whole
   `t32_hw` suite from even loading, so it must land before any TRACE32
   environment work can be assessed.
7. **`cannot index assign value of type array` (class 10)** — 42 examples,
   dbfs/nvfs image builders, one compiler/semantic rule.
8. **Stale test imports (class 8)** — 73 files but only 73 examples; low
   payoff per file, but each is a one-line delete or path correction and it
   clears 5% of the failing-FILE count, which matters for signal quality.

Fixing #1 and #2 alone moves ~6,820 of 8,092 failed examples (84.3%).

## 5. Method / reproducibility

Aggregates computed by parsing `FAIL <path> (n passed, n failed, n skipped, …)`
plus the following `Error:` line from the seven shard logs; the leading message
of each semicolon-joined `Error:` payload was normalised (paths, quoted
identifiers, receiver values and numbers stripped) and bucketed into the 16
classes above. Analysis scripts were run in scratch and are deliberately not
committed.
