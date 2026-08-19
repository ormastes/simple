# Failure Taxonomy — `test/system/` and `test/unit/` — 2026-08-18

Measurement-only record. **No fixes applied. No tests skipped.** Produced with the
class-resolution-fix binary `/mnt/data/tmp/classfix/release/simple`
(mtime 2026-08-18 14:27:16, matching HEAD `2d461e78c9c`
"fix(interpreter): restore class field/method resolution"), **not** the shared
`bin/simple`, which is still the old broken build.

Format mirrors `doc/08_tracking/test/failure_taxonomy_2026-08-18.md`.

## 0. HEADLINE — `object` type erasure is NOT fixed by the class-resolution fix

The parent lane expected `OBJECT_TYPE_ERASURE` to be near zero under the fixed
binary. **It is not.** It is the single largest class in both trees measured
here, on the fixed binary:

* `test/unit/` shards: **369 of 450 failed examples (82%)** across 22 spec files.
* `test/system/` shards: **22 of 57 failed examples** across 4 spec files — the joint-largest class.

Verbatim representative errors captured on the FIXED binary:

```
semantic: method `executed_files` not found on type `object` (receiver value: CoverageCollector(line_hits: {}, function_calls: {}))
semantic: undefined field 'width': cannot access field on value of type 'object'
semantic: method `append` not found on type `object` (receiver value: ConsoleBuffer(_count: 0, _head: 0, _entries: []))
```

Note the receiver values are fully-formed class instances printing their real
fields, yet the field/method lookup still resolves against `object`. Whatever
`2d461e78c9c` repaired, this defect class survives it. **Treat any claim that
the erasure regression is closed as unproven until this is re-measured.**

## 1. Run methodology and what is INCONCLUSIVE

Whole-tree runs were attempted first and **both failed to produce a `Results:`
line**:

* `test/system` (1859 specs) — reaped while still printing `[setup] discover: begin (target: test/system)`. **INCONCLUSIVE, not a pass.**
* `test/unit` (5124 specs) — reaped while still printing `[setup] discover: begin (target: test/unit)`. **INCONCLUSIVE, not a pass.**

This reproduces the known whole-tree discovery hazard. Both trees were therefore
**sharded by subdirectory** — every subdirectory of `test/system/` and
`test/unit/` was run as its own target, 91 shards total.

A second, separate failure mode appeared: launching all 91 shards concurrently
drove the box to **104 GB of 125 GB used**, and 62 shards were killed mid
module-load with no `Results:` line. Those were relaunched at concurrency 5;
that rerun was still in progress when this record was written. **Every shard
without a verbatim `Results:` line below is reported as INCONCLUSIVE and is
excluded from all counts — none is counted as a pass.**

| tree | shards with a `Results:` line | shards INCONCLUSIVE |
|---|---|---|
| `test/system/` | 13 | 45 |
| `test/unit/` | 15 | 18 |

INCONCLUSIVE system shards: sys_acceptance,sys_app,sys_batch,sys_code_quality,sys_compatibility,sys_compiler,sys_compiler_comprehensive,sys_database,sys_duplicate_check,sys_dynload,sys_e2e,sys_edge_case,sys_error_path,sys_exploratory,sys_features,sys_final_push,sys_functional,sys_generated,sys_gui,sys_infrastructure,sys_integration,sys_interpreter,sys_lint,sys_lsp,sys_math,sys_mcp,sys_module_import,sys_os,sys_performance,sys_qemu,sys_reftest,sys_regression,sys_resilience,sys_runtime_comprehensive,sys_sanity,sys_security,sys_security_tests,sys_simpleos,sys_smoke,sys_stdlib,sys_t32_tools,sys_test_daemon,sys_ui_browser,sys_watcher,sys_wm_compare

INCONCLUSIVE unit shards: u_app,u_browser_engine,u_bugs,u_common,u_compiler,u_compiler_core,u_core,u_doctest,u_hardware,u_jit,u_lib,u_memleak,u_os,u_perf,u_qemu,u_runtime,u_std,u_tools

## 2. Verbatim `Results:` lines

Aggregate of measured shards — system: `total=390 passed=333 failed=57 shards_with_results=13 shards_without=45`; unit: `total=959 passed=509 failed=450 shards_with_results=15 shards_without=18`.

### `test/system/`

| shard | verbatim Results line |
|---|---|
| `sys_compositor` | `Results: 3 total, 0 passed, 3 failed, 3 skipped` |
| `sys_core` | `Results: 10 total, 10 passed, 0 failed` |
| `sys_coverage` | `Results: 127 total, 111 passed, 16 failed, 15 skipped` |
| `sys_daemon_sdk` | `Results: 23 total, 23 passed, 0 failed` |
| `sys_dap` | `Results: 30 total, 30 passed, 0 failed` |
| `sys_hardware` | `Results: 86 total, 85 passed, 1 failed` |
| `sys_infra` | `Results: 9 total, 9 passed, 0 failed` |
| `sys_kernel` | `Results: 18 total, 11 passed, 7 failed, 6 skipped` |
| `sys_llm` | `Results: 28 total, 28 passed, 0 failed` |
| `sys_repl` | `Results: 19 total, 0 passed, 19 failed, 19 skipped` |
| `sys_tools` | `Results: 4 total, 4 passed, 0 failed` |
| `sys_ui` | `Results: 31 total, 20 passed, 11 failed, 10 skipped` |
| `sys_verification` | `Results: 2 total, 2 passed, 0 failed` |

### `test/unit/`

| shard | verbatim Results line |
|---|---|
| `u_baremetal` | `Results: 121 total, 121 passed, 0 failed` |
| `u_browser` | `Results: 288 total, 78 passed, 210 failed, 210 skipped` |
| `u_compiler_shared` | `Results: 4 total, 4 passed, 0 failed` |
| `u_coupling` | `Results: 109 total, 107 passed, 2 failed, 2 skipped` |
| `u_debug` | `Results: 6 total, 6 passed, 0 failed` |
| `u_doc` | `Results: 9 total, 3 passed, 6 failed, 4 skipped` |
| `u_examples` | `Results: 2 total, 2 passed, 0 failed` |
| `u_gpu` | `Results: 138 total, 9 passed, 129 failed, 126 skipped` |
| `u_hal` | `Results: 30 total, 26 passed, 4 failed, 4 skipped` |
| `u_net` | `Results: 20 total, 20 passed, 0 failed` |
| `u_rtl` | `Results: 26 total, 25 passed, 1 failed, 1 skipped` |
| `u_sffi` | `Results: 13 total, 8 passed, 5 failed, 5 skipped` |
| `u_spec` | `Results: 137 total, 49 passed, 88 failed, 87 skipped` |
| `u_t32_mcp` | `Results: 24 total, 24 passed, 0 failed` |
| `u_test_runner` | `Results: 32 total, 27 passed, 5 failed, 5 skipped` |

## 3. Ranked taxonomy — `test/system/` (57 failed examples measured)

| class | files | examples | cum % | representative error |
|---|---|---|---|---|
| `SUBPROCESS_EXIT_NONZERO` | 6 | 22 | 38.6 | Process exited with code 1 |
| `OBJECT_TYPE_ERASURE` | 4 | 22 | 77.2 | semantic: method `executed_files` not found on type `object` (receiver value: CoverageCollector(line_hits: {}, function_calls: {})); semantic: method  |
| `UNRESOLVED_MODULE` | 2 | 2 | 80.7 | error: semantic: Cannot resolve module: compiler.driver.build.coverage |
| `FUNCTION_NOT_FOUND` | 2 | 11 | 100.0 | semantic: function `parse_ui_file` not found; semantic: function `parse_ui_file` not found; semantic: function `parse_ui_file` not found |

## 4. Ranked taxonomy — `test/unit/` (450 failed examples measured)

| class | files | examples | cum % | representative error |
|---|---|---|---|---|
| `OBJECT_TYPE_ERASURE` | 22 | 369 | 82.0 | semantic: undefined field 'width': cannot access field on value of type 'object'; semantic: undefined field 'height': cannot access field on value of  |
| `SUBPROCESS_EXIT_NONZERO` | 6 | 61 | 95.6 | Process exited with code 1 |
| `UNRESOLVED_MODULE` | 2 | 2 | 96.0 | error: semantic: Cannot resolve module: doc.fpga.de10nano_quartus_setup |
| `METHOD_NOT_FOUND_CONCRETE` | 1 | 4 | 96.9 | semantic: method `to_int_or` not found on type `str` (receiver value: 42); semantic: method `to_int_or` not found on type `str` (receiver value: 0); s |
| `NO_SUMMARY_PARSE` | 1 | 1 | 97.1 | no parseable pass/fail summary in test output; refusing synthetic pass |
| `UNKNOWN_VARIANT_OR_STATIC` | 1 | 4 | 98.0 | semantic: unknown variant or method 'some' on enum Option; semantic: unknown variant or method 'none' on enum Option; semantic: unknown variant or met |
| `FUNCTION_NOT_FOUND` | 1 | 5 | 99.1 | semantic: unknown extern function: rt_cli_read_file; semantic: function `of` not found; semantic: function `of` not found |
| `MISC_UNCLASSIFIED` | 1 | 3 | 99.8 | semantic: array index out of bounds: index is 0 but length is 0; semantic: function expects 2 argument(s), but 3 were provided; error: semantic: panic |
| `MODULE_MISSING_EXPORT` | 1 | 1 | 100.0 | error: runtime: Module "spec" does not export 'matchers' |

## 5. Env-limited split

This lane excludes env-unsupported work (macOS/Windows qualification,
Vulkan-everywhere, GPU, RV64 board). Failures whose error text names an
env-limited dependency, counted separately and **not** proposed for fixing:

| tree | env class | failing files |
|---|---|---|
| system | `BOARD_HW` | 1 |
| unit | `GPU_VULKAN` | 3 |
| unit | `BOARD_HW` | 1 |

The env-limited share is small: the dominant classes in both trees are
compiler/interpreter semantic defects, not missing hardware. Notably
`test/unit/gpu` (`Results: 138 total, 9 passed, 129 failed, 126 skipped`) is
*not* purely a GPU-availability failure — only 3 of its failing files name a
GPU/Vulkan dependency; the rest fail on the same semantic classes as the rest of
the tree.

`test/system/qemu` (38 specs) is INCONCLUSIVE and unmeasured, so the true
env-limited share of `test/system/` is a **lower bound** and will rise when that
shard lands.

## 6. Mirror duplication — do not double-count

`test/unit/` and `test/01_unit/` are duplicate mirror trees, as are
`test/system/` and `test/03_system/`. Measured by path-set and byte comparison:

| pair | A specs | B specs | shared paths | byte-identical | unique to A |
|---|---|---|---|---|---|
| `test/unit/` vs `test/01_unit/` | 5124 | 8223 | **5117 (99.9% of A)** | 4350 | **7** |
| `test/system/` vs `test/03_system/` | 1859 | 3443 | 337 (18% of A) | 273 | **1522** |

* **`test/unit/` is essentially a strict subset mirror of `test/01_unit/`.** 5117
  of its 5124 specs exist at the same relative path under `test/01_unit/`, and
  4350 are byte-identical. Only **7 spec files are unique to `test/unit/`**.
  Any `test/unit/` failure count is therefore ~99.9% a re-report of
  already-measured `test/01_unit/` results and **must not be added** to a
  repo-wide total. The 767 shared-path-but-differing-content files are the only
  place `test/unit/` can yield genuinely new information.
* **`test/system/` is NOT mostly a mirror.** Only 337 of 1859 specs share a path
  with `test/03_system/`. **1522 specs (82%) are unique to `test/system/`**, so
  this tree is genuine new measurement and its counts stand on their own.

## 7. What this record does not claim

* It is not a full-tree baseline. 63 of 91 shards are INCONCLUSIVE.
* No test was fixed, skipped, or marked expected-fail.
* The failing-example counts are per-shard sums; a spec file that aborts records
  its remaining examples as skipped, so example counts track file-level events
  (the same cascade documented in the sibling taxonomy).
