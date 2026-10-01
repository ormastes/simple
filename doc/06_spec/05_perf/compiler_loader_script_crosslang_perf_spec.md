# Compiler, loader, and script cross-language performance B+B

> This system-performance contract proves the executable loader negative-cache

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler, loader, and script cross-language performance B+B

This system-performance contract proves the executable loader negative-cache

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/compiler_loader_script_crosslang_perf_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This system-performance contract proves the executable loader negative-cache
behavior and inspects the fail-closed cross-language harness and byte oracle.
The admitted self-hosted p95, RSS, and syscall rows remain explicitly blocked;
source contracts and bootstrap-seed diagnostics do not satisfy those budgets.

## Scenarios

### Compiler loader script cross-language performance B+B

#### packs exact facade totals and failed existence probes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- packs exact facade totals and failed existence probes
- Check two deterministic missing facade calls
   - Expected: check_exact_failed_existence_probe_packing() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("packs exact facade totals and failed existence probes")
step("Check two deterministic missing facade calls")
expect(check_exact_failed_existence_probe_packing()).to_equal("")
```

</details>

#### should reuse an exact unresolved module result within one cache generation

- should reuse an exact unresolved module result within one cache generation
- Prepare equivalent performance fixtures
   - Expected: first equals `second`
   - Expected: module_resolve_uncached_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("should reuse an exact unresolved module result within one cache generation")
step("Prepare equivalent performance fixtures")
module_resolve_cache_reset()
val first = resolve_module_path(
    "definitely_nonexistent_perf_negative_cache",
    "test/05_perf/compiler_loader_script_crosslang_perf_spec.spl"
)
val second = resolve_module_path(
    "definitely_nonexistent_perf_negative_cache",
    "test/05_perf/compiler_loader_script_crosslang_perf_spec.spl"
)
expect(first).to_equal(second)
expect(module_resolve_uncached_count()).to_equal(1)
```

</details>

#### should preserve caller-sensitive misses and invalidate them on reset

- should preserve caller-sensitive misses and invalidate them on reset
- Verify optimized paths preserve behavior and budgets
   - Expected: first equals `adjacent`
   - Expected: module_resolve_uncached_count() equals `2`
   - Expected: after_reset equals `first`
   - Expected: module_resolve_uncached_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("should preserve caller-sensitive misses and invalidate them on reset")
step("Verify optimized paths preserve behavior and budgets")
module_resolve_cache_reset()
val module_name = "definitely_nonexistent_perf_adjacent_cache"
val first = resolve_module_path(module_name, "test/05_perf/a.spl")
val adjacent = resolve_module_path(module_name, "test/03_system/b.spl")
expect(first).to_equal(adjacent)
expect(module_resolve_uncached_count()).to_equal(2)

module_resolve_cache_reset()
val after_reset = resolve_module_path(module_name, "test/05_perf/a.spl")
expect(after_reset).to_equal(first)
expect(module_resolve_uncached_count()).to_equal(1)
```

</details>

#### cuts failed existence probes across 100 uncached and 1000 retained resolutions

- cuts failed existence probes across 100 uncached and 1000 retained resolutions
- Measure failed existence probes at the file-exists facade
   - Expected: check_failed_existence_probe_cache_gate() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("cuts failed existence probes across 100 uncached and 1000 retained resolutions")
step("Measure failed existence probes at the file-exists facade")
expect(check_failed_existence_probe_cache_gate()).to_equal("")
```

</details>

#### keeps the probe provider native-atomic and Simple-core fail-closed

- keeps the probe provider native-atomic and Simple-core fail-closed
- Audit C, Rust, and interpreter-provider probe contracts


<details>
<summary>Executable SSpec</summary>

Runnable source: 75 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("keeps the probe provider native-atomic and Simple-core fail-closed")
step("Audit C, Rust, and interpreter-provider probe contracts")
val bootstrap_c_runtime = file_read(BOOTSTRAP_C_RUNTIME)
val c_runtime = file_read(C_RUNTIME)
val runtime_header = file_read(RUNTIME_HEADER)
val c_probe_selfcheck = file_read(C_PROBE_SELFCHECK)
val c_probe_script = file_read(C_PROBE_SCRIPT)
val text_extern_abi_router = file_read(TEXT_EXTERN_ABI_ROUTER)
val llvm_backend = file_read(LLVM_BACKEND)
val llvm_lib_translate = file_read(LLVM_LIB_TRANSLATE)
val sffi_minimal = file_read(SFFI_MINIMAL)
val interpreter_calls = file_read(INTERPRETER_CALLS)
val rust_runtime = file_read(RUST_RUNTIME)
val rust_file_io_exports = file_read(RUST_FILE_IO_EXPORTS)
val rust_value_exports = file_read(RUST_VALUE_EXPORTS)
val codegen_exports = file_read(CODEGEN_EXPORTS)
val simple_core_provider = file_read(SIMPLE_CORE_PROVIDER)
val interpreter_exports = file_read(INTERPRETER_EXPORTS)
expect(bootstrap_c_runtime).to_contain("rt_file_exists_probe_lease_admit")
expect(bootstrap_c_runtime).to_contain("rt_file_exists_probe_try_add_total")
expect(bootstrap_c_runtime).to_contain("rt_file_exists_probe_test_seed_counters")
expect(bootstrap_c_runtime).to_contain("rt_file_exists_probe_record(lease, exists)")
expect(bootstrap_c_runtime).to_contain("RT_FILE_EXISTS_PROBE_GENERATION_MAX UINT64_C(0x7fffffffffffffff)")
expect(bootstrap_c_runtime).to_contain("memory_order_relaxed")
expect(c_runtime).to_contain("rt_file_exists_probe_begin")
expect(c_runtime).to_contain("rt_file_exists_probe_end")
expect(c_runtime).to_contain("rt_file_exists_probe_lease_admit")
expect(c_runtime).to_contain("rt_file_exists_probe_try_add_total")
expect(c_runtime).to_contain("rt_file_exists_probe_test_seed_counters")
expect(c_runtime).to_contain("rt_file_exists_probe_record(lease, exists)")
expect(c_runtime).to_contain("RT_FILE_EXISTS_PROBE_GENERATION_MAX UINT64_C(0x7fffffffffffffff)")
expect(c_runtime).to_contain("memory_order_relaxed")
expect(runtime_header).to_contain("rt_file_exists_probe_begin")
expect(runtime_header).to_contain("rt_file_exists_probe_end")
expect(runtime_header).to_contain("SIMPLE_RUNTIME_TESTING")
expect(runtime_header).to_contain("rt_file_exists_probe_test_seed_counters")
expect(c_probe_selfcheck).to_contain("rt_file_exists_probe_test_seed_counters")
expect(c_probe_selfcheck).to_contain("access(missing, F_OK) == 0 || errno != ENOENT")
expect(c_probe_script).to_contain("runtime.c runtime_native.c")
expect(c_probe_script).to_contain("-DSIMPLE_RUNTIME_TESTING")
expect(rust_runtime).to_contain("FILE_EXISTS_PROBE_STATE")
expect(rust_runtime).to_contain("Ordering::Relaxed")
expect(rust_runtime).to_contain("rt_file_exists_probe_end")
expect(rust_runtime).to_contain("file_exists_probe_lease_admit")
expect(rust_runtime).to_contain("file_exists_probe_record(lease, exists)")
expect(rust_runtime).to_contain("file_exists_probe_try_add_total")
expect(rust_runtime).to_contain("file_exists_probe_test_seed_counters")
expect(rust_runtime).to_contain("0x7fff_ffff_ffff_ffff")
expect(rust_runtime).to_contain("file_exists_probe_after_admit_test_hook")
expect(rust_runtime).to_contain("file_exists_probe_end_closed_test_hook")
expect(rust_file_io_exports).to_contain("rt_file_exists_probe_begin")
expect(rust_file_io_exports).to_contain("rt_file_exists_probe_end")
expect(rust_value_exports).to_contain("rt_file_exists_probe_begin")
expect(rust_value_exports).to_contain("rt_file_exists_probe_end")
expect(codegen_exports).to_contain("rt_file_exists_probe_begin")
expect(codegen_exports).to_contain("rt_file_exists_probe_end")
expect(simple_core_provider).to_contain("single-thread, fail-closed")
expect(simple_core_provider).to_contain("rt_file_exists_probe_begin")
expect(simple_core_provider).to_contain("rt_file_exists_probe_end")
expect(simple_core_provider).to_contain("file_exists_probe_lease_admit")
expect(simple_core_provider).to_contain("file_exists_probe_record(lease, exists)")
expect(simple_core_provider).to_contain("file_exists_probe_test_seed_counters")
expect(interpreter_exports).to_contain("rt_file_exists_probe_begin")
expect(interpreter_exports).to_contain("rt_file_exists_probe_end")
expect(text_extern_abi_router).to_contain("rt_file_exists_probe_begin")
expect(text_extern_abi_router).to_contain("rt_file_exists_probe_end")
expect(llvm_backend).to_contain("declare i64 @rt_file_exists_probe_begin()")
expect(llvm_backend).to_contain("declare i64 @rt_file_exists_probe_end(i64)")
expect(llvm_lib_translate).to_contain("rt_file_exists_probe_begin")
expect(llvm_lib_translate).to_contain("rt_file_exists_probe_end")
expect(sffi_minimal).to_contain("extern fn rt_file_exists_probe_begin() -> i64")
expect(sffi_minimal).to_contain("extern fn rt_file_exists_probe_end(token: i64) -> i64")
expect(interpreter_calls).to_contain("rt_file_exists_probe_begin")
expect(interpreter_calls).to_contain("rt_file_exists_probe_end")
```

</details>

#### isolates the direct missing-path fixture per process

- isolates the direct missing-path fixture per process
- Reject a preexisting fixture without deleting any path


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("isolates the direct missing-path fixture per process")
step("Reject a preexisting fixture without deleting any path")
val fixture = file_read("test/05_perf/compiler_loader_script_crosslang_perf_spec.spl")
expect(fixture).to_contain("getpid().to_text()")
expect(fixture).to_contain("fixture unexpectedly exists")
```

</details>

#### should reject non-self-hosted Simple evidence before measurement

- should reject non-self-hosted Simple evidence before measurement
- Admit executable identity and execution modes


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("should reject non-self-hosted Simple evidence before measurement")
step("Admit executable identity and execution modes")
val harness = file_read(HARNESS)
expect(harness).to_contain("require-self-hosted.shs")
expect(harness).to_contain("require_self_hosted \"$SIMPLE_BINARY\" \"cross-language compiler\"")
expect(harness).to_contain("identity gate rejects Rust bootstrap seeds")
expect(harness).to_contain("SIMPLE_COMPILER_PROVENANCE must name the admitted Stage 3 manifest or adjacent Stage 4 provenance receipt")
expect(harness).to_contain("stage4_verify_candidate_provenance")
expect(harness).to_contain("bootstrap_stage3_verify_manifest")
expect(harness).to_contain("SIMPLE_NO_STUB_FALLBACK=1")
```

</details>

#### should include Rust and checksum equivalent warm work

- should include Rust and checksum equivalent warm work
- Compare cross-language semantic parity


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("should include Rust and checksum equivalent warm work")
step("Compare cross-language semantic parity")
val harness = file_read(HARNESS)
expect(harness).to_contain("write_rust_fib_warm")
expect(harness).to_contain("rustc -C opt-level=2")
expect(harness).to_contain("Rust (rustc -O)")
expect(harness).to_contain("checksum contract requires FIB_N=35")
expect(harness).to_contain(r"fib(35) = {checksum}")
expect(harness).to_contain("fib(35) = 9227465")
expect(harness).to_contain("checksum_mismatch")
expect(harness).to_contain("std::hint::black_box")
```

</details>

#### should fail closed instead of labeling fallback as interpreter evidence

- should fail closed instead of labeling fallback as interpreter evidence
- Admit executable identity and execution modes


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("should fail closed instead of labeling fallback as interpreter evidence")
step("Admit executable identity and execution modes")
val harness = file_read(HARNESS)
expect(harness).to_contain("Source execution can silently JIT/fallback")
expect(harness).to_contain("not labeled interpreter")
expect(harness).to_contain("blocked: no final-engine actual-mode receipt")
expect(harness).to_contain("blocked: no final-loader actual-mode receipt")
```

</details>

#### should retain compiler and native comparison provenance for installed toolchains

- should retain compiler and native comparison provenance for installed toolchains
- Compare cross-language semantic parity


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("should retain compiler and native comparison provenance for installed toolchains")
step("Compare cross-language semantic parity")
val harness = file_read(HARNESS)
expect(harness).to_contain("Retained Comparable Results")
expect(harness).to_contain("compiler_sha256")
expect(harness).to_contain("wall_samples_ms")
expect(harness).to_contain("wall_ms_p95")
expect(harness).to_contain("max_rss_kib")
expect(harness).to_contain("retained_compile_measure ||")
expect(harness).to_contain("simple_compiler_native")
expect(harness).to_contain("if have gcc; then [ -x \"$BUILD_DIR/fib_warm_c\" ]")
expect(harness).to_contain("if have rustc; then [ -x \"$BUILD_DIR/fib_warm_rust\" ]")
expect(harness).to_contain("if have go; then [ -x \"$BUILD_DIR/fib_warm_go\" ]")
```

</details>

#### should validate requested byte length and content before memory claims

- should validate requested byte length and content before memory claims
- Measure compiler loader and script rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("should validate requested byte length and content before memory claims")
step("Measure compiler loader and script rows")
val fixture = file_read(BYTE_FIXTURE)
val harness = file_read(HARNESS)
expect(fixture).to_contain("if buf.len() != n")
expect(fixture).to_contain(r"requested={n} actual_len={buf.len()}")
expect(fixture).to_contain("buf[0]")
expect(fixture).to_contain("buf[buf.len() - 1]")
expect(fixture).to_contain("zero_fill_checksum")
expect(fixture).to_contain("measure(\"32 MiB\", 33554432)")
expect(harness).to_contain("retained_byte_measure \"1 MiB\" 1048576")
expect(harness).to_contain("total process RSS")
```

</details>

#### should retain p95 RSS and failed-probe budgets as blocked until admitted evidence exists

- should retain p95 RSS and failed-probe budgets as blocked until admitted evidence exists
- Verify optimized paths preserve behavior and budgets


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("should retain p95 RSS and failed-probe budgets as blocked until admitted evidence exists")
step("Verify optimized paths preserve behavior and budgets")
val loader_record = file_read(LOADER_BUG)
val byte_record = file_read(BYTE_BUG)
expect(loader_record).to_contain("pending self-hosted reproduction")
expect(loader_record).to_contain("at least 90%")
expect(byte_record).to_contain("diagnostic rather than self-hosted release evidence")
expect(byte_record).to_contain("bounded RSS on an admitted self-hosted binary")
expect(byte_record).to_contain("admitted self-hosted memory row remains open")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-PERF`
- `REQ-001`
- `REQ-002`
- `REQ-003`
- `REQ-004`
- `REQ-005`
- `REQ-006`
- `REQ-007`
- `REQ-008`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `afbef99d8d2f2b912117c12efd3959fee17d30da96655a9995fd9034b4c61ca9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `afbef99d8d2f2b912117c12efd3959fee17d30da96655a9995fd9034b4c61ca9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `afbef99d8d2f2b912117c12efd3959fee17d30da96655a9995fd9034b4c61ca9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/05_perf/compiler_loader_script_crosslang_perf_spec.spl
mirror: doc/06_spec/05_perf/compiler_loader_script_crosslang_perf_spec.md (current)
findings: 13 blockers: 1
  narrative=100 structure=70 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/05_perf/compiler_loader_script_crosslang_perf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/compiler_loader_script_crosslang_perf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/compiler_loader_script_crosslang_perf_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/05_perf/compiler_loader_script_crosslang_perf_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 8 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/05_perf/compiler_loader_script_crosslang_perf_spec.spl:142:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'packs exact facade totals and failed existence probes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/compiler_loader_script_crosslang_perf_spec.spl:148:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reuse an exact unresolved module result within one cache generation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/05_perf/compiler_loader_script_crosslang_perf_spec.spl:148:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reuse an exact unresolved module result within one cache generation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/compiler_loader_script_crosslang_perf_spec.spl:164:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve caller-sensitive misses and invalidate them on reset' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/05_perf/compiler_loader_script_crosslang_perf_spec.spl:164:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve caller-sensitive misses and invalidate them on reset' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/compiler_loader_script_crosslang_perf_spec.spl:271:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject non-self-hosted Simple evidence before measurement' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/05_perf/compiler_loader_script_crosslang_perf_spec.spl:284:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should include Rust and checksum equivalent warm work' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/05_perf/compiler_loader_script_crosslang_perf_spec.spl:298:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail closed instead of labeling fallback as interpreter evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/05_perf/compiler_loader_script_crosslang_perf_spec.spl:308:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain compiler and native comparison provenance for installed toolchains' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
