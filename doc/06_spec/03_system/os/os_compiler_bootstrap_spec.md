# os_compiler_bootstrap_spec

> Source-contract inventory for SimpleOS libc and toolchain integration owners.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# os_compiler_bootstrap_spec

Source-contract inventory for SimpleOS libc and toolchain integration owners.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/os_compiler_bootstrap_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Source-contract inventory for SimpleOS libc and toolchain integration owners.

This spec proves that the maintained source/configuration surfaces remain
present. It is not compiler execution, image admission, guest execution, or
release evidence. In particular, Rust-seed and bin/simple presence are not
tested or accepted as bootstrap convergence.

## Scenarios

### SimpleOS compiler and libc source contract

#### should retain the libc build and header surface

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should retain the libc build and header surface
- Inspect the maintained SimpleOS libc build and headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain the libc build and header surface")
step("Inspect the maintained SimpleOS libc build and headers")
expect(all_files_exist([
    "src/os/libc/Makefile",
    "src/os/libc/include/stdio.h",
    "src/os/libc/include/stdlib.h",
    "src/os/libc/include/string.h",
    "src/os/libc/include/setjmp.h",
    "src/os/libc/include/pthread.h",
    "src/os/libc/include/math.h",
    "src/os/libc/include/errno.h",
])).to_be(true)
```

</details>

#### should retain the libc implementation surface

- should retain the libc implementation surface
- Inspect the maintained SimpleOS libc implementation owners


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain the libc implementation surface")
step("Inspect the maintained SimpleOS libc implementation owners")
expect(all_files_exist([
    "src/os/libc/simpleos_libc.c",
    "src/os/libc/simpleos_math.c",
    "src/os/libc/simpleos_math_ext.c",
    "src/os/libc/simpleos_fs.c",
    "src/os/libc/simpleos_process.c",
    "src/os/libc/simpleos_pthread.c",
    "src/os/libc/simpleos_alloc.c",
    "src/os/libc/simpleos_string_ext.c",
    "src/os/libc/simpleos_stdlib_ext.c",
    "src/os/libc/simpleos_time.c",
    "src/os/libc/simpleos_printf_float.c",
    "src/os/libc/simpleos_cxxabi.c",
    "src/os/libc/simpleos_dlmalloc.c",
    "src/os/libc/simpleos_signal.c",
])).to_be(true)
```

</details>

#### should retain the LLVM and Rust port configuration surfaces

- should retain the LLVM and Rust port configuration surfaces
- Inspect the maintained cross-toolchain port owners


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain the LLVM and Rust port configuration surfaces")
step("Inspect the maintained cross-toolchain port owners")
expect(all_files_exist([
    "src/os/port/llvm/build.shs",
    "src/os/port/llvm/sysroot.shs",
    "src/os/port/llvm/build.spl",
    "src/os/toolchain/llvm/simpleos_cross_toolchain.cmake",
    "src/os/port/llvm/test_smoke.spl",
    "src/os/toolchain/rust/x86_64-unknown-simpleos.json",
    "src/os/port/rust/build.shs",
    "src/os/port/rust/build.spl",
    "src/os/toolchain/rust/cargo_config.toml",
    "src/os/port/rust/examples/hello.rs",
    "src/os/port/rust/examples/ipc_sample.rs",
])).to_be(true)
```

</details>

#### should retain the production SimpleOS integration owners

- should retain the production SimpleOS integration owners
- Inspect the production SimpleOS build and acceptance owners


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain the production SimpleOS integration owners")
step("Inspect the production SimpleOS build and acceptance owners")
expect(all_files_exist([
    "scripts/os/simpleos-native-build.shs",
    "src/os/port/simpleos_native_build_config.spl",
    "src/os/port/build_tools/simple_make.spl",
    "test/03_system/os/simpleos_deploy_image_simple_toolchain_spec.spl",
    "test/03_system/os/simpleos_guest_toolchain_wrapper_spec.spl",
    "test/03_system/os/simpleos_toolchain_deployment_desktop_boot_spec.spl",
])).to_be(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `543d3ff8a622fa8e39c1f01a5aedbebeb5a4853338e28ca75fd91ed9114106f3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `543d3ff8a622fa8e39c1f01a5aedbebeb5a4853338e28ca75fd91ed9114106f3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `543d3ff8a622fa8e39c1f01a5aedbebeb5a4853338e28ca75fd91ed9114106f3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/os/os_compiler_bootstrap_spec.spl
mirror: doc/06_spec/03_system/os/os_compiler_bootstrap_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/os_compiler_bootstrap_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/os_compiler_bootstrap_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/os_compiler_bootstrap_spec.spl:31:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain the libc build and header surface' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/os_compiler_bootstrap_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should retain the libc build and header surface' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/os_compiler_bootstrap_spec.spl:46:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain the libc implementation surface' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/os_compiler_bootstrap_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should retain the libc implementation surface' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/os_compiler_bootstrap_spec.spl:67:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain the LLVM and Rust port configuration surfaces' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/os_compiler_bootstrap_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should retain the LLVM and Rust port configuration surfaces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/os_compiler_bootstrap_spec.spl:85:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain the production SimpleOS integration owners' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
