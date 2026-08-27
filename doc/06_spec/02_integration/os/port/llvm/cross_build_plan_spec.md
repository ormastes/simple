# Cross Build Plan Specification

> Tests covering SimpleOS LLVM cross-build --print-plan scaffolding, SimpleOS LLVM triple vocabulary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cross Build Plan Specification

## Scenarios

### SimpleOS LLVM cross-build --print-plan scaffolding

#### defines CROSS_SUPPORTED_TARGETS with 5 triples

- defines CROSS_SUPPORTED_TARGETS with 5 triples


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("defines CROSS_SUPPORTED_TARGETS with 5 triples")
"""CROSS_SUPPORTED_TARGETS constant must be declared."""
val src = build_source()
check(src.contains("val CROSS_SUPPORTED_TARGETS"))
```

</details>

#### includes x86_64-unknown-simpleos triple

- includes x86_64-unknown-simpleos triple


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("includes x86_64-unknown-simpleos triple")
"""x86_64 triple must appear in the supported-targets list."""
val src = build_source()
check(src.contains("x86_64-unknown-simpleos"))
```

</details>

#### includes aarch64-unknown-simpleos triple

- includes aarch64-unknown-simpleos triple


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("includes aarch64-unknown-simpleos triple")
val src = build_source()
check(src.contains("aarch64-unknown-simpleos"))
```

</details>

#### includes riscv64gc-unknown-simpleos triple

- includes riscv64gc-unknown-simpleos triple


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("includes riscv64gc-unknown-simpleos triple")
val src = build_source()
check(src.contains("riscv64gc-unknown-simpleos"))
```

</details>

#### includes riscv32imac-unknown-simpleos triple

- includes riscv32imac-unknown-simpleos triple


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("includes riscv32imac-unknown-simpleos triple")
val src = build_source()
check(src.contains("riscv32imac-unknown-simpleos"))
```

</details>

#### includes armv7-unknown-simpleos triple

- includes armv7-unknown-simpleos triple


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("includes armv7-unknown-simpleos triple")
val src = build_source()
check(src.contains("armv7-unknown-simpleos"))
```

</details>

#### maps triples via cross_llvm_arch_for

- maps triples via cross_llvm_arch_for


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("maps triples via cross_llvm_arch_for")
val src = build_source()
check(src.contains("fn cross_llvm_arch_for"))
```

</details>

#### maps armv7 to LLVM ARM

- maps armv7 to LLVM ARM


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("maps armv7 to LLVM ARM")
val src = build_source()
check(src.contains("triple.starts_with(\"armv7\")"))
check(src.contains("\"ARM\""))
```

</details>

#### normalizes runner separator before --cross dispatch

- normalizes runner separator before --cross dispatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("normalizes runner separator before --cross dispatch")
val src = build_source()
check(src.contains("args[0] == \"--\""))
check(src.contains("args = args.slice(1, args.len())"))
```

</details>

#### defines cross_build_print_plan

- defines cross_build_print_plan


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("defines cross_build_print_plan")
val src = build_source()
check(src.contains("fn cross_build_print_plan"))
```

</details>

#### defines cross_build_stage_for_target

- defines cross_build_stage_for_target


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("defines cross_build_stage_for_target")
val src = build_source()
check(src.contains("fn cross_build_stage_for_target"))
```

</details>

#### cross_build_status iterates all targets

- cross_build_status iterates all targets


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("cross_build_status iterates all targets")
val src = build_source()
check(src.contains("fn cross_build_status"))
check(src.contains("for triple in CROSS_SUPPORTED_TARGETS"))
```

</details>

#### exposes --targets CLI flag

- exposes --targets CLI flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("exposes --targets CLI flag")
val src = build_source()
check(src.contains("--targets"))
```

</details>

#### parses --targets as comma-separated triples

- parses --targets as comma-separated triples


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses --targets as comma-separated triples")
val src = build_source()
check(src.contains("override.split(\",\")"))
# Each CSV entry is normalized onto the canonical triple as it is
# collected, so downstream build dirs / env vars use one vocabulary.
check(src.contains("selected.push(canonical_simpleos_triple(trimmed))"))
```

</details>

#### exposes --all CLI flag

- exposes --all CLI flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("exposes --all CLI flag")
val src = build_source()
check(src.contains("--all"))
```

</details>

#### exposes --print-plan CLI flag

- exposes --print-plan CLI flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("exposes --print-plan CLI flag")
val src = build_source()
check(src.contains("--print-plan"))
```

</details>

#### per-target stage passes SIMPLEOS_TARGET_TRIPLE env var

- per-target stage passes SIMPLEOS_TARGET_TRIPLE env var


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("per-target stage passes SIMPLEOS_TARGET_TRIPLE env var")
val src = build_source()
check(src.contains("SIMPLEOS_TARGET_TRIPLE"))
```

</details>

#### per-target build dir is cross-<triple>

- per-target build dir is cross-<triple>


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("per-target build dir is cross-<triple>")
val src = build_source()
# Was `contains("cross-")`, which every header comment satisfied.
# Anchored to the real interpolated build-dir paths.
check(src.contains("val cross_dir = \"build/os/llvm/cross-{{triple}}/bin\""))
check(src.contains("build dir : build/os/llvm/cross-{{triple}}"))
```

</details>

#### rejects unsupported target overrides instead of skipping them

- rejects unsupported target overrides instead of skipping them


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects unsupported target overrides instead of skipping them")
val src = build_source()
check(src.contains("fn cross_target_supported"))
check(src.contains("if not cross_target_supported(triple):"))
check(src.contains("Unsupported SimpleOS target"))
check(!src.contains("Skip non-SimpleOS triple"))
```

</details>

#### requires compiler-rt to produce an archive before installation

- requires compiler-rt to produce an archive before installation


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("requires compiler-rt to produce an archive before installation")
val src = build_source()
check(src.contains("val archive_probe = process.run"))
check(src.contains("-type f -name 'libclang_rt.builtins*.a' -print -quit"))
check(src.contains("find {{rt_dir}} -name 'libclang_rt.builtins*.a' -exec cp"))
check(src.contains("archive_probe.stdout.trim() == \"\""))
check(src.contains("No builtins archive produced"))
```

</details>

#### makes cross-binary verification fail closed

- makes cross-binary verification fail closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("makes cross-binary verification fail closed")
val src = verifier_source()
# `{join2}` / `{join}` must be escaped as `{{...}}` — an unescaped brace
# is string interpolation and fails with "variable `join2` not found".
check(src.contains("use std.path.{{join2}}"))
check(!src.contains("use std.path.{{join}}"))
check(src.contains("FAIL (unknown target)"))
check(!src.contains("SKIP (unknown target)"))
check(src.contains("seed:    MISSING ({{seed_bin}})\"\n        return false"))
check(src.contains("simple:  NOT BUILT (run cross_compile.spl first)\"\n        return false"))
check(src.contains("qemu:    FAIL or no --help support\"\n                return false"))
check(src.contains("wine:    FAIL or no --help support\"\n                return false"))
check(src.contains("qemu:    FAIL (QEMU not installed)\"\n            return false"))
check(src.contains("wine:    FAIL (Wine not installed)\"\n            return false"))
check(!src.contains("qemu:    SKIP (QEMU not installed)"))
check(!src.contains("wine:    SKIP (Wine not installed)"))
check(src.contains("# Wine test for Windows\n    if (not quick and\n        not native_host and"))
check(src.contains("process_run_timeout(full_bin, [\"--help\"], 10000)"))
check(src.contains("target == \"macos-arm64\""))
check(src.contains("target == \"windows-x86_64\""))
check(src.contains("target == \"windows-x86\""))
check(src.contains("native:  FAIL or no --help support\"\n            return false"))
check(src.contains("{{qemu_cmd}} {{full_bin}} --help"))
check(src.contains("wine {{full_bin}} --help"))
check(!src.contains("{{qemu_cmd}} {{seed_bin}} --help"))
check(!src.contains("wine {{seed_bin}} --help"))
```

</details>

### SimpleOS LLVM triple vocabulary

#### normalizes the selector form onto the canonical triple

- normalizes the selector form onto the canonical triple
   - Expected: canonical_simpleos_triple("x86_64-simpleos") equals `x86_64-unknown-simpleos`
   - Expected: canonical_simpleos_triple("aarch64-simpleos") equals `aarch64-unknown-simpleos`
   - Expected: canonical_simpleos_triple("riscv64gc-simpleos") equals `riscv64gc-unknown-simpleos`
   - Expected: canonical_simpleos_triple("riscv32imac-simpleos") equals `riscv32imac-unknown-simpleos`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("normalizes the selector form onto the canonical triple")
"""`x86_64-simpleos` is a documented spelling; it must not be rejected."""
expect(canonical_simpleos_triple("x86_64-simpleos")).to_equal("x86_64-unknown-simpleos")
expect(canonical_simpleos_triple("aarch64-simpleos")).to_equal("aarch64-unknown-simpleos")
expect(canonical_simpleos_triple("riscv64gc-simpleos")).to_equal("riscv64gc-unknown-simpleos")
expect(canonical_simpleos_triple("riscv32imac-simpleos")).to_equal("riscv32imac-unknown-simpleos")
```

</details>

#### leaves an already-canonical triple untouched

- leaves an already-canonical triple untouched
   - Expected: canonical_simpleos_triple("x86_64-unknown-simpleos") equals `x86_64-unknown-simpleos`
   - Expected: canonical_simpleos_triple("armv7-unknown-simpleos") equals `armv7-unknown-simpleos`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("leaves an already-canonical triple untouched")
"""Normalization must be idempotent — no double vendor field."""
expect(canonical_simpleos_triple("x86_64-unknown-simpleos")).to_equal("x86_64-unknown-simpleos")
expect(canonical_simpleos_triple("armv7-unknown-simpleos")).to_equal("armv7-unknown-simpleos")
```

</details>

#### accepts both spellings of every supported triple

- accepts both spellings of every supported triple


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("accepts both spellings of every supported triple")
"""The core reconciliation: one vocabulary, two accepted input forms."""
assert_true(cross_target_supported("x86_64-unknown-simpleos"))
assert_true(cross_target_supported("x86_64-simpleos"))
assert_true(cross_target_supported("aarch64-unknown-simpleos"))
assert_true(cross_target_supported("aarch64-simpleos"))
assert_true(cross_target_supported("riscv64gc-simpleos"))
assert_true(cross_target_supported("riscv32imac-simpleos"))
assert_true(cross_target_supported("armv7-unknown-simpleos"))
```

</details>

#### still refuses host triples

- still refuses host triples


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("still refuses host triples")
"""The gate exists to stop a baremetal compiler-rt overwriting a host
toolchain — hosted triples must never be granted compiler-rt."""
assert_false(is_simpleos_triple("x86_64-unknown-linux-gnu"))
assert_false(cross_target_supported("x86_64-unknown-linux-gnu"))
assert_false(cross_target_supported("aarch64-apple-darwin"))
assert_false(cross_target_supported("x86_64-pc-windows-msvc"))
```

</details>

#### still refuses the empty triple

- still refuses the empty triple


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("still refuses the empty triple")
"""Fail-closed: an unset/blank target is refused, not defaulted."""
assert_false(is_simpleos_triple(""))
assert_false(cross_target_supported(""))
```

</details>

#### treats -simpleos as a suffix, not a substring

- treats -simpleos as a suffix, not a substring


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("treats -simpleos as a suffix, not a substring")
"""`simpleos-x86_64` and `x86_64-simpleos-foo` contain the token but do
not end in it; both must be refused."""
assert_false(is_simpleos_triple("simpleos-x86_64"))
assert_false(cross_target_supported("simpleos-x86_64"))
assert_false(is_simpleos_triple("x86_64-simpleos-foo"))
assert_false(cross_target_supported("x86_64-simpleos-foo"))
```

</details>

#### refuses an unknown arch that merely ends in -simpleos

- refuses an unknown arch that merely ends in -simpleos


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("refuses an unknown arch that merely ends in -simpleos")
"""Shape gate passes, allowlist must still reject — normalization is a
widening of accepted spellings, never of accepted architectures."""
assert_true(is_simpleos_triple("wat-simpleos"))
assert_false(cross_target_supported("wat-simpleos"))
assert_false(cross_target_supported("mips64-unknown-simpleos"))
```

</details>

#### normalization cannot launder a refused triple into acceptance

- normalization cannot launder a refused triple into acceptance
   - Expected: canonical_simpleos_triple("x86_64-unknown-linux-gnu") equals `x86_64-unknown-linux-gnu`
   - Expected: canonical_simpleos_triple("simpleos-x86_64") equals `simpleos-x86_64`
   - Expected: canonical_simpleos_triple("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("normalization cannot launder a refused triple into acceptance")
"""Anything failing the shape gate passes through unrewritten."""
expect(canonical_simpleos_triple("x86_64-unknown-linux-gnu")).to_equal("x86_64-unknown-linux-gnu")
expect(canonical_simpleos_triple("simpleos-x86_64")).to_equal("simpleos-x86_64")
expect(canonical_simpleos_triple("")).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/port/llvm/cross_build_plan_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS LLVM cross-build --print-plan scaffolding, SimpleOS LLVM triple vocabulary.
- SimpleOS LLVM cross-build --print-plan scaffolding
- SimpleOS LLVM triple vocabulary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0ef70b6deea0a00bb5e5f6b1dc159fc87e4b9f95d97e67449b493fa0833a2765`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0ef70b6deea0a00bb5e5f6b1dc159fc87e4b9f95d97e67449b493fa0833a2765`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0ef70b6deea0a00bb5e5f6b1dc159fc87e4b9f95d97e67449b493fa0833a2765`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/os/port/llvm/cross_build_plan_spec.spl
mirror: doc/06_spec/02_integration/os/port/llvm/cross_build_plan_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/os/port/llvm/cross_build_plan_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/os/port/llvm/cross_build_plan_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/os/port/llvm/cross_build_plan_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines CROSS_SUPPORTED_TARGETS with 5 triples' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/os/port/llvm/cross_build_plan_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes x86_64-unknown-simpleos triple' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/os/port/llvm/cross_build_plan_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes aarch64-unknown-simpleos triple' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
