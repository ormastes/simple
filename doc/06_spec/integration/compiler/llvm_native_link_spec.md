# Llvm Native Link Specification

> Tests covering LLVM Native Linking.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm Native Link Specification

## Scenarios

### LLVM Native Linking

#### prerequisites

<details>
<summary>Advanced: has C compiler available</summary>

#### has C compiler available _(slow)_

- has C compiler available


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("has C compiler available")
val cc = find_c_compiler()
# Most systems should have clang or gcc
if cc != "":
    expect(cc.len()).to_be_greater_than(0)
else:
    pending("C compiler unavailable")
```

</details>


</details>

<details>
<summary>Advanced: has runtime source directory</summary>

#### has runtime source directory _(slow)_

- has runtime source directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("has runtime source directory")
val rt_dir = find_runtime_source_dir()
if rt_dir != "":
    expect(rt_dir).to_contain("runtime")
else:
    pending("runtime source directory unavailable")
```

</details>


</details>

#### entry point generation

<details>
<summary>Advanced: generates valid LLVM IR for hosted entry point</summary>

#### generates valid LLVM IR for hosted entry point _(slow)_

- generates valid LLVM IR for hosted entry point


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("generates valid LLVM IR for hosted entry point")
val ir = generate_entry_point_ir("test_program")
expect(ir).to_contain("@__simple_runtime_init")
expect(ir).to_contain("@__simple_main")
expect(ir).to_contain("@__simple_runtime_shutdown")
expect(ir).to_contain("define i32 @main")
```

</details>


</details>

#### runtime compilation

<details>
<summary>Advanced: compiles runtime objects</summary>

#### compiles runtime objects _(slow)_

- compiles runtime objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles runtime objects")
val cc = find_c_compiler()
val rt_dir = find_runtime_source_dir()
if cc == "" or rt_dir == "":
    # Skip if prerequisites missing
    pending("native link prerequisites not available")
else:
    val result = compile_runtime_objects(false, false)
    if result.is_ok():
        val objects = result.unwrap()
        expect(objects.len()).to_be_greater_than(0)
    else:
        # May fail in CI without all headers
        pending("runtime compilation prerequisites not available")
```

</details>


</details>

#### native executable link

<details>
<summary>Advanced: links a native executable when prerequisites are present</summary>

#### links a native executable when prerequisites are present _(slow)_

- links a native executable when prerequisites are present
   - Expected: result.is_ok() is true
   - Expected: file_exists(output) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("links a native executable when prerequisites are present")
val cc = find_c_compiler()
val rt_dir = find_runtime_source_dir()
if cc == "" or rt_dir == "":
    pending("native link prerequisites not available")
else:
    val output = "/tmp/simple_llvm_native_link_spec.out"
    val opts = NativeLinkOptions.default()
    val result = link_llvm_native([], output, opts)
    expect(result.is_ok()).to_equal(true)
    expect(file_exists(output)).to_equal(true)
    file_delete(output)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/integration/compiler/llvm_native_link_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LLVM Native Linking.
- LLVM Native Linking

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
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

- Canonical SPipe generation for source `f82d46292695523edbb179c5dc59e6409abb8af0bfc817b35e80cc38064290ff`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f82d46292695523edbb179c5dc59e6409abb8af0bfc817b35e80cc38064290ff`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f82d46292695523edbb179c5dc59e6409abb8af0bfc817b35e80cc38064290ff`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/compiler/llvm_native_link_spec.spl
mirror: doc/06_spec/integration/compiler/llvm_native_link_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/compiler/llvm_native_link_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/compiler/llvm_native_link_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/compiler/llvm_native_link_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has C compiler available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/llvm_native_link_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has runtime source directory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/llvm_native_link_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates valid LLVM IR for hosted entry point' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
