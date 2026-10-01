# C Backend Export Wrapper Specification

> Checks that the C backend emits exported symbols using the same ABI-visible names as the header generators. In particular, standalone exported functions must use the `spl_` prefix unless the user provides an explicit custom name.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# C Backend Export Wrapper Specification

Checks that the C backend emits exported symbols using the same ABI-visible names as the header generators. In particular, standalone exported functions must use the `spl_` prefix unless the user provides an explicit custom name.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SFFI-BIDIR #SFFI-EXPORT-ABI |
| Category | Compiler / Backend / C Export |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/unit/compiler/backend/c_backend_export_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Checks that the C backend emits exported symbols using the same ABI-visible
names as the header generators. In particular, standalone exported functions
must use the `spl_` prefix unless the user provides an explicit custom name.

## Scenarios

### C backend export wrappers

#### prefixes standalone exported function names with spl

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- prefixes standalone exported function names with spl


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prefixes standalone exported function names with spl")
val func = make_exported_fn("__simple_add_numbers", "")
val module = make_module_with_export(func)
val translator = MirToC.create("test.export")

val output = translator.translate_module(module)

expect(output).to_contain("extern \"C\" int32_t spl_add_numbers(")
expect(output).to_not_contain("extern \"C\" int32_t add_numbers(")
```

</details>

#### preserves explicit custom export names

- preserves explicit custom export names


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves explicit custom export names")
val func = make_exported_fn("__simple_add_numbers", "custom_add")
val module = make_module_with_export(func)
val translator = MirToC.create("test.export")

val output = translator.translate_module(module)

expect(output).to_contain("extern \"C\" int32_t custom_add(")
expect(output).to_not_contain("extern \"C\" int32_t spl_add_numbers(")
```

</details>

#### emits typed opaque-handle wrappers for exported classes

- emits typed opaque-handle wrappers for exported classes


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits typed opaque-handle wrappers for exported classes")
val module = make_module_with_exported_type()
val translator = MirToC.create("test.export")

val output = translator.translate_module(module)

expect(output).to_contain("struct spl_Calculator {")
expect(output).to_contain("Calculator inner;")
expect(output).to_contain("extern \"C\" spl_Calculator_t spl_Calculator_create(")
expect(output).to_contain("obj->inner.precision = precision;")
expect(output).to_contain("extern \"C\" int32_t spl_Calculator_add(spl_Calculator_t self")
expect(output).to_contain("__simple_Calculator_add(&self->inner")
```

</details>

#### emits bitfield syntax in backend type definitions

- emits bitfield syntax in backend type definitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits bitfield syntax in backend type definitions")
val module = make_module_with_bitfield_type()
val translator = MirToC.create("test.export")

val output = translator.translate_module(module)

expect(output).to_contain("struct GpioRegister_s {")
expect(output).to_contain("uint8_t mode : 4;")
expect(output).to_contain("bool output : 1;")
expect(output).to_contain("bool input : 1;")
expect(output).to_contain("uint8_t speed : 2;")
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ca8a0cc4737e27f20d7a0d7d96c589074fd1b6d273098a72376d898a1dd6b435`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ca8a0cc4737e27f20d7a0d7d96c589074fd1b6d273098a72376d898a1dd6b435`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ca8a0cc4737e27f20d7a0d7d96c589074fd1b6d273098a72376d898a1dd6b435`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/backend/c_backend_export_spec.spl
mirror: doc/06_spec/unit/compiler/backend/c_backend_export_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/c_backend_export_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/c_backend_export_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/c_backend_export_spec.spl:150:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prefixes standalone exported function names with spl' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/c_backend_export_spec.spl:162:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves explicit custom export names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/c_backend_export_spec.spl:174:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits typed opaque-handle wrappers for exported classes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
