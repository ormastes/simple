# Compiler Ffi Specification

> Tests covering Compiler Ffi.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler Ffi Specification

## Scenarios

### Compiler Ffi

#### creates a compiler context

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates a compiler context
   - Expected: ctx.alive is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a compiler context")
val ctx = CompilerContext.create()
expect(ctx.alive).to_equal(true)
```

</details>

#### builds primitive and named type info

- builds primitive and named type info
   - Expected: make_int_type(64, true).type_name equals `i64`
   - Expected: make_float_type(32).type_name equals `f32`
   - Expected: make_bool_type().type_name equals `bool`
   - Expected: make_string_type().type_name equals `string`
   - Expected: make_named_type("Widget").type_name equals `Widget`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds primitive and named type info")
expect(make_int_type(64, true).type_name).to_equal("i64")
expect(make_float_type(32).type_name).to_equal("f32")
expect(make_bool_type().type_name).to_equal("bool")
expect(make_string_type().type_name).to_equal("string")
expect(make_named_type("Widget").type_name).to_equal("Widget")
```

</details>

#### formats type arguments and byte lengths

- formats type arguments and byte lengths
   - Expected: type_args_is_empty(args) is false
   - Expected: type_args_is_empty([]) is true
   - Expected: type_to_string(args[0]) equals `Int`
   - Expected: code_bytes_len([1, 2, 3]) equals `3`
   - Expected: bytes_len([4, 5]) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats type arguments and byte lengths")
val args = [make_named_type("Int"), make_named_type("String")]
expect(type_args_is_empty(args)).to_equal(false)
expect(type_args_is_empty([])).to_equal(true)
expect(type_to_string(args[0])).to_equal("Int")
expect(code_bytes_len([1, 2, 3])).to_equal(3)
expect(bytes_len([4, 5])).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/loader/compiler_ffi_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Compiler Ffi.
- Compiler Ffi

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `0d03199d5ec7ad6814b5c5c54e4c18a6ddf92bff689e932fbf839db81f3dc4ac`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0d03199d5ec7ad6814b5c5c54e4c18a6ddf92bff689e932fbf839db81f3dc4ac`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0d03199d5ec7ad6814b5c5c54e4c18a6ddf92bff689e932fbf839db81f3dc4ac`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/compiler/loader/compiler_ffi_spec.spl
mirror: doc/06_spec/unit/compiler/loader/compiler_ffi_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/loader/compiler_ffi_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/loader/compiler_ffi_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/loader/compiler_ffi_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/loader/compiler_ffi_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a compiler context' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/loader/compiler_ffi_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds primitive and named type info' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/loader/compiler_ffi_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats type arguments and byte lengths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
