# Native `--entry-closure`: a struct returned by value must keep its field values

> A struct RETURNED BY VALUE from a function reads every field back as `1` once the program is built through `SIMPLE_BOOTSTRAP=1 bin/simple native-build --entry-closure`. A struct constructed inline in the same function is correct, so the corruption is in the aggregate RETURN transport, not in field layout.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native `--entry-closure`: a struct returned by value must keep its field values

A struct RETURNED BY VALUE from a function reads every field back as `1` once the program is built through `SIMPLE_BOOTSTRAP=1 bin/simple native-build --entry-closure`. A struct constructed inline in the same function is correct, so the corruption is in the aggregate RETURN transport, not in field layout.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Codegen / aggregate return ABI |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/native_struct_return_by_value_field_read_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

A struct RETURNED BY VALUE from a function reads every field back as `1` once
the program is built through
`SIMPLE_BOOTSTRAP=1 bin/simple native-build --entry-closure`. A struct
constructed inline in the same function is correct, so the corruption is in the
aggregate RETURN transport, not in field layout.

The failure is silent: the binary exits 0 and prints wrong numbers.

## Why this spec must shell out

Spec files fall back to the INTERPRETER, and both the interpreter and the
cranelift JIT are CORRECT here — measured directly:

```
interpreter: inline len=3 tag=77 returned len=3 tag=77
jit:         inline len=3 tag=77 returned len=3 tag=77
```

So the in-process examples below can never go red; they exist to pin the
correct answer for the two engines that already have it. The example that
actually reproduces the defect builds the reproducer with `native-build
--entry-closure` in a subprocess and runs the resulting binary — the same
shape as `test/01_unit/compiler/codegen/f32_struct_field_roundtrip_spec.spl`.

Pre-fix evidence from that path, verbatim:

```
inline len=3 tag=77returned len=1 tag=1
```

`inline` correct, `returned` wrong, in one process, same struct — which is the
whole oracle. A check that only asserted "fields are non-zero" would pass on
`1`, so the assertions below compare against the absolute stored values `3`
and `77`, and `77` is chosen because no field of the struct and no operand in
the program is `77` by accident.

## Cost

One `native-build` (minutes on a loaded host). The spec is deliberately a
single build with several assertions read off its one output line.

## Scenarios

### a struct returned by value keeps its field values

#### reads the stored values back from a locally constructed struct

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads the stored values back from a locally constructed struct
- Construct the struct inline, the shape that was always correct
- Compare against the absolute stored values, not against non-zero
   - Expected: inline_v.length equals `3`
   - Expected: inline_v.tag equals `77`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads the stored values back from a locally constructed struct")
step("Construct the struct inline, the shape that was always correct")
val inline_v = W3(ok: true, length: 3, tag: 77)

step("Compare against the absolute stored values, not against non-zero")
expect(inline_v.length).to_equal(3)
expect(inline_v.tag).to_equal(77)
```

</details>

#### reads the stored values back from a struct returned by a function

- reads the stored values back from a struct returned by a function
- Obtain the struct as a by-value return, the shape that corrupts
- Assert the exact values; the defect substitutes 1 for every field
   - Expected: ret_v.length equals `3`
   - Expected: ret_v.tag equals `77`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads the stored values back from a struct returned by a function")
step("Obtain the struct as a by-value return, the shape that corrupts")
val ret_v = make_w3(3)

step("Assert the exact values; the defect substitutes 1 for every field")
expect(ret_v.length).to_equal(3)
expect(ret_v.tag).to_equal(77)
expect(ret_v.ok).to_be(true)
```

</details>

#### agrees between a locally built struct and a returned one after native-build

- agrees between a locally built struct and a returned one after native-build
- Build the reproducer with native-build --entry-closure and run it
- Fail loudly if the build itself did not produce a binary
- The inline construction was never affected
- The returned struct must carry the same values, not 1
   - Expected: out does not contain `RETURNED\n1\n1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("agrees between a locally built struct and a returned one after native-build")
step("Build the reproducer with native-build --entry-closure and run it")
# This is the only example here that can go red — see the header.
val out = native_build_and_run()

step("Fail loudly if the build itself did not produce a binary")
# An unbuildable fixture must not read as a pass.
expect(out).to_contain("INLINE")
expect(out).to_contain("RETURNED")

step("The inline construction was never affected")
expect(out).to_contain("INLINE\n3\n77")

step("The returned struct must carry the same values, not 1")
expect(out).to_contain("RETURNED\n3\n77")
expect(out.contains("RETURNED\n1\n1")).to_equal(false)
```

</details>

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2dae24a6181e81b6d08e2fc1c1e4a77b1ad7407dee47357d7ebcfcab7ed043aa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2dae24a6181e81b6d08e2fc1c1e4a77b1ad7407dee47357d7ebcfcab7ed043aa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2dae24a6181e81b6d08e2fc1c1e4a77b1ad7407dee47357d7ebcfcab7ed043aa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/codegen/native_struct_return_by_value_field_read_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/native_struct_return_by_value_field_read_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/native_struct_return_by_value_field_read_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/native_struct_return_by_value_field_read_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/native_struct_return_by_value_field_read_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/codegen/native_struct_return_by_value_field_read_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads the stored values back from a locally constructed struct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/native_struct_return_by_value_field_read_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads the stored values back from a struct returned by a function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/native_struct_return_by_value_field_read_spec.spl:136:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees between a locally built struct and a returned one after native-build' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
