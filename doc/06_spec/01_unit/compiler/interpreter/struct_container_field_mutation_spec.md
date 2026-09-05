# Struct Container Field Mutation Specification

> Tests covering struct container-field mutation through a by-value receiver.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Struct Container Field Mutation Specification

## Scenarios

### struct container-field mutation through a by-value receiver

#### keeps a dict write made by a free function taking the struct as self

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps a dict write made by a free function taking the struct as self
- Build a struct whose only field is an empty dict
- Mutate that dict through a free function whose parameter is named self
   - Expected: result equals `1`
- The caller must observe the write — this is the assertion that was red
   - Expected: holder.values.has("answer") is true
- Absence control: a key nobody wrote must still be absent
   - Expected: holder.values.has("never-written") is false
- The stored VALUE must survive, not merely the key
   - Expected: holder.values["answer"] equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps a dict write made by a free function taking the struct as self")
step("Build a struct whose only field is an empty dict")
val holder = StructDictHolder(values: {})

step("Mutate that dict through a free function whose parameter is named self")
val result = write_struct_dict(holder, "answer", 42)
expect(result).to_equal(1)

step("The caller must observe the write — this is the assertion that was red")
expect(holder.values.has("answer")).to_equal(true)

step("Absence control: a key nobody wrote must still be absent")
expect(holder.values.has("never-written")).to_equal(false)

step("The stored VALUE must survive, not merely the key")
expect(holder.values["answer"]).to_equal(42)
```

</details>

#### keeps the same dict write when the holder is a reference-typed class

- keeps the same dict write when the holder is a reference-typed class
- A class receiver was never in question — it is the A/B control
   - Expected: result equals `1`
- Present key observed, absent key still absent
   - Expected: holder.values.has("answer") is true
   - Expected: holder.values.has("never-written") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the same dict write when the holder is a reference-typed class")
step("A class receiver was never in question — it is the A/B control")
val holder = ClassDictHolder(values: {})
val result = write_class_dict(holder, "answer", 42)
expect(result).to_equal(1)

step("Present key observed, absent key still absent")
expect(holder.values.has("answer")).to_equal(true)
expect(holder.values.has("never-written")).to_equal(false)
```

</details>

#### agrees between the interpreter and the JIT on the same source

- agrees between the interpreter and the JIT on the same source
- Run one identical program through both engines as subprocesses
- Both engines must report the write as visible
- Both engines must report the absence control as absent
- Both engines must have actually run the helper


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("agrees between the interpreter and the JIT on the same source")
step("Run one identical program through both engines as subprocesses")
val interpreted = run_cross_engine("interpreter")
val jitted = run_cross_engine("jit")

step("Both engines must report the write as visible")
expect(interpreted).to_contain("present=true")
expect(jitted).to_contain("present=true")

step("Both engines must report the absence control as absent")
expect(interpreted).to_contain("absent=false")
expect(jitted).to_contain("absent=false")

step("Both engines must have actually run the helper")
expect(interpreted).to_contain("r=1")
expect(jitted).to_contain("r=1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/struct_container_field_mutation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering struct container-field mutation through a by-value receiver.
- struct container-field mutation through a by-value receiver

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

- Canonical SPipe generation for source `9a745d802305a355a35dabd09537518d454c7eb518fb6b56ae88c326414ee1b3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9a745d802305a355a35dabd09537518d454c7eb518fb6b56ae88c326414ee1b3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9a745d802305a355a35dabd09537518d454c7eb518fb6b56ae88c326414ee1b3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/interpreter/struct_container_field_mutation_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/struct_container_field_mutation_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/struct_container_field_mutation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/struct_container_field_mutation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/struct_container_field_mutation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/struct_container_field_mutation_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a dict write made by a free function taking the struct as self' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/struct_container_field_mutation_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the same dict write when the holder is a reference-typed class' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/struct_container_field_mutation_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees between the interpreter and the JIT on the same source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
