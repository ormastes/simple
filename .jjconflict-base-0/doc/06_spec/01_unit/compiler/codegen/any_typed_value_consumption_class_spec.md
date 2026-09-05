# Any Typed Value Consumption Class Specification

> Tests covering an ANY-typed value must be decoded at every consumption site.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Any Typed Value Consumption Class Specification

## Scenarios

### an ANY-typed value must be decoded at every consumption site

#### reads elements of an untyped `list` as numbers, not as boxed words

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads elements of an untyped `list` as numbers, not as boxed words
- Run the run-path probe under the cranelift JIT
- The typed-array control arm proves the fixture itself is sound
- `xs: list` must read 10, not 10 << 3 == 80
- Arithmetic over two untyped elements must not scale by 8


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads elements of an untyped `list` as numbers, not as boxed words")
step("Run the run-path probe under the cranelift JIT")
val jit = run_probe_in_mode("jit")

step("The typed-array control arm proves the fixture itself is sound")
expect(jit).to_contain("PASS typed_array_elem_mask")

step("`xs: list` must read 10, not 10 << 3 == 80")
expect(jit).to_contain("PASS list_elem_mask")

step("Arithmetic over two untyped elements must not scale by 8")
expect(jit).to_contain("PASS list_elem_add")
```

</details>

#### converts a CHAINED text builtin result, not its heap pointer

- converts a CHAINED text builtin result, not its heap pointer
- The direct form records a STRING receiver and already works
- Every text-in/text-out builtin must classify its result as text so the chained .to_i64() routes to rt_string_to_int


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("converts a CHAINED text builtin result, not its heap pointer")
val jit = run_probe_in_mode("jit")

step("The direct form records a STRING receiver and already works")
expect(jit).to_contain("PASS text_to_i64_direct")

step("Every text-in/text-out builtin must classify its result as text so the chained .to_i64() routes to rt_string_to_int")
expect(jit).to_contain("PASS text_to_i64_after_trim")
expect(jit).to_contain("PASS text_to_i64_after_upper")
expect(jit).to_contain("PASS text_to_i64_after_replace")
```

</details>

#### renders an untyped function result as a number

- renders an untyped function result as a number
- A tagged word that reached rendering leaks as `<value:0x..>`
   - Expected: jit does not contain `<value:0x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("renders an untyped function result as a number")
val jit = run_probe_in_mode("jit")

step("A tagged word that reached rendering leaks as `<value:0x..>`")
expect(jit).to_contain("PASS untyped_fn_result_add")
expect(jit).to_contain("PASS untyped_fn_result_id")
expect(jit.contains("<value:0x")).to_equal(false)
```

</details>

#### shows the same answers on the interpreter, the correctness oracle

- shows the same answers on the interpreter, the correctness oracle
- The interpreter decodes tags dynamically per value and is the reference


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("shows the same answers on the interpreter, the correctness oracle")
val interp = run_probe_in_mode("interpreter")

step("The interpreter decodes tags dynamically per value and is the reference")
expect(interp).to_contain("ANY_TYPED_CONSUMPTION PROBE: ALL PASS")
```

</details>

#### has no failing check under either engine

- has no failing check under either engine
- The aggregate verdict line is the authoritative result
   - Expected: jit does not contain `FAIL `
   - Expected: interp does not contain `FAIL `


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has no failing check under either engine")
val jit = run_probe_in_mode("jit")
val interp = run_probe_in_mode("interpreter")

step("The aggregate verdict line is the authoritative result")
expect(jit).to_contain("ANY_TYPED_CONSUMPTION PROBE: ALL PASS")
expect(jit.contains("FAIL ")).to_equal(false)
expect(interp.contains("FAIL ")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/any_typed_value_consumption_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering an ANY-typed value must be decoded at every consumption site.
- an ANY-typed value must be decoded at every consumption site

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `afdadc4e1a98717ce7ddf407473068dd97d796125c0b207e6953b84c10e3e434`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `afdadc4e1a98717ce7ddf407473068dd97d796125c0b207e6953b84c10e3e434`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `afdadc4e1a98717ce7ddf407473068dd97d796125c0b207e6953b84c10e3e434`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/any_typed_value_consumption_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/any_typed_value_consumption_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/any_typed_value_consumption_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/any_typed_value_consumption_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/any_typed_value_consumption_class_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads elements of an untyped `list` as numbers, not as boxed words' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/any_typed_value_consumption_class_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts a CHAINED text builtin result, not its heap pointer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/any_typed_value_consumption_class_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders an untyped function result as a number' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
