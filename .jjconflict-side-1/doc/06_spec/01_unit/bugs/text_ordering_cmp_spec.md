# Text Ordering (`<` `>` `<=` `>=`) Content Comparison Specification

> Regression guard for the P0 sspec false-green root cause: text `<` / `>` / `<=` / `>=` used to lower to a RAW POINTER (handle) integer compare on the native/cranelift codegen paths, producing address-dependent (context- sensitive) results instead of lexicographic byte comparison. Fixed by lowering text ordering compares through `rt_text_cmp_any` (strcmp-style signed result vs 0) in both the seed cranelift codegen (`src/compiler_rust/compiler/src/codegen/instr/core.rs`) and the self-hosted MIR lowering (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Ordering (`<` `>` `<=` `>=`) Content Comparison Specification

Regression guard for the P0 sspec false-green root cause: text `<` / `>` / `<=` / `>=` used to lower to a RAW POINTER (handle) integer compare on the native/cranelift codegen paths, producing address-dependent (context- sensitive) results instead of lexicographic byte comparison. Fixed by lowering text ordering compares through `rt_text_cmp_any` (strcmp-style signed result vs 0) in both the seed cranelift codegen (`src/compiler_rust/compiler/src/codegen/instr/core.rs`) and the self-hosted MIR lowering (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #P0-TEXT-ORDER-001 |
| Category | Runtime |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | doc/08_tracking/bug/sspec_test_path_false_green_undercount_2026-07-20.md |
| Source | `test/01_unit/bugs/text_ordering_cmp_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Regression guard for the P0 sspec false-green root cause: text `<` / `>` /
`<=` / `>=` used to lower to a RAW POINTER (handle) integer compare on the
native/cranelift codegen paths, producing address-dependent (context-
sensitive) results instead of lexicographic byte comparison. Fixed by
lowering text ordering compares through `rt_text_cmp_any` (strcmp-style
signed result vs 0) in both the seed cranelift codegen
(`src/compiler_rust/compiler/src/codegen/instr/core.rs`) and the self-hosted
MIR lowering (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`).

This spec must run on the sspec TEST path (the path that was broken);
`simple run` was always correct on all backends.

## Scenarios

### text ordering comparison is lexicographic content compare

#### orders distinct words alphabetically

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- orders distinct words alphabetically
   - Expected: "apple" < "banana" is true
   - Expected: "banana" < "apple" is false
   - Expected: "banana" > "apple" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("orders distinct words alphabetically")
expect("apple" < "banana").to_equal(true)
expect("banana" < "apple").to_equal(false)
expect("banana" > "apple").to_equal(true)
```

</details>

#### orders a prefix before its extension

- orders a prefix before its extension
   - Expected: "a" < "ab" is true
   - Expected: "ab" < "a" is false
   - Expected: "ab" > "a" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("orders a prefix before its extension")
expect("a" < "ab").to_equal(true)
expect("ab" < "a").to_equal(false)
expect("ab" > "a").to_equal(true)
```

</details>

#### orders single characters bytewise

- orders single characters bytewise
   - Expected: "b" > "a" is true
   - Expected: "a" < "b" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("orders single characters bytewise")
expect("b" > "a").to_equal(true)
expect("a" < "b").to_equal(true)
```

</details>

#### treats equal strings as neither < nor >

- treats equal strings as neither < nor >
   - Expected: a < b is false
   - Expected: a > b is false
   - Expected: a <= b is true
   - Expected: a >= b is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats equal strings as neither < nor >")
val a = "same"
val b = "same"
expect(a < b).to_equal(false)
expect(a > b).to_equal(false)
expect(a <= b).to_equal(true)
expect(a >= b).to_equal(true)
```

</details>

#### orders non-literal (runtime-built) strings by content

- orders non-literal (runtime-built) strings by content
   - Expected: ab < "ac" is true
   - Expected: ab > "aa" is true
   - Expected: ab < "ab" is false
   - Expected: ab >= "ab" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("orders non-literal (runtime-built) strings by content")
# Concat-produced strings exercise the tagged-heap-string operand
# shape (vs raw literal pointers) — both must compare by content.
val ab = "a" + "b"
expect(ab < "ac").to_equal(true)
expect(ab > "aa").to_equal(true)
expect(ab < "ab").to_equal(false)
expect(ab >= "ab").to_equal(true)
```

</details>

#### orders empty string before any non-empty string

- orders empty string before any non-empty string
   - Expected: "" < "a" is true
   - Expected: "a" > "" is true
   - Expected: "" < "" is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("orders empty string before any non-empty string")
expect("" < "a").to_equal(true)
expect("a" > "").to_equal(true)
expect("" < "").to_equal(false)
```

</details>

### text ordering is content-based for runtime-produced (untyped) operands

#### orders a substring result below the digit range

- orders a substring result below the digit range
   - Expected: _ge_zero("/") is false
   - Expected: _ge_zero(".") is false
   - Expected: _ge_zero(" ") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("orders a substring result below the digit range")
# '/' is 0x2F, one below '0' (0x30). PRE-FIX JIT: true (address order).
expect(_ge_zero("/")).to_equal(false)
expect(_ge_zero(".")).to_equal(false)
expect(_ge_zero(" ")).to_equal(false)
```

</details>

#### orders a substring result inside the digit range

- orders a substring result inside the digit range
   - Expected: _ge_zero("0") is true
   - Expected: _ge_zero("7") is true
   - Expected: _ge_zero("9") is true
   - Expected: _le_nine("0") is true
   - Expected: _le_nine("9") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("orders a substring result inside the digit range")
expect(_ge_zero("0")).to_equal(true)
expect(_ge_zero("7")).to_equal(true)
expect(_ge_zero("9")).to_equal(true)
expect(_le_nine("0")).to_equal(true)
expect(_le_nine("9")).to_equal(true)
```

</details>

#### orders a substring result above the digit range

- orders a substring result above the digit range
   - Expected: _ge_zero("a") is true
   - Expected: _le_nine("a") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("orders a substring result above the digit range")
expect(_ge_zero("a")).to_equal(true)
expect(_le_nine("a")).to_equal(false)
```

</details>

#### gives a correct lexicographic comparator for text sorting

- gives a correct lexicographic comparator for text sorting
   - Expected: _lower_lt("apple", "banana") is true
   - Expected: _lower_lt("banana", "apple") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gives a correct lexicographic comparator for text sorting")
# PRE-FIX JIT: both directions returned true, so the comparator was
# not even antisymmetric.
expect(_lower_lt("apple", "banana")).to_equal(true)
expect(_lower_lt("banana", "apple")).to_equal(false)
```

</details>

#### keeps the sorting comparator antisymmetric and irreflexive

- keeps the sorting comparator antisymmetric and irreflexive
   - Expected: _lower_lt("Zebra", "apple") is false
   - Expected: _lower_lt("apple", "Zebra") is true
   - Expected: _lower_lt("apple", "apple") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the sorting comparator antisymmetric and irreflexive")
expect(_lower_lt("Zebra", "apple")).to_equal(false)
expect(_lower_lt("apple", "Zebra")).to_equal(true)
expect(_lower_lt("apple", "apple")).to_equal(false)
```

</details>

### text ordering is correct on the JIT path (out of process)

#### passes the probe under the interpreter

- passes the probe under the interpreter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes the probe under the interpreter")
# Control column. The interpreter was correct throughout, so this
# arm failing means the probe or the harness broke, not codegen.
expect(engine_stdout(_PROBE, "interpret")).to_contain(_PASS)
```

</details>

#### passes the probe under the cranelift JIT

- passes the probe under the cranelift JIT


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes the probe under the cranelift JIT")
# The arm that carries the weight. Observed RED against a binary
# missing the rt_native_cmp runtime symbol, GREEN once present.
expect(engine_stdout(_PROBE, "jit")).to_contain(_PASS)
```

</details>

#### rejects an unrecognised engine name instead of silently using the JIT

- rejects an unrecognised engine name instead of silently using the JIT


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unrecognised engine name instead of silently using the JIT")
# SIMPLE_EXECUTION_MODE falls back to JIT on any unknown value, which
# would make an A/B comparison look like agreement.
assert_false(is_known_engine("interp"))
assert_true(is_known_engine("jit"))
assert_true(is_known_engine("interpret"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Research:** `doc/08_tracking/bug/sspec_test_path_false_green_undercount_2026-07-20.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f691cf85790c98e2c0b44db6a20cbf4a7242caaf69c6c8e5d8dba638de555b43`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f691cf85790c98e2c0b44db6a20cbf4a7242caaf69c6c8e5d8dba638de555b43`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f691cf85790c98e2c0b44db6a20cbf4a7242caaf69c6c8e5d8dba638de555b43`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/bugs/text_ordering_cmp_spec.spl
mirror: doc/06_spec/01_unit/bugs/text_ordering_cmp_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/bugs/text_ordering_cmp_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/bugs/text_ordering_cmp_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/bugs/text_ordering_cmp_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'orders distinct words alphabetically' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/bugs/text_ordering_cmp_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'orders a prefix before its extension' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/bugs/text_ordering_cmp_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'orders single characters bytewise' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
