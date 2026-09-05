# Class-detection spec: name-resolved arguments must be order-independent

> Defect class (generalized from

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Class-detection spec: name-resolved arguments must be order-independent

Defect class (generalized from

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/name_resolved_argument_order_independence_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Defect class (generalized from
doc/08_tracking/bug/struct_shorthand_arg_order_binds_wrong_field_2026-07-20.md):

An argument that is bound by NAME -- either an explicit `name: value` argument
or a shorthand `name` argument whose identifier is the field/parameter name --
must resolve to the same slot regardless of what precedes it in the argument
list. Any binder that keeps a separate positional index alongside a
name-keyed pass can desynchronise the two once a named argument appears, and
then silently binds later arguments to the wrong slot (or to the type default,
which for i64 is 0 and for text is "" -- both silent wrong answers, not errors).

This spec probes the whole class, not just the one reported shape: shorthand at
every index, named args written out of declaration order, wide structs, text
and bool fields (whose defaults are NOT 0, so an index-desync shows up as a
different wrong value), and nested construction.

Runs interpreted -- the defect lives in the interpreter's argument binder.

## Scenarios

### name-resolved arguments bind independently of argument order

#### resolves a shorthand at each index after a leading named argument

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves a shorthand at each index after a leading named argument


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves a shorthand at each index after a leading named argument")
val b = 2
val c = 3
val t1 = NrTriple(a: 1, b, c)
expect t1.a == 1
expect t1.b == 2
expect t1.c == 3
```

</details>

#### resolves a shorthand sandwiched between two named arguments

- resolves a shorthand sandwiched between two named arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves a shorthand sandwiched between two named arguments")
val b = 2
val t2 = NrTriple(a: 1, b, c: 3)
expect t2.a == 1
expect t2.b == 2
expect t2.c == 3
```

</details>

#### resolves a trailing named argument after leading shorthands

- resolves a trailing named argument after leading shorthands


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves a trailing named argument after leading shorthands")
val a = 1
val b = 2
val t3 = NrTriple(a, b, c: 3)
expect t3.a == 1
expect t3.b == 2
expect t3.c == 3
```

</details>

#### resolves named arguments written out of declaration order

- resolves named arguments written out of declaration order


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves named arguments written out of declaration order")
val t4 = NrTriple(c: 3, a: 1, b: 2)
expect t4.a == 1
expect t4.b == 2
expect t4.c == 3
```

</details>

#### resolves a shorthand after an out-of-order named argument

- resolves a shorthand after an out-of-order named argument


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves a shorthand after an out-of-order named argument")
val a = 1
val b = 2
val t5 = NrTriple(c: 3, a, b)
expect t5.a == 1
expect t5.b == 2
expect t5.c == 3
```

</details>

#### keeps non-integer fields off the zero-default masking path

- keeps non-integer fields off the zero-default masking path


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps non-integer fields off the zero-default masking path")
# text and bool defaults differ from 0, so an index desync produces a
# visibly different wrong value here rather than a plausible 0.
val two = "two"
val three = true
val five = "five"
val w = NrWide(one: 1, two, three, four: 4, five)
expect w.one == 1
expect w.two == "two"
expect w.three == true
expect w.four == 4
expect w.five == "five"
```

</details>

#### resolves a shorthand whose value is a struct

- resolves a shorthand whose value is a struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves a shorthand whose value is a struct")
val inner = NrInner(v: 7)
val o = NrOuter(label: "outer", inner)
expect o.label == "outer"
expect o.inner.v == 7
```

</details>

#### resolves shorthands whose values come from expressions and calls

- resolves shorthands whose values come from expressions and calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves shorthands whose values come from expressions and calls")
val b = 1 + 1
val c = compute_three()
val t6 = NrTriple(a: 1, b, c)
expect t6.a == 1
expect t6.b == 2
expect t6.c == 3
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `32b5a48634e641881f984420cec1862ebe22b5f77e995fb944b5a6e79163ec36`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `32b5a48634e641881f984420cec1862ebe22b5f77e995fb944b5a6e79163ec36`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `32b5a48634e641881f984420cec1862ebe22b5f77e995fb944b5a6e79163ec36`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/frontend/name_resolved_argument_order_independence_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/name_resolved_argument_order_independence_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/name_resolved_argument_order_independence_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/name_resolved_argument_order_independence_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/name_resolved_argument_order_independence_class_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves a shorthand at each index after a leading named argument' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/name_resolved_argument_order_independence_class_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves a shorthand sandwiched between two named arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/name_resolved_argument_order_independence_class_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves a trailing named argument after leading shorthands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
