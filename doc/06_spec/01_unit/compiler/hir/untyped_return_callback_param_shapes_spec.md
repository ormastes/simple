# Untyped-return-value: callback-parameter and non-scalar-param-ident shapes

> Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Untyped-return-value: callback-parameter and non-scalar-param-ident shapes

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/untyped_return_callback_param_shapes_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## Operator workflow

1. Run `bin/simple test test/01_unit/compiler/hir/untyped_return_callback_param_shapes_spec.spl`.
2. Every scenario must pass; a failure is a regression in the behavior under test.

## Compatibility and limitations

Covers the behavior asserted here; platform-specific behavior is out of scope.

## Scenarios

### untyped return: callback param and non-scalar param ident

#### callback param `fn(Any) -> bool`: untyped errors, -> Any? is clean

- Verify: callback param `fn(Any) -> bool`: untyped errors, -> Any? is clean
   - Expected: error_count(head + ":\n" + body, "cb_bad") equals `1`
   - Expected: error_count(head + " -> Any?:\n" + body, "cb_ok") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: callback param `fn(Any) -> bool`: untyped errors, -> Any? is clean")
# @req: REQ-SSPEC-LOCAL-001
val body = "    var i = 0\n" +
    "    while i < arr.len():\n" +
    "        if predicate(arr[i]):\n            return arr[i]\n" +
    "        i = i + 1\n    nil\n"
val head = "fn array_find(arr: [Any], predicate: fn(Any) -> bool)"
expect(error_count(head + ":\n" + body, "cb_bad")).to_equal(1)
expect(error_count(head + " -> Any?:\n" + body, "cb_ok")).to_equal(0)
```

</details>

#### callback param + `return i` on a local: untyped errors, -> i64 is clean

- Verify: callback param + `return i` on a local: untyped errors, -> i64 is clean
   - Expected: error_count(head + ":\n" + body, "pos_bad") equals `1`
   - Expected: error_count(head + " -> i64:\n" + body, "pos_ok") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: callback param + `return i` on a local: untyped errors, -> i64 is clean")
val body = "    var i = 0\n" +
    "    while i < arr.len():\n" +
    "        if predicate(arr[i]):\n            return i\n" +
    "        i = i + 1\n    -1\n"
val head = "fn array_position(arr: [Any], predicate: fn(Any) -> bool)"
expect(error_count(head + ":\n" + body, "pos_bad")).to_equal(1)
expect(error_count(head + " -> i64:\n" + body, "pos_ok")).to_equal(0)
```

</details>

#### non-scalar param ident `return arr` where arr: [Any]: untyped errors, -> [Any] is clean

- Verify: non-scalar param ident `return arr` where arr: [Any]: untyped errors, -> [Any] is clean
   - Expected: error_count(head + ":\n" + body, "inter_bad") equals `1`
   - Expected: error_count(head + " -> [Any]:\n" + body, "inter_ok") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: non-scalar param ident `return arr` where arr: [Any]: untyped errors, -> [Any] is clean")
# @req: REQ-SSPEC-LOCAL-001
val body = "    if arr.len() <= 1:\n        return arr\n" +
    "    var result = [arr[0]]\n    result\n"
val head = "fn array_intersperse(arr: [Any], separator: Any)"
expect(error_count(head + ":\n" + body, "inter_bad")).to_equal(1)
expect(error_count(head + " -> [Any]:\n" + body, "inter_ok")).to_equal(0)
```

</details>

#### scalar param ident IS resolved: `return x` where x: i64 never errors

- Verify: scalar param ident IS resolved: `return x` where x: i64 never errors
   - Expected: error_count(src, "scalar_ok") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: scalar param ident IS resolved: `return x` where x: i64 never errors")
val src = "fn passthrough(x: i64, predicate: fn(i64) -> bool):\n" +
    "    if predicate(x):\n        return x\n    0\n"
expect(error_count(src, "scalar_ok")).to_equal(0)
```

</details>

#### an untyped parameter suppresses the diagnostic entirely

- Verify: an untyped parameter suppresses the diagnostic entirely
   - Expected: error_count(src, "untyped_param") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: an untyped parameter suppresses the diagnostic entirely")
val src = "fn option_ce_filter(value, predicate: fn() -> bool):\n" +
    "    if value == nil:\n        return nil\n" +
    "    if predicate(value):\n        return value\n    nil\n"
expect(error_count(src, "untyped_param")).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b932737684c49358f3b1a7aaf67f7d487fa1d451eef9fd1e994dfaf5ac9e991b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b932737684c49358f3b1a7aaf67f7d487fa1d451eef9fd1e994dfaf5ac9e991b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b932737684c49358f3b1a7aaf67f7d487fa1d451eef9fd1e994dfaf5ac9e991b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/hir/untyped_return_callback_param_shapes_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/untyped_return_callback_param_shapes_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/untyped_return_callback_param_shapes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/untyped_return_callback_param_shapes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/untyped_return_callback_param_shapes_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/untyped_return_callback_param_shapes_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'callback param `fn(Any) -> bool`: untyped errors, -> Any? is clean' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/untyped_return_callback_param_shapes_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'callback param + `return i` on a local: untyped errors, -> i64 is clean' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/untyped_return_callback_param_shapes_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'non-scalar param ident `return arr` where arr: [Any]: untyped errors, -> [Any] is clean' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

<!-- doc06-layout-migration: Historical generated/manual evidence retained; authoritative executable source remains at test/01_unit/compiler/hir/untyped_return_callback_param_shapes_spec.spl. -->
