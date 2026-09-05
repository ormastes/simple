# Untyped-return-value shapes: fixed files lower without the diagnostic

> Reproduce for bootstrap run9 stage1 fatal (2026-08-22):

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Untyped-return-value shapes: fixed files lower without the diagnostic

Reproduce for bootstrap run9 stage1 fatal (2026-08-22):

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/untyped_return_value_shapes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Reproduce for bootstrap run9 stage1 fatal (2026-08-22):
`HIR lowering error in src/compiler/driver/driver_build/incremental.spl:
untyped function returns a value: function 'get_cached_mir_functions' ...`.
Same defect class as 5c285c2436f (text_advanced.spl). The three examples
below are the representative shapes that were fixed tree-wide:
  1. `return nil` + trailing `Some(dict)`        (incremental.spl)
  2. `return self.field` method on a struct      (vhdl/domain files)
  3. `return Err(...)`/`Ok(...)` static ctor     (backend_api.spl)
Each is asserted twice: the pre-fix (untyped) shape MUST produce the
diagnostic, the fixed (`-> T`) shape MUST lower clean. Tree-wide coverage is
`sh scripts/check/check-untyped-return-value.shs`.

## Scenarios

### untyped function returns a value: fixed shapes lower clean

#### return nil + trailing Some(dict): untyped errors, -> Dict<text, text>? is clean

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- return nil + trailing Some(dict): untyped errors, -> Dict<text, text>? is clean
   - Expected: error_count("fn get_cached(source: text):\n" + body, "shape1_bad") equals `1`
   - Expected: error_count("fn get_cached(source: text) -> Dict<text, text>?:\n" + body, "shape1_ok") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("return nil + trailing Some(dict): untyped errors, -> Dict<text, text>? is clean")
val body = "    if source == \"\":\n" +
    "        return nil\n" +
    "    var result: {text: text} = {}\n" +
    "    result[\"k\"] = source\n" +
    "    Some(result)\n"
expect(error_count("fn get_cached(source: text):\n" + body, "shape1_bad")).to_equal(1)
expect(error_count("fn get_cached(source: text) -> Dict<text, text>?:\n" + body, "shape1_ok")).to_equal(0)
```

</details>

#### method returning self.field: untyped errors, -> i32 is clean

- method returning self.field: untyped errors, -> i32 is clean
   - Expected: error_count(head + "    me max_unsigned():\n" + body, "shape2_bad") equals `1`
   - Expected: error_count(head + "    me max_unsigned() -> i32:\n" + body, "shape2_ok") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("method returning self.field: untyped errors, -> i32 is clean")
val head = "struct W:\n    width: i32\n"
val body = "        if self.width > 0:\n            return self.width\n        return 0\n"
expect(error_count(head + "    me max_unsigned():\n" + body, "shape2_bad")).to_equal(1)
expect(error_count(head + "    me max_unsigned() -> i32:\n" + body, "shape2_ok")).to_equal(0)
```

</details>

#### Err/Ok static constructor: untyped errors, -> Result<T, text> is clean

- Err/Ok static constructor: untyped errors, -> Result<T, text> is clean
   - Expected: error_count(head + "    static fn create(kind: i64):\n" + body, "shape3_bad") > 0 is true
   - Expected: error_count(head + "    static fn create(kind: i64) -> Result<B, text>:\n" + body, "shape3_ok") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Err/Ok static constructor: untyped errors, -> Result<T, text> is clean")
val head = "struct B:\n    kind: i64\n"
val body = "        if kind < 0:\n            return Err(\"bad kind\")\n        Ok(B(kind: kind))\n"
expect(error_count(head + "    static fn create(kind: i64):\n" + body, "shape3_bad") > 0).to_equal(true)
expect(error_count(head + "    static fn create(kind: i64) -> Result<B, text>:\n" + body, "shape3_ok")).to_equal(0)
```

</details>

#### return nil + return arr[mid] + trailing arithmetic (array_advanced.spl): untyped errors, -> Any? is clean

- return nil + return arr[mid] + trailing arithmetic (array_advanced.spl): untyped errors, -> Any? is clean
   - Expected: error_count("fn array_median(arr: [Any]):\n" + body, "shape4_bad") equals `1`
   - Expected: error_count("fn array_median(arr: [Any]) -> Any?:\n" + body, "shape4_ok") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("return nil + return arr[mid] + trailing arithmetic (array_advanced.spl): untyped errors, -> Any? is clean")
# src/lib/*/array_advanced.spl:array_median sat in the ratchet baseline
# while being in the stage1 lowering set (run9, 2026-08-22).
val body = "    if arr.len() == 0:\n        return nil\n" +
    "    val mid = arr.len() / 2\n" +
    "    if arr.len() % 2 == 1:\n        return arr[mid]\n" +
    "    (arr[mid - 1] + arr[mid]) / 2\n"
expect(error_count("fn array_median(arr: [Any]):\n" + body, "shape4_bad")).to_equal(1)
expect(error_count("fn array_median(arr: [Any]) -> Any?:\n" + body, "shape4_ok")).to_equal(0)
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c0ab92d63d70e15f2a76aa46465f0d66756bc6defe7bc04c059f654f92d160f8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c0ab92d63d70e15f2a76aa46465f0d66756bc6defe7bc04c059f654f92d160f8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c0ab92d63d70e15f2a76aa46465f0d66756bc6defe7bc04c059f654f92d160f8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/hir/untyped_return_value_shapes_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/untyped_return_value_shapes_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/untyped_return_value_shapes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/untyped_return_value_shapes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/untyped_return_value_shapes_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/untyped_return_value_shapes_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'return nil + trailing Some(dict): untyped errors, -> Dict<text, text>? is clean' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/untyped_return_value_shapes_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'method returning self.field: untyped errors, -> i32 is clean' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/untyped_return_value_shapes_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Err/Ok static constructor: untyped errors, -> Result<T, text> is clean' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
