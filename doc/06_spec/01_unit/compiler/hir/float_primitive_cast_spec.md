# Float Primitive Cast Specification

> Tests covering float(x) lowers as an f64 primitive cast.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Float Primitive Cast Specification

## Scenarios

### float(x) lowers as an f64 primitive cast

#### lowers the format.spl shape with zero errors

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lowers the format.spl shape with zero errors
   - Expected: unresolved_float is false
   - Expected: hl.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers the format.spl shape with zero errors")
val src = "fn frac_digits(f: f64, i_part: i64) -> f64:\n" +
    "    var frac = f - float(i_part)\n" +
    "    frac\n"
val parsed = parse_full_frontend(src, "testdata/float_cast_format.spl", "float_cast_format", Logger(level: 0))
var hl = HirLowering.with_filename("testdata/float_cast_format.spl")
val hir = hl.lower_module(parsed)

var unresolved_float = false
for err in hl.errors:
    if err.message.contains("unresolved name: float"):
        unresolved_float = true
expect(unresolved_float).to_equal(false)
expect(hl.errors.len()).to_equal(0)
```

</details>

#### lowers float(x) the same way as the already-supported f64(x)

- lowers float(x) the same way as the already-supported f64(x)
   - Expected: unresolved_names equals `0`
   - Expected: hl.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers float(x) the same way as the already-supported f64(x)")
val src = "fn via_float(n: i64) -> f64:\n" +
    "    float(n)\n" +
    "\n" +
    "fn via_f64(n: i64) -> f64:\n" +
    "    f64(n)\n"
val parsed = parse_full_frontend(src, "testdata/float_cast_alias.spl", "float_cast_alias", Logger(level: 0))
var hl = HirLowering.with_filename("testdata/float_cast_alias.spl")
val hir = hl.lower_module(parsed)
# Neither spelling may produce an unresolved-name error: `f64(x)` was
# already a cast, `float(x)` must now be the same cast.
var unresolved_names = 0
for err in hl.errors:
    if err.message.contains("unresolved name:"):
        unresolved_names = unresolved_names + 1
expect(unresolved_names).to_equal(0)
expect(hl.errors.len()).to_equal(0)
```

</details>

#### control: an unrelated unknown callee still errors loudly

- control: an unrelated unknown callee still errors loudly
   - Expected: has_unresolved is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("control: an unrelated unknown callee still errors loudly")
val src = "fn f(n: i64) -> i64:\n" +
    "    definitely_not_a_builtin(n)\n"
val parsed = parse_full_frontend(src, "testdata/float_cast_control.spl", "float_cast_control", Logger(level: 0))
var hl = HirLowering.with_filename("testdata/float_cast_control.spl")
val hir = hl.lower_module(parsed)

var has_unresolved = false
for err in hl.errors:
    if err.message.contains("unresolved name: definitely_not_a_builtin"):
        has_unresolved = true
expect(has_unresolved).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/float_primitive_cast_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering float(x) lowers as an f64 primitive cast.
- float(x) lowers as an f64 primitive cast

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

- Canonical SPipe generation for source `cdde55560114abd3bf29340416b4ad3bbc02415d2313b14b9ea1bc8b4b4636ca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cdde55560114abd3bf29340416b4ad3bbc02415d2313b14b9ea1bc8b4b4636ca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cdde55560114abd3bf29340416b4ad3bbc02415d2313b14b9ea1bc8b4b4636ca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/hir/float_primitive_cast_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/float_primitive_cast_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/float_primitive_cast_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/float_primitive_cast_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/float_primitive_cast_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/float_primitive_cast_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers the format.spl shape with zero errors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/float_primitive_cast_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers float(x) the same way as the already-supported f64(x)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/float_primitive_cast_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'control: an unrelated unknown callee still errors loudly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
