# Test Db Compiled Specification

> Tests covering compiled db local harness.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Db Compiled Specification

## Scenarios

### compiled db local harness

#### roundtrips stable content without production imports

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- roundtrips stable content without production imports
   - Expected: parsed.interner.len() equals `original.interner.len()`
   - Expected: parsed.files.len() equals `1`
   - Expected: parsed.suites.len() equals `1`
   - Expected: parsed.tests.len() equals `1`
   - Expected: parsed.tests[0].qualified_by equals ``
   - Expected: text_list_equals(parsed.interner.strings, original.interner.strings) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrips stable content without production imports")
val original = compiled_db_fixture()
val encoded = serialize_compiled_db(original)
val parsed = parse_compiled_db(encoded)

expect(parsed.interner.len()).to_equal(original.interner.len())
expect(parsed.files.len()).to_equal(1)
expect(parsed.suites.len()).to_equal(1)
expect(parsed.tests.len()).to_equal(1)
expect(parsed.tests[0].qualified_by).to_equal("")
expect(text_list_equals(parsed.interner.strings, original.interner.strings)).to_equal(true)
```

</details>

#### detects out-of-bounds references

- detects out-of-bounds references
   - Expected: issues.len() > 0 is true
   - Expected: issues[0].severity equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects out-of-bounds references")
var db = compiled_db_fixture()
db.tests.push(CompiledTestRecord(
    suite_id: 9,
    name_str: 99,
    category_str: 99,
    status_str: 99,
    qualified_by: ""
))

val issues = validate_interner_bounds(db)
expect(issues.len() > 0).to_equal(true)
expect(issues[0].severity).to_equal("error")
```

</details>

#### counts unqualified ignored tests

- counts unqualified ignored tests
   - Expected: count_unqualified_ignores(db, ignored) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts unqualified ignored tests")
var db = compiled_db_fixture()
val ignored = db.interner.intern("ignored")
db.tests.push(CompiledTestRecord(
    suite_id: 0,
    name_str: db.interner.intern("known_failure"),
    category_str: db.interner.intern("unit"),
    status_str: ignored,
    qualified_by: ""
))
db.tests.push(CompiledTestRecord(
    suite_id: 0,
    name_str: db.interner.intern("qualified_failure"),
    category_str: db.interner.intern("unit"),
    status_str: ignored,
    qualified_by: "issue-123"
))

expect(count_unqualified_ignores(db, ignored)).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/test_db_compiled_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering compiled db local harness.
- compiled db local harness

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

- Canonical SPipe generation for source `d3f85553e51d26f41993ba6bac896bb6a5927a5fe87fcfdcf765f1f2e201510d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d3f85553e51d26f41993ba6bac896bb6a5927a5fe87fcfdcf765f1f2e201510d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d3f85553e51d26f41993ba6bac896bb6a5927a5fe87fcfdcf765f1f2e201510d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/tooling/test_db_compiled_spec.spl
mirror: doc/06_spec/unit/app/tooling/test_db_compiled_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/test_db_compiled_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/test_db_compiled_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/test_db_compiled_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/tooling/test_db_compiled_spec.spl:227:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'roundtrips stable content without production imports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/test_db_compiled_spec.spl:241:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects out-of-bounds references' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/test_db_compiled_spec.spl:257:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'counts unqualified ignored tests' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
