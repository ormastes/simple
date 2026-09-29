# Test Db Core Construction Specification

> Tests covering RunnerTestDbCore is constructible, the renamed interner class is the only one.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Db Core Construction Specification

## Scenarios

### RunnerTestDbCore is constructible

#### empty() builds a database with no records

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- empty() builds a database with no records
   - Expected: db.tests.len() equals `0`
   - Expected: db.files.len() equals `0`
   - Expected: db.suites.len() equals `0`
   - Expected: db.dirty is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty() builds a database with no records")
var db = RunnerTestDbCore.empty()
expect(db.tests.len()).to_equal(0)
expect(db.files.len()).to_equal(0)
expect(db.suites.len()).to_equal(0)
expect(db.dirty).to_equal(false)
```

</details>

#### carries a real TestDbStringInterner, not an empty dict

- carries a real TestDbStringInterner, not an empty dict
   - Expected: db.interner.len() equals `0`
   - Expected: db.interner does not contain `nope`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("carries a real TestDbStringInterner, not an empty dict")
var db = RunnerTestDbCore.empty()
expect(db.interner.len()).to_equal(0)
expect(db.interner.contains("nope")).to_equal(false)
```

</details>

#### interns through the field the broken import used to blank out

- interns through the field the broken import used to blank out
   - Expected: id equals `0`
   - Expected: db.interner.get(id) equals `test/01_unit/example_spec.spl`
   - Expected: db.interner.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("interns through the field the broken import used to blank out")
var db = RunnerTestDbCore.empty()
val id = db.interner.intern("test/01_unit/example_spec.spl")
expect(id).to_equal(0)
expect(db.interner.get(id)).to_equal("test/01_unit/example_spec.spl")
expect(db.interner.len()).to_equal(1)
```

</details>

#### find_test_index reports absence on an empty database

- find_test_index reports absence on an empty database
   - Expected: db.find_test_index(0, 0) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("find_test_index reports absence on an empty database")
var db = RunnerTestDbCore.empty()
expect(db.find_test_index(0, 0)).to_equal(-1)
```

</details>

### the renamed interner class is the only one

#### TestDbStringInterner.empty() is the constructor the module provides

- TestDbStringInterner.empty() is the constructor the module provides
   - Expected: interner.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("TestDbStringInterner.empty() is the constructor the module provides")
var interner = TestDbStringInterner.empty()
expect(interner.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/test_runner/test_db_core_construction_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RunnerTestDbCore is constructible, the renamed interner class is the only one.
- RunnerTestDbCore is constructible
- the renamed interner class is the only one

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4bc1cc758093a5e9087b87135bb8a78da37fafdf61b5d96a2d47fc13c04d7047`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4bc1cc758093a5e9087b87135bb8a78da37fafdf61b5d96a2d47fc13c04d7047`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4bc1cc758093a5e9087b87135bb8a78da37fafdf61b5d96a2d47fc13c04d7047`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/test_runner/test_db_core_construction_spec.spl
mirror: doc/06_spec/01_unit/lib/test_runner/test_db_core_construction_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/test_runner/test_db_core_construction_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/test_runner/test_db_core_construction_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/test_runner/test_db_core_construction_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/test_runner/test_db_core_construction_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty() builds a database with no records' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/test_runner/test_db_core_construction_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries a real TestDbStringInterner, not an empty dict' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/test_runner/test_db_core_construction_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'interns through the field the broken import used to blank out' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
