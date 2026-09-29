# bug_gen_does_not_clobber_records_spec

> Purpose: This spec proves `bug-gen` never rewrites, truncates or deletes a bug

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# bug_gen_does_not_clobber_records_spec

Purpose: This spec proves `bug-gen` never rewrites, truncates or deletes a bug

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/bug_gen/bug_gen_does_not_clobber_records_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves `bug-gen` never rewrites, truncates or deletes a bug
record file under `doc/08_tracking/bug/`, and refuses to regenerate its index
from a partially-parsed database instead of silently dropping rows.
Audience: Maintainers of the tracking CLI.

Bug: doc/08_tracking/bug/bug_gen_truncates_unrelated_records_2026-08-21.md

## Scenarios

### bug-gen never clobbers bug record files

#### leaves unrelated records byte-identical on a clean run

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- regenerate the index over a directory holding two hand-written records
   - Expected: code equals `0`
- both record files are still present and byte-identical
   - Expected: _record_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-BUGGENSAFETY-001
step("regenerate the index over a directory holding two hand-written records")
_setup_fixture("")
val (_out, _err, code) = _run_bug_gen([])
expect(code).to_equal(0)
step("both record files are still present and byte-identical")
expect(_record_count()).to_equal("2")
val (same, _e2, _c2) = _records_unchanged()
expect(same).to_contain("IDENTICAL")
```

</details>

#### refuses to regenerate from a partially-parsed database

- a bugs row with too few fields must fail closed, not be dropped
   - Expected: code equals `1`
- nothing was written and every record is untouched
   - Expected: _record_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-BUGGENSAFETY-001
step("a bugs row with too few fields must fail closed, not be dropped")
_setup_fixture("printf '    BUG-2, P2, Open, \\\"truncated row\\\"\\n'; ")
val (out, _err, code) = _run_bug_gen([])
expect(code).to_equal(1)
expect(out).to_contain("partial parse")
step("nothing was written and every record is untouched")
expect(_record_count()).to_equal("2")
val (same, _e2, _c2) = _records_unchanged()
expect(same).to_contain("IDENTICAL")
```

</details>

#### writes only its own index file when given -o

- -o names a directory; only recent_bugs.md may appear in it
   - Expected: code equals `0`
   - Expected: _record_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-BUGGENSAFETY-001
step("-o names a directory; only recent_bugs.md may appear in it")
_setup_fixture("")
val (_out, _err, code) = _run_bug_gen(["-o", "doc/08_tracking/bug"])
expect(code).to_equal(0)
expect(_record_count()).to_equal("2")
val (same, _e2, _c2) = _records_unchanged()
expect(same).to_contain("IDENTICAL")
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

- `REQ-SSPEC-UNIT`
- `REQ-BUGGENSAFETY-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `db917e72cf61d0d548f3c44b9f9eb5aa48d9840b177495b6115056f3cc2c80bc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db917e72cf61d0d548f3c44b9f9eb5aa48d9840b177495b6115056f3cc2c80bc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db917e72cf61d0d548f3c44b9f9eb5aa48d9840b177495b6115056f3cc2c80bc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/app/bug_gen/bug_gen_does_not_clobber_records_spec.spl
mirror: doc/06_spec/unit/app/bug_gen/bug_gen_does_not_clobber_records_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/unit/app/bug_gen/bug_gen_does_not_clobber_records_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/bug_gen/bug_gen_does_not_clobber_records_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/bug_gen/bug_gen_does_not_clobber_records_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/bug_gen/bug_gen_does_not_clobber_records_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/app/bug_gen/bug_gen_does_not_clobber_records_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves unrelated records byte-identical on a clean run' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/bug_gen/bug_gen_does_not_clobber_records_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses to regenerate from a partially-parsed database' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/bug_gen/bug_gen_does_not_clobber_records_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes only its own index file when given -o' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
