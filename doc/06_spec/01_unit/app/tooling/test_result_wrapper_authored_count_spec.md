# Test Result Wrapper Authored Count Specification

> Tests covering interpreter result wrapper authored-count guard.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Result Wrapper Authored Count Specification

## Scenarios

### interpreter result wrapper authored-count guard

#### counts sibling examples and ignores documentation and comments

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- counts sibling examples and ignores documentation and comments
   - Expected: count_authored_examples(source) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("counts sibling examples and ignores documentation and comments")
val source = "\"\"\"\nit \"documented only\":\n\"\"\"\n# it \"commented\":\ndescribe \"first\":\n    it \"one\":\n        expect(1).to_equal(1)\ndescribe \"second\":\n    it(\"two\"):\n        expect(2).to_equal(2)\n"
expect(count_authored_examples(source)).to_equal(2)
```

</details>

#### counts the supported example aliases

- counts the supported example aliases
   - Expected: count_authored_examples(source) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("counts the supported example aliases")
val source = "test \"a\":\n    pass_dn\nexample \"b\":\n    pass_dn\nspecify \"c\":\n    pass_dn\nslow_it \"d\":\n    pass_dn\nskip_it \"e\":\n    pass_dn\npending \"f\"\n"
expect(count_authored_examples(source)).to_equal(6)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/test_result_wrapper_authored_count_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering interpreter result wrapper authored-count guard.
- interpreter result wrapper authored-count guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5f508d638a4c8d377f88859637485615e2200109fbf94232b1a98f7b3b6b9a3f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5f508d638a4c8d377f88859637485615e2200109fbf94232b1a98f7b3b6b9a3f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5f508d638a4c8d377f88859637485615e2200109fbf94232b1a98f7b3b6b9a3f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/app/tooling/test_result_wrapper_authored_count_spec.spl
mirror: doc/06_spec/01_unit/app/tooling/test_result_wrapper_authored_count_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/tooling/test_result_wrapper_authored_count_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/tooling/test_result_wrapper_authored_count_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/tooling/test_result_wrapper_authored_count_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/tooling/test_result_wrapper_authored_count_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'counts sibling examples and ignores documentation and comments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/tooling/test_result_wrapper_authored_count_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'counts the supported example aliases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
