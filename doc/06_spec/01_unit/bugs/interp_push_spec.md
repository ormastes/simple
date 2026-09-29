# Interp Push Specification

> Tests covering Module-level .push() bug.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interp Push Specification

## Scenarios

### Module-level .push() bug

#### demonstrates workaround with concatenation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- demonstrates workaround with concatenation
   - Expected: _test_concat_workaround() equals `3`
   - Expected: _len(items) equals `3`
   - Expected: _get(items, 0) equals `alpha`
   - Expected: _get(items, 1) equals `beta`
   - Expected: _get(items, 2) equals `gamma`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("demonstrates workaround with concatenation")
expect(_test_concat_workaround()).to_equal(3)
val items = _test_concat_items()
expect(_len(items)).to_equal(3)
expect(_get(items, 0)).to_equal("alpha")
expect(_get(items, 1)).to_equal("beta")
expect(_get(items, 2)).to_equal("gamma")
```

</details>

#### push works inside local scope

- push works inside local scope
   - Expected: _test_push_local() equals `2`
   - Expected: _test_push_local_first() equals `one`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("push works inside local scope")
expect(_test_push_local()).to_equal(2)
expect(_test_push_local_first()).to_equal("one")
```

</details>

#### workaround preserves existing items

- workaround preserves existing items
   - Expected: _test_preserve_items() equals `second`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("workaround preserves existing items")
expect(_test_preserve_items()).to_equal("second")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Bug Regression |
| Status | Active |
| Source | `test/01_unit/bugs/interp_push_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Module-level .push() bug.
- Module-level .push() bug

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

- `REQ-SSPEC-BUGS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4ad2091eb4f68564633627b42012858f7cfd1b1a3bd44163797c71d12ddea604`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4ad2091eb4f68564633627b42012858f7cfd1b1a3bd44163797c71d12ddea604`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4ad2091eb4f68564633627b42012858f7cfd1b1a3bd44163797c71d12ddea604`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/bugs/interp_push_spec.spl
mirror: doc/06_spec/01_unit/bugs/interp_push_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/bugs/interp_push_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/bugs/interp_push_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/bugs/interp_push_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/bugs/interp_push_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'demonstrates workaround with concatenation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/bugs/interp_push_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'push works inside local scope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/bugs/interp_push_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'workaround preserves existing items' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
