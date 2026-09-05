# Facade Resolution Specification

> Tests covering nogc_sync_immut facade resolution.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Facade Resolution Specification

## Scenarios

### nogc_sync_immut facade resolution

#### resolves persistent helpers through the no-GC async immutable backing family

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves persistent helpers through the no-GC async immutable backing family
   - Expected: pfold([1, 2, 3], 0, \acc, x: acc + x) equals `6`
   - Expected: nogc_async_immut_version() equals `0.1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves persistent helpers through the no-GC async immutable backing family")
expect(pfold([1, 2, 3], 0, \acc, x: acc + x)).to_equal(6)
expect(nogc_async_immut_version()).to_equal("0.1.0")
```

</details>

#### preserves root coordination type behavior through the no-GC sync facade

- preserves root coordination type behavior through the no-GC sync facade
   - Expected: atom.deref() equals `22`
   - Expected: snapshot.current() equals `head`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves root coordination type behavior through the no-GC sync facade")
var atom = Atom.new(21)
atom.reset(22)
expect(atom.deref()).to_equal(22)

var snapshot = VersionedSnapshot.new("base")
snapshot.update("head")
expect(snapshot.current()).to_equal("head")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_immut/facade_resolution_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_sync_immut facade resolution.
- nogc_sync_immut facade resolution

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `adbff10ddb770ae6166889227022277858318666830d071a29240853b6489ccb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `adbff10ddb770ae6166889227022277858318666830d071a29240853b6489ccb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `adbff10ddb770ae6166889227022277858318666830d071a29240853b6489ccb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/nogc_sync_immut/facade_resolution_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_immut/facade_resolution_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_immut/facade_resolution_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_immut/facade_resolution_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_immut/facade_resolution_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_immut/facade_resolution_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves persistent helpers through the no-GC async immutable backing family' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_immut/facade_resolution_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves root coordination type behavior through the no-GC sync facade' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
