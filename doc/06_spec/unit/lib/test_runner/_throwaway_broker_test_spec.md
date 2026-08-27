# _throwaway_broker_test_spec

> Purpose: Import-check probe that also exercises the imported module behaviorally

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# _throwaway_broker_test_spec

Purpose: Import-check probe that also exercises the imported module behaviorally

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/test_runner/_throwaway_broker_test_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Import-check probe that also exercises the imported module behaviorally
so a broken export fails here, not silently at load time.
Audience: test-runner engineers who own the imported module.

## Scenarios

### throwaway broker import check

#### loads broker module

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- loads broker module
   - Expected: broker.max_sessions equals `2`
   - Expected: broker.sessions.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("loads broker module")
# evidence(protocol_json): broker construction invariants below are the complete typed oracle
val broker = qemu_broker_new(2)
expect(broker.max_sessions).to_equal(2)
expect(broker.sessions.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `d643885ac76a624cecf5e6a46d75eb97734e0a1159cdc22dedf31146a902471f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d643885ac76a624cecf5e6a46d75eb97734e0a1159cdc22dedf31146a902471f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d643885ac76a624cecf5e6a46d75eb97734e0a1159cdc22dedf31146a902471f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **93/100**; effective score: **93/100**; blockers: **0**.

SSpec documentization score: 93/100
source: test/unit/lib/test_runner/_throwaway_broker_test_spec.spl
mirror: doc/06_spec/unit/lib/test_runner/_throwaway_broker_test_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/test_runner/_throwaway_broker_test_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/test_runner/_throwaway_broker_test_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/test_runner/_throwaway_broker_test_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
<!-- sspec-maintain:scorecard:end -->
