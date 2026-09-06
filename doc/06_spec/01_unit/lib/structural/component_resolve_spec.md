# Component Resolution (ComponentDescriptorV1 / resolve_component)

> End-to-end resolution: an SDN-subset catalog is parsed into versioned ComponentDescriptorV1 records and resolved via resolve_component to a concrete choice on the Phase B §5.3 decision table: presence=off is ABSENT, placement=dynamic never folds, placement=auto folds static only on a verified digest match and picks dynamic when the static copy is stale.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Component Resolution (ComponentDescriptorV1 / resolve_component)

End-to-end resolution: an SDN-subset catalog is parsed into versioned ComponentDescriptorV1 records and resolved via resolve_component to a concrete choice on the Phase B §5.3 decision table: presence=off is ABSENT, placement=dynamic never folds, placement=auto folds static only on a verified digest match and picks dynamic when the static copy is stale.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Plan | doc/03_plan/compiler/startup_performance/startup_perf_plan_2026-08-17.md (Phase B) |
| Source | `test/01_unit/lib/structural/component_resolve_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

End-to-end resolution: an SDN-subset catalog is parsed into versioned
ComponentDescriptorV1 records and resolved via resolve_component to a
concrete choice on the Phase B §5.3 decision table: presence=off is ABSENT,
placement=dynamic never folds, placement=auto folds static only on a
verified digest match and picks dynamic when the static copy is stale.

Specs read text verdicts from module-side accessors
(component_parse_status / resolve_component_verdict) because the current
seed erases class-typed values crossing into spec files; the accessors are
pure projections over resolve_component's Result.

## Examples

A three-component catalog resolves optimizer.basic to static on a matching
digest, to dynamic on a stale digest, loader.zstd (placement=dynamic) to
dynamic even with matching digests, and aspect.log_debug (presence=off) to
absent.

**Plan:** doc/03_plan/compiler/startup_performance/startup_perf_plan_2026-08-17.md (Phase B)

## Scenarios

### resolve_component end to end

#### parses the SDN catalog cleanly

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses the SDN catalog cleanly
   - Expected: component_parse_status(catalog_source()) equals `ok:3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses the SDN catalog cleanly")
expect(component_parse_status(catalog_source())).to_equal("ok:3")
```

</details>

#### folds placement=auto static on a matching digest

- folds placement=auto static on a matching digest
   - Expected: v equals `ok:static:command:presence=auto,placement=auto,activation=command`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("folds placement=auto static on a matching digest")
val v = resolve_component_verdict(component_catalog_v1_parse(catalog_source()), "optimizer.basic", "h123", "h123")
expect(v).to_equal("ok:static:command:presence=auto,placement=auto,activation=command")
```

</details>

#### picks dynamic when the static copy is stale (digest mismatch)

- picks dynamic when the static copy is stale (digest mismatch)
   - Expected: v equals `ok:dynamic:command:presence=auto,placement=auto,activation=command`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("picks dynamic when the static copy is stale (digest mismatch)")
val v = resolve_component_verdict(component_catalog_v1_parse(catalog_source()), "optimizer.basic", "h123", "h999")
expect(v).to_equal("ok:dynamic:command:presence=auto,placement=auto,activation=command")
```

</details>

#### never folds placement=dynamic even on matching digests

- never folds placement=dynamic even on matching digests
   - Expected: v equals `ok:dynamic:first_use:presence=on,placement=dynamic,activation=first_use`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never folds placement=dynamic even on matching digests")
val v = resolve_component_verdict(component_catalog_v1_parse(catalog_source()), "loader.zstd", "same", "same")
expect(v).to_equal("ok:dynamic:first_use:presence=on,placement=dynamic,activation=first_use")
```

</details>

#### resolves presence=off to absent

- resolves presence=off to absent
   - Expected: v equals `ok:absent:manual:presence=off,placement=auto,activation=manual`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves presence=off to absent")
val v = resolve_component_verdict(component_catalog_v1_parse(catalog_source()), "aspect.log_debug", "a", "a")
expect(v).to_equal("ok:absent:manual:presence=off,placement=auto,activation=manual")
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


## Related Documentation

- **Plan:** `doc/03_plan/compiler/startup_performance/startup_perf_plan_2026-08-17.md (Phase B)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `72dcc223daf8b9a5a40930e43c57373c764c0de211bfe7bae26918e8a6f52aae`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `72dcc223daf8b9a5a40930e43c57373c764c0de211bfe7bae26918e8a6f52aae`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `72dcc223daf8b9a5a40930e43c57373c764c0de211bfe7bae26918e8a6f52aae`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/structural/component_resolve_spec.spl
mirror: doc/06_spec/01_unit/lib/structural/component_resolve_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/structural/component_resolve_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/structural/component_resolve_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/structural/component_resolve_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses the SDN catalog cleanly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/structural/component_resolve_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'folds placement=auto static on a matching digest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/structural/component_resolve_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'picks dynamic when the static copy is stale (digest mismatch)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
