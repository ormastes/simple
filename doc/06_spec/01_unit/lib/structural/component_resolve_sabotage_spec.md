# Component Resolution Fail-Closed (sabotage + positive control)

> Defect-class spec for resolve_component's fail-closed contract: an unknown component id, a malformed descriptor (bad axis value), a duplicate id, an unsupported schema version, and a missing impl digest on placement=auto each produce the explicit typed error — never a silent default. Every sabotage scenario carries a POSITIVE CONTROL: a valid sibling in the same scenario still resolves, so the implementation cannot pass by rejecting everything.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Component Resolution Fail-Closed (sabotage + positive control)

Defect-class spec for resolve_component's fail-closed contract: an unknown component id, a malformed descriptor (bad axis value), a duplicate id, an unsupported schema version, and a missing impl digest on placement=auto each produce the explicit typed error — never a silent default. Every sabotage scenario carries a POSITIVE CONTROL: a valid sibling in the same scenario still resolves, so the implementation cannot pass by rejecting everything.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Plan | doc/03_plan/compiler/startup_performance/startup_perf_plan_2026-08-17.md (Phase B sabotage requirement) |
| Source | `test/01_unit/lib/structural/component_resolve_sabotage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Defect-class spec for resolve_component's fail-closed contract: an unknown
component id, a malformed descriptor (bad axis value), a duplicate id, an
unsupported schema version, and a missing impl digest on placement=auto each
produce the explicit typed error — never a silent default. Every sabotage
scenario carries a POSITIVE CONTROL: a valid sibling in the same scenario
still resolves, so the implementation cannot pass by rejecting everything.

**Plan:** doc/03_plan/compiler/startup_performance/startup_perf_plan_2026-08-17.md (Phase B sabotage requirement)

## Scenarios

### resolve_component fails closed

#### rejects an unknown component id while the valid sibling resolves

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects an unknown component id while the valid sibling resolves
   - Expected: resolve_component_verdict(cat, "no.such.component", "h", "h") equals `err:unknown_component`
   - Expected: resolve_component_verdict(cat, "compiler.frontend", "h", "h") equals `ok:static:first_use:presence=auto,placement=static,activation=first_use`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unknown component id while the valid sibling resolves")
var cat: [ComponentDescriptorV1] = []
cat.push(component_v1_make(1, "compiler.frontend", "1", "auto", "static", "first_use"))
expect(resolve_component_verdict(cat, "no.such.component", "h", "h")).to_equal("err:unknown_component")
# POSITIVE CONTROL: same catalog, valid id, still resolves.
expect(resolve_component_verdict(cat, "compiler.frontend", "h", "h")).to_equal("ok:static:first_use:presence=auto,placement=static,activation=first_use")
```

</details>

#### rejects a malformed descriptor (unknown axis value) explicitly

- rejects a malformed descriptor (unknown axis value) explicitly
   - Expected: resolve_component_verdict(cat, "optimizer.broken", "h", "h") equals `err:malformed_descriptor`
   - Expected: resolve_component_verdict(ok_cat, "optimizer.basic", "h", "h") equals `ok:static:command:presence=auto,placement=static,activation=command`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a malformed descriptor (unknown axis value) explicitly")
var cat: [ComponentDescriptorV1] = []
cat.push(component_v1_make(1, "optimizer.broken", "1", "auto", "sideways", "first_use"))
expect(resolve_component_verdict(cat, "optimizer.broken", "h", "h")).to_equal("err:malformed_descriptor")
# POSITIVE CONTROL: a valid sibling catalog resolves fine.
var ok_cat: [ComponentDescriptorV1] = []
ok_cat.push(component_v1_make(1, "optimizer.basic", "1", "auto", "static", "command"))
expect(resolve_component_verdict(ok_cat, "optimizer.basic", "h", "h")).to_equal("ok:static:command:presence=auto,placement=static,activation=command")
```

</details>

#### rejects duplicate ids as malformed, never picks one silently

- rejects duplicate ids as malformed, never picks one silently
   - Expected: resolve_component_verdict(cat, "dup.id", "h", "h") equals `err:malformed_descriptor`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects duplicate ids as malformed, never picks one silently")
var cat: [ComponentDescriptorV1] = []
cat.push(component_v1_make(1, "dup.id", "1", "auto", "static", "manual"))
cat.push(component_v1_make(1, "dup.id", "2", "auto", "static", "manual"))
expect(resolve_component_verdict(cat, "dup.id", "h", "h")).to_equal("err:malformed_descriptor")
```

</details>

#### rejects an unsupported schema version explicitly

- rejects an unsupported schema version explicitly
   - Expected: resolve_component_verdict(cat, "future.component", "h", "h") equals `err:unsupported_schema_version`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unsupported schema version explicitly")
var cat: [ComponentDescriptorV1] = []
cat.push(component_v1_make(2, "future.component", "1", "auto", "static", "manual"))
expect(resolve_component_verdict(cat, "future.component", "h", "h")).to_equal("err:unsupported_schema_version")
```

</details>

#### rejects a missing impl digest on placement=auto instead of guessing

- rejects a missing impl digest on placement=auto instead of guessing
   - Expected: resolve_component_verdict(cat, "optimizer.basic", "", "h") equals `err:missing_impl_digest`
   - Expected: resolve_component_verdict(cat, "optimizer.basic", "h", "h") equals `ok:static:command:presence=auto,placement=auto,activation=command`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a missing impl digest on placement=auto instead of guessing")
var cat: [ComponentDescriptorV1] = []
cat.push(component_v1_make(1, "optimizer.basic", "1", "auto", "auto", "command"))
expect(resolve_component_verdict(cat, "optimizer.basic", "", "h")).to_equal("err:missing_impl_digest")
# POSITIVE CONTROL: with real digests the same descriptor resolves.
expect(resolve_component_verdict(cat, "optimizer.basic", "h", "h")).to_equal("ok:static:command:presence=auto,placement=auto,activation=command")
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

- **Plan:** `doc/03_plan/compiler/startup_performance/startup_perf_plan_2026-08-17.md (Phase B sabotage requirement)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7ff16297a2a5e8877cbf744288b913e479b28527ca960673826937d999f73b9a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7ff16297a2a5e8877cbf744288b913e479b28527ca960673826937d999f73b9a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7ff16297a2a5e8877cbf744288b913e479b28527ca960673826937d999f73b9a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/structural/component_resolve_sabotage_spec.spl
mirror: doc/06_spec/01_unit/lib/structural/component_resolve_sabotage_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/structural/component_resolve_sabotage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/structural/component_resolve_sabotage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/structural/component_resolve_sabotage_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an unknown component id while the valid sibling resolves' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/structural/component_resolve_sabotage_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a malformed descriptor (unknown axis value) explicitly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/structural/component_resolve_sabotage_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects duplicate ids as malformed, never picks one silently' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
