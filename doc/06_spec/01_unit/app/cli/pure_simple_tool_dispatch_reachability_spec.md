# Pure Simple Tool Dispatch Reachability Specification

> Tests covering pure-Simple-only CLI tools are structurally reachable.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure Simple Tool Dispatch Reachability Specification

## Scenarios

### pure-Simple-only CLI tools are structurally reachable

#### the three driver tables were actually parsed (non-vacuity)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- the three driver tables were actually parsed (non-vacuity)
   - Expected: source.len() > 1000 is true
   - Expected: pure_simple_block(source).len() > 100 is true
   - Expected: dispatch_block(source).len() > 100 is true
   - Expected: pairs.len() > 50 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the three driver tables were actually parsed (non-vacuity)")
val source = driver_source()
expect(source.len() > 1000).to_equal(true)
expect(pure_simple_block(source).len() > 100).to_equal(true)
expect(dispatch_block(source).len() > 100).to_equal(true)
val pairs = collect_name_app_pairs(source)
# 73 app_path entries at the time of writing; a parse regression that
# silently collected nothing must fail here, not pass vacuously.
expect(pairs.len() > 50).to_equal(true)
```

</details>

#### every pure-Simple-only command has an app that exists and is dispatchable

- every pure-Simple-only command has an app that exists and is dispatchable
   - Expected: checked > 10 is true
   - Expected: offenders equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("every pure-Simple-only command has an app that exists and is dispatchable")
val source = driver_source()
val ps = pure_simple_block(source)
val allow_list = dispatch_block(source)
val pairs = collect_name_app_pairs(source)
var checked = 0
var offenders = ""
for pair in pairs:
    val name = pair.0
    val app = pair.1
    if app == "":
        continue
    if not ps.contains("\"{name}\""):
        continue
    if name == BASELINED_MISSING_APP:
        continue
    checked = checked + 1
    if not rt_file_exists(app):
        offenders = "{offenders} {name}->{app}:NO_FILE"
    if not allow_list.contains("app_relative_path != \"{app}\""):
        offenders = "{offenders} {name}->{app}:NOT_DISPATCHABLE"
# A scan that examined nothing is a failure, not a pass.
expect(checked > 10).to_equal(true)
expect(offenders).to_equal("")
```

</details>

#### the baselined exception is still genuinely missing (stale-baseline guard)

- the baselined exception is still genuinely missing (stale-baseline guard)
   - Expected: rt_file_exists("src/app/depgraph/main.spl") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the baselined exception is still genuinely missing (stale-baseline guard)")
# If depgraph's app ever lands, delete BASELINED_MISSING_APP and the
# `continue` above instead of leaving a dead exemption behind.
expect(rt_file_exists("src/app/depgraph/main.spl")).to_equal(false)
```

</details>

#### a dispatch miss on a pure-Simple tool fails closed rather than silently

- a dispatch miss on a pure-Simple tool fails closed rather than silently


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a dispatch miss on a pure-Simple tool fails closed rather than silently")
val source = driver_source()
expect(source).to_contain("refusing Rust fallback")
expect(source).to_contain("let pure_simple_tool = command_is_pure_simple_tool(entry.name);")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/pure_simple_tool_dispatch_reachability_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering pure-Simple-only CLI tools are structurally reachable.
- pure-Simple-only CLI tools are structurally reachable

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `ef1dd05c8bd80b9130d66feb781f5bbef8d88f1466267a1e5818825b205d4bd3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ef1dd05c8bd80b9130d66feb781f5bbef8d88f1466267a1e5818825b205d4bd3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ef1dd05c8bd80b9130d66feb781f5bbef8d88f1466267a1e5818825b205d4bd3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/cli/pure_simple_tool_dispatch_reachability_spec.spl
mirror: doc/06_spec/01_unit/app/cli/pure_simple_tool_dispatch_reachability_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/cli/pure_simple_tool_dispatch_reachability_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/cli/pure_simple_tool_dispatch_reachability_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/cli/pure_simple_tool_dispatch_reachability_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the three driver tables were actually parsed (non-vacuity)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/pure_simple_tool_dispatch_reachability_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'every pure-Simple-only command has an app that exists and is dispatchable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/pure_simple_tool_dispatch_reachability_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the baselined exception is still genuinely missing (stale-baseline guard)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
