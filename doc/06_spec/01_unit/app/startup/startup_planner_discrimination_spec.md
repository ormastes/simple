# Startup Planner Discrimination Specification (defect-class, WP-15s)

> Positive-control spec: the planner must DISCRIMINATE — different requests against the same catalog yield different plans, so a stub that returns one fixed plan cannot pass. Also proves the no-host-I/O constraint by static scan: the planner module's source imports only pure descriptor helpers and contains no file/env/process/network API tokens.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Startup Planner Discrimination Specification (defect-class, WP-15s)

Positive-control spec: the planner must DISCRIMINATE — different requests against the same catalog yield different plans, so a stub that returns one fixed plan cannot pass. Also proves the no-host-I/O constraint by static scan: the planner module's source imports only pure descriptor helpers and contains no file/env/process/network API tokens.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/startup_perf_parallel_plan_2026-08-17.md (WP-15s) |
| Source | `test/01_unit/app/startup/startup_planner_discrimination_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Positive-control spec: the planner must DISCRIMINATE — different requests
against the same catalog yield different plans, so a stub that returns one
fixed plan cannot pass. Also proves the no-host-I/O constraint by static
scan: the planner module's source imports only pure descriptor helpers and
contains no file/env/process/network API tokens.

**Plan:** doc/03_plan/agent_tasks/startup_perf_parallel_plan_2026-08-17.md (WP-15s)

## Scenarios

### startup planner discriminates between requests (positive control)

#### different requested sets yield different plans against one catalog

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- different requested sets yield different plans against one catalog


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("different requested sets yield different plans against one catalog")
val cat = disc_catalog()
var req_opt = planner_request_default("compile")
req_opt.requested = ["optimizer.basic"]
var req_lsp = planner_request_default("lsp")
req_lsp.requested = ["lsp.server"]
var req_none = planner_request_default("version")
val p_opt = plan_render(plan_startup(req_opt, cat))
val p_lsp = plan_render(plan_startup(req_lsp, cat))
val p_none = plan_render(plan_startup(req_none, cat))
# all three plans are pairwise distinct — a fixed plan cannot pass
assert_true(p_opt != p_lsp)
assert_true(p_opt != p_none)
assert_true(p_lsp != p_none)
# and each still succeeds, so the difference is content, not failure
assert_true(plan_startup(req_opt, cat).ok)
assert_true(plan_startup(req_lsp, cat).ok)
assert_true(plan_startup(req_none, cat).ok)
```

</details>

#### the same request yields the same plan (control for the control)

- the same request yields the same plan (control for the control)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the same request yields the same plan (control for the control)")
val cat = disc_catalog()
var req = planner_request_default("compile")
req.requested = ["optimizer.basic"]
assert_eq(plan_render(plan_startup(req, cat)), plan_render(plan_startup(req, cat)))
```

</details>

#### catalog content changes the plan too

- catalog content changes the plan too


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("catalog content changes the plan too")
var req = planner_request_default("compile")
req.requested = ["optimizer.basic"]
val full = plan_render(plan_startup(req, disc_catalog()))
val none: [text] = []
var small: [ComponentDescriptorV1] = []
small.push(desc2("optimizer.basic", "auto", "dynamic", "command", none))
val trimmed = plan_render(plan_startup(req, small))
assert_true(full != trimmed)
```

</details>

### startup planner performs no host I/O (static scan)

#### planner source imports only pure descriptor helpers and no I/O API tokens

- planner source imports only pure descriptor helpers and no I/O API tokens


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("planner source imports only pure descriptor helpers and no I/O API tokens")
val src = read_file("src/app/startup/startup_planner.spl")
assert_true(src.len() > 0)
# sanity: right file
assert_true(src.contains("fn plan_startup"))
assert_true(src.contains("use std.common.structural.component.descriptor"))
# forbidden host-I/O surfaces are absent from the module source
assert_true(not src.contains("std.nogc_sync_mut"))
assert_true(not src.contains("std.nogc_async_mut"))
assert_true(not src.contains("read_" + "file"))
assert_true(not src.contains("write_" + "file"))
assert_true(not src.contains("open" + "("))
assert_true(not src.contains("getenv"))
assert_true(not src.contains("env" + "("))
assert_true(not src.contains("spawn"))
assert_true(not src.contains("socket"))
assert_true(not src.contains("http"))
assert_true(not src.contains("rt_" ))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/startup_perf_parallel_plan_2026-08-17.md (WP-15s)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5cc61c085c1bf5264d188b67a39967c2e6594eb9541f99b5133c19442e73fd41`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5cc61c085c1bf5264d188b67a39967c2e6594eb9541f99b5133c19442e73fd41`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5cc61c085c1bf5264d188b67a39967c2e6594eb9541f99b5133c19442e73fd41`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/startup/startup_planner_discrimination_spec.spl
mirror: doc/06_spec/01_unit/app/startup/startup_planner_discrimination_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/startup/startup_planner_discrimination_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/startup/startup_planner_discrimination_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/startup/startup_planner_discrimination_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'different requested sets yield different plans against one catalog' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/startup/startup_planner_discrimination_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the same request yields the same plan (control for the control)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/startup/startup_planner_discrimination_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'catalog content changes the plan too' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
