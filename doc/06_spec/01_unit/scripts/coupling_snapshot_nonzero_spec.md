# Coupling Snapshot Nonzero Specification

> Tests covering coupling closure snapshot (Phase E bracketing).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Coupling Snapshot Nonzero Specification

## Scenarios

### coupling closure snapshot (Phase E bracketing)

#### produces a non-vacuous Results line: N modules, E edges, both > 0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- produces a non-vacuous Results line: N modules, E edges, both > 0
- Run --check; parse the Results line; assert both counts are positive integers
- Both module and edge counts are strictly positive
- The Results line itself is present verbatim


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces a non-vacuous Results line: N modules, E edges, both > 0")
step("Run --check; parse the Results line; assert both counts are positive integers")
val out = process_run("sh", ["-c",
    "o=$(sh " + CHECK + " --check); rc=$?; " +
    "r=$(printf '%s\\n' \"$o\" | grep '^Results: '); " +
    "m=$(printf '%s\\n' \"$r\" | sed 's/^Results: \\([0-9]*\\) modules, \\([0-9]*\\) edges.*/\\1/'); " +
    "e=$(printf '%s\\n' \"$r\" | sed 's/^Results: \\([0-9]*\\) modules, \\([0-9]*\\) edges.*/\\2/'); " +
    "ok=BAD; if [ -n \"$m\" ] && [ -n \"$e\" ] && [ \"$m\" -gt 0 ] && [ \"$e\" -gt 0 ]; then ok=NONZERO_OK; fi; " +
    "echo \"RC=$rc COUNTS=$ok LINE=$r\""])
val s: text = out.0
step("Both module and edge counts are strictly positive")
expect(s).to_contain("COUNTS=NONZERO_OK")
step("The Results line itself is present verbatim")
expect(s).to_contain("LINE=Results: ")
```

</details>

#### a zero-module snapshot is an ERROR (exit 2), never a pass

- a zero-module snapshot is an ERROR (exit 2), never a pass
- Feed a synthetic zero-module current snapshot into --compare
- Exit code is 2 and the verdict is ERROR — a vacuous measurement is never evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a zero-module snapshot is an ERROR (exit 2), never a pass")
step("Feed a synthetic zero-module current snapshot into --compare")
val out = process_run("sh", ["-c",
    "d=$(mktemp -d); " +
    "printf 'modules 100\\nedges 200\\nlargest_scc 10\\n' > $d/prev; " +
    "printf 'modules 0\\nedges 0\\nlargest_scc 0\\n' > $d/zero; " +
    "o=$(sh " + CHECK + " --compare $d/prev $d/zero); rc=$?; " +
    "rm -rf $d; " +
    "last=$(printf '%s\\n' \"$o\" | tail -1); echo \"RC=$rc LAST=$last\""])
val s: text = out.0
step("Exit code is 2 and the verdict is ERROR — a vacuous measurement is never evidence")
expect(s).to_contain("RC=2")
expect(s).to_contain("LAST=ERROR")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/scripts/coupling_snapshot_nonzero_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering coupling closure snapshot (Phase E bracketing).
- coupling closure snapshot (Phase E bracketing)

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ded70f6d0a1853638ebbd597dfef45c0c072aba18d98474dab12a628c7451ea0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ded70f6d0a1853638ebbd597dfef45c0c072aba18d98474dab12a628c7451ea0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ded70f6d0a1853638ebbd597dfef45c0c072aba18d98474dab12a628c7451ea0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/scripts/coupling_snapshot_nonzero_spec.spl
mirror: doc/06_spec/01_unit/scripts/coupling_snapshot_nonzero_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/scripts/coupling_snapshot_nonzero_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/scripts/coupling_snapshot_nonzero_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/scripts/coupling_snapshot_nonzero_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces a non-vacuous Results line: N modules, E edges, both > 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/scripts/coupling_snapshot_nonzero_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a zero-module snapshot is an ERROR (exit 2), never a pass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
