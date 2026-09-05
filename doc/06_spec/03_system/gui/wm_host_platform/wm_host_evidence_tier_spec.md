# WM/GUI Host Seam — Evidence Tier Ledger

> This suite verifies that the WM/GUI/web host seam is implemented on each

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WM/GUI Host Seam — Evidence Tier Ledger

This suite verifies that the WM/GUI/web host seam is implemented on each

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing |
| Status | In Progress |
| Source | `test/03_system/gui/wm_host_platform/wm_host_evidence_tier_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

This suite verifies that the WM/GUI/web host seam is implemented on each
target platform. The portability contract under test is:

> WM/GUI/web is portable code over a host seam of *2D surface + event
> source*; every platform implements that seam.

The canonical 2D-surface seam is `trait CompositorBackend` in
`src/os/compositor/display_backend_core.spl` (11 methods). The event half is
`RenderBackend.poll_event` in `src/lib/common/ui/backend.spl`.

## Scope and Preconditions

THE CENTRAL HONESTY CONSTRAINT OF THIS FILE.

A conformance result is only as good as the host that produced it. This file
computes, at runtime, an *evidence tier* per platform, and every other spec in
this directory is required to label its results with that tier.

    RUNTIME-NATIVE   the spec process is executing ON that platform
    RUNTIME-QEMU     a QEMU receipt artifact for that platform is present
    STATIC-ONLY      neither — structural checks only, INCONCLUSIVE BY HOST

`STATIC-ONLY` is NOT a pass. It means "this host cannot execute this
platform, so no runtime claim is made". A suite that reports green for all
five platforms from a single host is lying; this ledger is the structural
mechanism that prevents that, rather than a comment asking the reader to be
careful.

The tier is DERIVED (from `host_os()` and from the presence of receipt
artifacts), never hardcoded. Receipts are per-run artifacts and are
deliberately NOT committed, so a fresh checkout correctly reports
`STATIC-ONLY` for every non-host platform until a harness actually runs.

`pending()` is deliberately not used to represent "cannot run here": it is
invisible to the spec verdict line (it increments examples and never
failures), which is precisely the failure mode this file exists to prevent.

## Compatibility and Limitations

On a Linux host: Linux is RUNTIME-NATIVE. macOS and Windows are STATIC-ONLY
and cannot be executed. FreeBSD and SimpleOS are STATIC-ONLY unless their
QEMU harness has been run in this working copy.

## Scenarios

### WM host seam — evidence tier ledger

#### assigns exactly one tier to every target platform

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- assigns exactly one tier to every target platform
   - Expected: known is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("assigns exactly one tier to every target platform")
var i = 0
val ps = wm_target_platforms()
while i < ps.len():
    val t = evidence_tier(ps[i])
    val known = t == TIER_RUNTIME_NATIVE or t == TIER_RUNTIME_QEMU or t == TIER_STATIC_ONLY
    expect(known).to_equal(true)
    i = i + 1
```

</details>

#### grants RUNTIME-NATIVE to the executing host and to no other platform

- grants RUNTIME-NATIVE to the executing host and to no other platform
   - Expected: ps[i] equals `host_os()`
   - Expected: natives equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("grants RUNTIME-NATIVE to the executing host and to no other platform")
var i = 0
val ps = wm_target_platforms()
var natives = 0
while i < ps.len():
    if evidence_tier(ps[i]) == TIER_RUNTIME_NATIVE:
        natives = natives + 1
        expect(ps[i]).to_equal(host_os())
    i = i + 1
expect(natives).to_equal(1)
```

</details>

#### never grants a runtime claim to a platform this host cannot execute

- never grants a runtime claim to a platform this host cannot execute
   - Expected: has_qemu_receipt(p) is false
   - Expected: evidence_tier(p) equals `TIER_STATIC_ONLY`
   - Expected: tier_permits_runtime_claim(p) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("never grants a runtime claim to a platform this host cannot execute")
# macOS and Windows have no QEMU harness in this repo at all, so on
# any host that is not itself macOS/Windows they MUST be static-only.
# This is the assertion that would catch a suite quietly reporting
# green for all five platforms.
var i = 0
val unexecutable = ["macos", "windows"]
while i < unexecutable.len():
    val p = unexecutable[i]
    if p != host_os():
        expect(has_qemu_receipt(p)).to_equal(false)
        expect(evidence_tier(p)).to_equal(TIER_STATIC_ONLY)
        expect(tier_permits_runtime_claim(p)).to_equal(false)
    i = i + 1
```

</details>

#### reports a static-only tier that is explicitly labelled inconclusive

- reports a static-only tier that is explicitly labelled inconclusive


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports a static-only tier that is explicitly labelled inconclusive")
# The label must carry its own meaning into the spec output, so a
# reader scanning results cannot mistake it for a pass.
expect(TIER_STATIC_ONLY).to_contain("INCONCLUSIVE-BY-HOST")
expect(TIER_STATIC_ONLY).to_contain("STATIC-ONLY")
```

</details>

#### derives the tier rather than hardcoding it

- derives the tier rather than hardcoding it
   - Expected: evidence_tier(host_os()) equals `TIER_RUNTIME_NATIVE`
   - Expected: tier_permits_runtime_claim(host_os()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("derives the tier rather than hardcoding it")
# Sabotage anchor: if evidence_tier ever stops consulting host_os(),
# this pins the one platform that IS the host.
expect(evidence_tier(host_os())).to_equal(TIER_RUNTIME_NATIVE)
expect(tier_permits_runtime_claim(host_os())).to_equal(true)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WM-HOST-PLATFORM-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `40fb61ee2189e3bb9bf5b607f19fb72e446e847c9d142d86cce7e83f811c31a3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `40fb61ee2189e3bb9bf5b607f19fb72e446e847c9d142d86cce7e83f811c31a3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `40fb61ee2189e3bb9bf5b607f19fb72e446e847c9d142d86cce7e83f811c31a3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/gui/wm_host_platform/wm_host_evidence_tier_spec.spl
mirror: doc/06_spec/03_system/gui/wm_host_platform/wm_host_evidence_tier_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/03_system/gui/wm_host_platform/wm_host_evidence_tier_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/wm_host_platform/wm_host_evidence_tier_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/wm_host_platform/wm_host_evidence_tier_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/wm_host_platform/wm_host_evidence_tier_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/gui/wm_host_platform/wm_host_evidence_tier_spec.spl:121:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'assigns exactly one tier to every target platform' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_host_platform/wm_host_evidence_tier_spec.spl:132:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'grants RUNTIME-NATIVE to the executing host and to no other platform' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_host_platform/wm_host_evidence_tier_spec.spl:145:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never grants a runtime claim to a platform this host cannot execute' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
