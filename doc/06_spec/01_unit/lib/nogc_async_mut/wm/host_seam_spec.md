# host_seam_spec

> WM host/OS seam — the portability-contract check.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# host_seam_spec

WM host/OS seam — the portability-contract check.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/wm/host_seam_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

WM host/OS seam — the portability-contract check.

ONE check, asserting exactly the contract:

    If Simple 2D (surface + event delivery) runs on a platform, the WM runs on
    that platform.

The WM frame logic (`wm_host_2d_frame`) contains no platform branch, so proving
the contract means proving two things:

  1. Swapping the seam implementation does not change WM behaviour — the same
     frame logic runs unmodified against whatever satisfies the four methods.
  2. An implementation that cannot reach an OS can never report a green frame.

Point 2 is the tripwire. Every real platform currently refuses, because no
backend is reachable yet (the real Cocoa/Win32/SDL2 backends exist but no
dispatcher selects them). When the dispatch lane wires one, its assertion here
flips — which is the signal that the platform genuinely became supported,
rather than a struct being renamed after it.

## Scenarios

### WM 2D+event seam — portability contract

#### runs the WM frame to completion with exact values, not vacuously

- runs the WM frame to completion with exact values, not vacuously
   - Expected: r.surface_ok is true
   - Expected: r.present_ok is true
   - Expected: r.released_ok is true
   - Expected: r.events_drained equals `3`
   - Expected: r.surface_width equals `800u32`
   - Expected: r.surface_height equals `600u32`
   - Expected: r.steps equals `acquire(acquired) present(presented) events(3) release(released)`
   - Expected: r.event_trace equals `7/65/0,0;7/0/12,34;7/0/12,34;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("runs the WM frame to completion with exact values, not vacuously")
val r = wm_host_2d_frame(wm_host_2d_reference(_screen(), _events()), _request())
expect(r.surface_ok).to_equal(true)
expect(r.present_ok).to_equal(true)
expect(r.released_ok).to_equal(true)
expect(r.events_drained).to_equal(3)
expect(r.surface_width).to_equal(800u32)
expect(r.surface_height).to_equal(600u32)
expect(r.steps).to_equal("acquire(acquired) present(presented) events(3) release(released)")
expect(r.event_trace).to_equal("7/65/0,0;7/0/12,34;7/0/12,34;")
```

</details>

#### keeps WM behaviour identical when the seam implementation is swapped

- keeps WM behaviour identical when the seam implementation is swapped
   - Expected: b equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps WM behaviour identical when the seam implementation is swapped")
val a = _digest(wm_host_2d_frame(wm_host_2d_reference(_screen(), _events()), _request()))
val b = _digest(wm_host_2d_frame(wm_host_2d_reference(_screen(), _events()), _request()))
expect(b).to_equal(a)
val refused = _digest(wm_host_2d_frame(wm_host_2d_unavailable("nowhere", "no backend"), _request()))
expect_not(refused == a)
```

</details>

#### never reports a green frame for a platform with no reachable backend

- never reports a green frame for a platform with no reachable backend
   - Expected: r.events_drained equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("never reports a green frame for a platform with no reachable backend")
for platform in ["macos", "windows", "linux", "freebsd", "simpleos"]:
    val r = wm_host_2d_frame(wm_host_2d_for(platform), _request())
    expect_not(r.surface_ok)
    expect_not(r.present_ok)
    expect_not(r.released_ok)
    expect(r.events_drained).to_equal(0)
    expect(r.surface_state).to_contain("unavailable:" + platform)
```

</details>

#### refuses when the reference seam has no display bound

- refuses when the reference seam has no display bound
   - Expected: r.surface_state equals `no-display`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("refuses when the reference seam has no display bound")
val r = wm_host_2d_frame(wm_host_2d_reference(Size.wh(0, 0), _events()), _request())
expect_not(r.surface_ok)
expect(r.surface_state).to_equal("no-display")
expect_not(r.present_ok)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a7ba11599003a6c3c4405d178bdc403adf0125b11970837a0a70f238bf3d3140`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a7ba11599003a6c3c4405d178bdc403adf0125b11970837a0a70f238bf3d3140`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a7ba11599003a6c3c4405d178bdc403adf0125b11970837a0a70f238bf3d3140`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/nogc_async_mut/wm/host_seam_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/wm/host_seam_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/wm/host_seam_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/wm/host_seam_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/wm/host_seam_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/wm/host_seam_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs the WM frame to completion with exact values, not vacuously' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/wm/host_seam_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps WM behaviour identical when the seam implementation is swapped' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/wm/host_seam_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never reports a green frame for a platform with no reachable backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
