# WM/GUI Host Seam — FreeBSD Honest-Refusal Verification (Task #60, Lane B)

> Task #60 was filed as "FreeBSD WM seam missing entirely." The real state,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WM/GUI Host Seam — FreeBSD Honest-Refusal Verification (Task #60, Lane B)

Task #60 was filed as "FreeBSD WM seam missing entirely." The real state,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing |
| Status | In Progress |
| Source | `test/03_system/gui/wm_host_platform/wm_host_freebsd_refusal_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Task #60 was filed as "FreeBSD WM seam missing entirely." The real state,
confirmed by reading `src/lib/nogc_async_mut/wm/host.spl`, is smaller: the
honest-refusal vocabulary for FreeBSD was ALREADY implemented —
`wm_host_2d_for("freebsd")` already returns `WmHost2dUnavailable` with an
accurate reason. The only genuine defects were two docstring lies in
`src/os/compositor/hosted_input_backend.spl` (lines 4 and 152) that listed
FreeBSD alongside macOS/Linux/Windows as a supported winit host desktop, when
no 2D backend exists for it. This lane fixed those two lines and this file
verifies the fix, plus the seam's pre-existing refusal behaviour.

Implementing a real FreeBSD 2D backend is an explicit non-goal of this lane
(see `doc/03_plan/ui/wm_platform_honesty_agent_lanes.md`, Lane B) — a real
backend would build on Linux SDL2/X11 arms that do not exist yet, so building
FreeBSD's first would invert priority.

## Scope and Preconditions

This file's `describe` blocks run unconditionally on any host — they exercise
the seam's IN-MEMORY refusal object, which makes no OS calls and needs no
FreeBSD hardware. The in-VM runtime receipt (the seam's ACTUAL behaviour under
a real FreeBSD kernel) is a separate artifact:
`scripts/check/check-freebsd-wm-seam-refusal.shs`, which drives
`scripts/check/check-freebsd-bootstrap-qemu.shs`'s QEMU/OVMF harness and
prints `FREEBSD WM SEAM VERDICT: platform=... refusal=... reason=...` to its
own transcript. This spec file only proves the Linux-observable half:
the refusal object's shape and the absence of contradicting prose.

## Compatibility and Limitations

The anchored-grep sweep below is scoped to the WM/compositor source tree
(`src/os/compositor`, `src/lib/nogc_async_mut/wm`, `src/os/services/wm`,
`src/lib/common/window_protocol`, `src/os/desktop`) rather than the whole
repo: FreeBSD is a legitimate build/package/linker target elsewhere (see
`src/lib/nogc_sync_mut/platform.spl`, `src/app/setup/freebsd_ssh.spl`, the
linker backend, etc.) and asserting "outside the refusal vocabulary" against
that broader set would flag unrelated, honest platform-support code.

## Scenarios

### WM host seam — FreeBSD routes to the honest refusal

#### wm_host_2d_for(\

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- wm_host_2d_for(\
   - Expected: host.platform equals `freebsd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("wm_host_2d_for(\")
val host = wm_host_2d_for("freebsd")
expect(host.platform).to_equal("freebsd")
```

</details>

#### the refusal reason names the missing backend, not a vague error

- the refusal reason names the missing backend, not a vague error
   - Expected: host.reason contains `backend`
   - Expected: host.reason.len() > 10 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("the refusal reason names the missing backend, not a vague error")
val host = wm_host_2d_for("freebsd")
expect(host.reason.contains("backend")).to_equal(true)
# Non-vacuity: the reason must be platform-specific text, not empty.
expect(host.reason.len() > 10).to_equal(true)
```

</details>

#### wm_host_2d_unavailable constructs the same refusal shape directly

- wm_host_2d_unavailable constructs the same refusal shape directly
   - Expected: host.platform equals `freebsd`
   - Expected: host.reason contains `backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("wm_host_2d_unavailable constructs the same refusal shape directly")
val host = wm_host_2d_unavailable("freebsd", "no 2D backend exists for this platform")
expect(host.platform).to_equal("freebsd")
expect(host.reason.contains("backend")).to_equal(true)
```

</details>

### WM host seam — all four seam methods refuse on FreeBSD, none report green

#### surface_acquire refuses rather than returning a usable handle

- surface_acquire refuses rather than returning a usable handle
   - Expected: surface.ok is false
   - Expected: surface.state contains `unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("surface_acquire refuses rather than returning a usable handle")
val host = wm_host_2d_for("freebsd")
val surface = host.surface_acquire(800u32, 600u32)
expect(surface.ok).to_equal(false)
expect(surface.state.contains("unavailable")).to_equal(true)
```

</details>

#### surface_present refuses rather than reporting a fake presentation

- surface_present refuses rather than reporting a fake presentation
   - Expected: status.ok is false
   - Expected: status.state contains `unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("surface_present refuses rather than reporting a fake presentation")
val host = wm_host_2d_for("freebsd")
val status = host.surface_present(1u64, 100)
expect(status.ok).to_equal(false)
expect(status.state.contains("unavailable")).to_equal(true)
```

</details>

#### surface_release refuses rather than reporting a fake teardown

- surface_release refuses rather than reporting a fake teardown
   - Expected: status.ok is false
   - Expected: status.state contains `unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("surface_release refuses rather than reporting a fake teardown")
val host = wm_host_2d_for("freebsd")
val status = host.surface_release(1u64)
expect(status.ok).to_equal(false)
expect(status.state.contains("unavailable")).to_equal(true)
```

</details>

#### event_poll refuses rather than reporting a fake empty-but-healthy queue

- event_poll refuses rather than reporting a fake empty-but-healthy queue
   - Expected: poll.ok is false
   - Expected: poll.state contains `unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("event_poll refuses rather than reporting a fake empty-but-healthy queue")
val host = wm_host_2d_for("freebsd")
val poll = host.event_poll()
expect(poll.ok).to_equal(false)
expect(poll.state.contains("unavailable")).to_equal(true)
```

</details>

### WM host seam — no source in the WM tree claims FreeBSD support outside refusal vocabulary

#### the seam file itself exists and mentions freebsd honestly

- the seam file itself exists and mentions freebsd honestly
   - Expected: file_exists("src/lib/nogc_async_mut/wm/host.spl") is true
   - Expected: source_contains("src/lib/nogc_async_mut/wm/host.spl", "WmHost2dUnavailable") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("the seam file itself exists and mentions freebsd honestly")
expect(file_exists("src/lib/nogc_async_mut/wm/host.spl")).to_equal(true)
expect(source_contains("src/lib/nogc_async_mut/wm/host.spl", "WmHost2dUnavailable")).to_equal(true)
```

</details>

#### hosted_input_backend.spl no longer lists FreeBSD as a supported winit host desktop

- hosted_input_backend.spl no longer lists FreeBSD as a supported winit host desktop
   - Expected: source_contains(path, "no 2D backend") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("hosted_input_backend.spl no longer lists FreeBSD as a supported winit host desktop")
# EXPECTED GREEN after the Lane B fix: the two docstring lines (4, 152)
# used to read "(used on macOS, Linux, Windows, FreeBSD host
# desktops)" and "Used on host desktops (macOS, Linux, Windows,
# FreeBSD)" with no refusal qualifier anywhere near them. The fix
# keeps FreeBSD mentioned (it is still relevant context) but pairs it
# with the refusal fact instead of listing it as a working target.
val path = "src/os/compositor/hosted_input_backend.spl"
expect(source_contains(path, "no 2D backend")).to_equal(true)
```

</details>

#### every FreeBSD mention in the WM/compositor tree carries the refusal vocabulary

- every FreeBSD mention in the WM/compositor tree carries the refusal vocabulary
   - Expected: wm_tree_unguarded_freebsd_claims() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("every FreeBSD mention in the WM/compositor tree carries the refusal vocabulary")
# The general sweep: any file in the WM tree that says "freebsd" at
# all must ALSO say so somewhere in the same file. A file that merely
# lists FreeBSD alongside working platforms, with no refusal marker
# anywhere, is exactly the lie this lane fixes.
expect(wm_tree_unguarded_freebsd_claims()).to_equal("")
```

</details>

#### the sweep actually found files to check (non-vacuity)

- the sweep actually found files to check (non-vacuity)
   - Expected: mentions contains `host.spl`
   - Expected: mentions contains `hosted_input_backend.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("the sweep actually found files to check (non-vacuity)")
# Without this, a RED in the sweep above whose file list is empty
# (e.g. from a typo'd directory) would silently look identical to a
# real pass. At least host.spl and hosted_input_backend.spl must
# appear.
val mentions = wm_tree_freebsd_mentions()
expect(mentions.contains("host.spl")).to_equal(true)
expect(mentions.contains("hosted_input_backend.spl")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WM-HOST-PLATFORM-005`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `aea4540b824de5f0ea2eddc81bfdcafcdeabe5968383143669b1d1c05cdbba94`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aea4540b824de5f0ea2eddc81bfdcafcdeabe5968383143669b1d1c05cdbba94`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aea4540b824de5f0ea2eddc81bfdcafcdeabe5968383143669b1d1c05cdbba94`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/gui/wm_host_platform/wm_host_freebsd_refusal_spec.spl
mirror: doc/06_spec/03_system/gui/wm_host_platform/wm_host_freebsd_refusal_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/03_system/gui/wm_host_platform/wm_host_freebsd_refusal_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/wm_host_platform/wm_host_freebsd_refusal_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/wm_host_platform/wm_host_freebsd_refusal_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/gui/wm_host_platform/wm_host_freebsd_refusal_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wm_host_2d_for(\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_host_platform/wm_host_freebsd_refusal_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the refusal reason names the missing backend, not a vague error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_host_platform/wm_host_freebsd_refusal_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wm_host_2d_unavailable constructs the same refusal shape directly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
