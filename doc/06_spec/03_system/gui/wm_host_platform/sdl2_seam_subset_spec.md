# WM/GUI Host Seam — SDL2 Seam-Subset Audit + Ratchet (Task lane C)

> SDL2 is the host 2D-surface + event-source implementation for the WM

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WM/GUI Host Seam — SDL2 Seam-Subset Audit + Ratchet (Task lane C)

SDL2 is the host 2D-surface + event-source implementation for the WM

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing |
| Status | In Progress |
| Source | `test/03_system/gui/wm_host_platform/sdl2_seam_subset_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

SDL2 is the host 2D-surface + event-source implementation for the WM
compositor, not configuration data. The registered `rt_sdl2_*` surface is 66
entry points; the WM host seam (`src/lib/nogc_async_mut/wm/host.spl`, trait
`WmHost2d`) is 4 methods (`surface_acquire`, `surface_present`,
`surface_release`, `event_poll`). This file answers, mechanically and on every
run, the question the audit doc
(`doc/04_architecture/ui/sdl2_seam_subset_audit.md`) answers once in prose:
does compositor code reach only the seam-shaped subset, or does it reach the
extras (timers, display bounds/DPI, window title/size/position/fullscreen,
cursor grab/warp, clipboard, lifecycle)?

Only `src/os/compositor/**/*.spl` and `src/lib/nogc_async_mut/wm/**/*.spl` are
in scope. `game2d`, `web_ui`, `desktop/display.spl`, and `app/io/window_*`
legitimately want the full SDL2 surface (window management, multi-display,
clipboard) and are explicitly OUT of this ratchet — Rule 4 below proves that
exclusion is doing real work, not vacuously passing.

## Scope and Preconditions

Text-reading stdlib entry points do not resolve under the current tooling
binary (same constraint as `wm_host_false_success_guard_spec.spl`), so all
source-shape checks below go through the shell via `shell_output`. Every
shell pipeline used here is exit-code-safe (the last command in each pipeline
always succeeds, even on zero matches) so `shell_output`'s "" on the empty
case is never confused with its "" on command failure — see
`src/lib/nogc_sync_mut/io_runtime.spl::shell_output`, which collapses both to
the same string.

## Recovery and Troubleshooting

A RED result under Rule 2 means compositor or wm-seam code started calling an
SDL2 entry point outside the seam allowlist that is not yet in
`doc/08_tracking/wm_sdl2_extras_baseline.txt`. Either the call is a genuine
new seam-shaped need (add it to the allowlist doc discussion first) or it is
a hidden precondition (dependency-audit class C) that should route through
the seam instead. A RED under Rule 3 means a baseline line no longer matches
any real reference — delete the stale line in the same commit as whatever fix
made it stale.

## Compatibility and Limitations

The scanner treats a `rt_sdl2_*` token on a non-full-line-comment line as a
reference, including inside multi-line docstrings (it does not parse
docstring boundaries) — this is deliberately conservative: a prose mention of
an extern in a docstring still earns a baseline line rather than being
silently ignored, so the ratchet cannot be defeated by moving a real call
into a comment.

## Scenarios

### SDL2 seam-subset audit — registered surface size

#### the runtime registers the audited 66-entry-point surface

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- the runtime registers the audited 66-entry-point surface
   - Expected: sdl2_registered_surface_count() equals `66`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("the runtime registers the audited 66-entry-point surface")
# NON-VACUITY: this is a real count, not a hardcoded skip — if a new
# rt_sdl2_* function is added or removed from runtime_sdl2.c without
# updating the audit doc, this goes RED and says so.
expect(sdl2_registered_surface_count()).to_equal("66")
```

</details>

### SDL2 seam-subset audit — compositor ratchet

#### no compositor or wm-seam file reaches an SDL2 symbol outside the seam allowlist or the extras baseline

- no compositor or wm-seam file reaches an SDL2 symbol outside the seam allowlist or the extras baseline
   - Expected: sdl2_compositor_scope_violations() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("no compositor or wm-seam file reaches an SDL2 symbol outside the seam allowlist or the extras baseline")
# EXPECTED GREEN today: hosted_backend_sdl2.spl and
# hosted_input_sdl2.spl's non-seam references (init/quit/get_mouse_x/
# get_mouse_y plus several dangling externs) are all recorded in
# doc/08_tracking/wm_sdl2_extras_baseline.txt.
expect(sdl2_compositor_scope_violations()).to_equal("")
```

</details>

#### the compositor scan reaches the two SDL2 backend files (positive control)

- the compositor scan reaches the two SDL2 backend files (positive control)
   - Expected: listing contains `hosted_backend_sdl2.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("the compositor scan reaches the two SDL2 backend files (positive control)")
# Without this, a RED-then-fixed rule above could be a broken
# discovery glob rather than a real compliant scope.
val listing = shell_output('/usr/bin/grep -rlE "rt_sdl2_[A-Za-z0-9_]+" --include=*.spl src/os/compositor src/lib/nogc_async_mut/wm 2>/dev/null')
expect(listing.contains("hosted_backend_sdl2.spl")).to_equal(true)
```

</details>

### SDL2 seam-subset audit — baseline hygiene

#### every extras-baseline line still corresponds to a real reference

- every extras-baseline line still corresponds to a real reference
   - Expected: sdl2_stale_baseline_lines() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("every extras-baseline line still corresponds to a real reference")
# EXPECTED GREEN today. A fix lane that removes a dangling extern or
# deletes hosted_input_sdl2.spl (per the platform-honesty lane plan,
# A4) must delete the matching baseline line in the same commit —
# this is what enforces that.
expect(sdl2_stale_baseline_lines()).to_equal("")
```

</details>

### SDL2 seam-subset audit — non-compositor SDL2 consumers stay excluded

#### desktop/display.spl is a real full-surface consumer (would fail if it were in scope)

- desktop/display.spl is a real full-surface consumer (would fail if it were in scope)
   - Expected: display_violations contains `VIOLATION:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("desktop/display.spl is a real full-surface consumer (would fail if it were in scope)")
# Establishes the premise: if the exclusion below did nothing (e.g.
# display.spl happened to already be seam-only), excluding it would
# prove nothing about the ratchet's boundary.
val display_violations = sdl2_violations_in("src/lib/nogc_sync_mut/desktop/display.spl")
expect(display_violations.contains("VIOLATION:")).to_equal(true)
```

</details>

#### desktop/display.spl is never discovered by the compositor-scoped scan

- desktop/display.spl is never discovered by the compositor-scoped scan
   - Expected: listing does not contain `desktop/display.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("desktop/display.spl is never discovered by the compositor-scoped scan")
val listing = shell_output('/usr/bin/grep -rlE "rt_sdl2_[A-Za-z0-9_]+" --include=*.spl src/os/compositor src/lib/nogc_async_mut/wm 2>/dev/null')
expect(listing.contains("desktop/display.spl")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WM-HOST-PLATFORM-006`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1af9eb5f065db87ec2a757f3d5a9387bc9933dcae1bea9a28c75c4b09e4f3a9f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1af9eb5f065db87ec2a757f3d5a9387bc9933dcae1bea9a28c75c4b09e4f3a9f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1af9eb5f065db87ec2a757f3d5a9387bc9933dcae1bea9a28c75c4b09e4f3a9f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/gui/wm_host_platform/sdl2_seam_subset_spec.spl
mirror: doc/06_spec/03_system/gui/wm_host_platform/sdl2_seam_subset_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/03_system/gui/wm_host_platform/sdl2_seam_subset_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/wm_host_platform/sdl2_seam_subset_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: primary workflow
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/wm_host_platform/sdl2_seam_subset_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/gui/wm_host_platform/sdl2_seam_subset_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the runtime registers the audited 66-entry-point surface' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_host_platform/sdl2_seam_subset_spec.spl:132:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'no compositor or wm-seam file reaches an SDL2 symbol outside the seam allowlist or the extras baseline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_host_platform/sdl2_seam_subset_spec.spl:141:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the compositor scan reaches the two SDL2 backend files (positive control)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
