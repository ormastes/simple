# WM/GUI/GPU False-Success Family Guard (Lane A0)

> `doc/04_architecture/ui/wm_host_platform_matrix.md` enumerated 31 false-success

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WM/GUI/GPU False-Success Family Guard (Lane A0)

`doc/04_architecture/ui/wm_host_platform_matrix.md` enumerated 31 false-success

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing |
| Status | In Progress |
| Source | `test/03_system/gui/wm_host_platform/wm_false_success_family_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

`doc/04_architecture/ui/wm_host_platform_matrix.md` enumerated 31 false-success
sites in the WM/GUI/GPU host seam **once, by hand**. A sweep that does not
enumerate the family leaves siblings behind: the next stub written in the same
shape lands silently unless something re-runs the sweep on every change. This
spec is that re-run: it turns five of the matrix's false-success SHAPES into
anchored, repo-wide, machine-checked searches, and cross-checks every match
against `doc/08_tracking/wm_false_success_baseline.txt`.

Two directions are both failures:
- A match with **no baseline line** is a **new sibling** — a false-success
  site the matrix never saw, or a regression of one that was fixed and came
  back.
- A baseline line with **no match** is **stale** — the site it names no
  longer has the shape the baseline claims, and the owning fix lane must
  delete the line in the same commit that fixed the site.

This guard fixes nothing. Fixing the 31 sites is lanes A1-A5's job
(`doc/03_plan/ui/wm_platform_honesty_agent_lanes.md`); this file only freezes
the enumeration so their progress is measured by baseline shrink and no
sibling lands unnoticed while they work.

## Scope and Preconditions

Five predicate families, each an anchored search over non-vendored `.spl`
source (`src/*/vendor/**` and the stb/miniaudio headers excluded):

1. `uses_native_[a-z0-9_]*_symbols()` whose body's first line is the literal
   `true` — repo-wide.
2. `readback()` bodies ending in the bare `""` success sentinel, in
   `src/lib/gc_async_mut/gpu/session/backend_*_adapter.spl`.
3. `engine2d_readback(.., "cpu_mirror")` as the unconditional, un-guarded body
   of `read_pixels_with_source()` in `backend_webgpu.spl`.
4. A counter-handle (`_ctr + 1` / `.len() + 1`) used as a return value, in
   `src/lib/nogc_async_mut/wm/*.spl`, `src/os/compositor/hosted_backend*.spl`,
   `src/lib/nogc_async_mut/gpu/dxvk_d3d11.spl`.
5. `supports_*()` / `supports()` bodies hardcoding `true`, in the same three
   file sets as predicate 4.

Not every one of the matrix's 31 sites has a shape a five-family regex can
express (a hardcoded `dx: 0`, a declared-vs-actual ABI mismatch, a Rust match
arm) — those are recorded in the baseline with predicate-tag `manual` for
count/shrink tracking, and are NOT cross-checked here; their owning fix lane's
own gate re-verifies them directly. See the baseline file's header comment for
the full accounting, including the two documented deviations from a literal
31-line copy of the matrix (cluster 1 already fixed before this lane
dispatched; three extra `dxvk_d3d11.spl` counter-handle siblings predicate 4
found beyond the matrix's single named site).

## Recovery and Troubleshooting

A RED result here means one of:
- a new false-success site landed matching one of the five shapes (add it to
  the baseline ONLY if it is being deliberately introduced, which should never
  happen — otherwise fix it), or
- a fix lane fixed a baselined site but forgot to delete its baseline line in
  the same commit.

## Compatibility and Limitations

All five searches are host-independent (pure source-shape checks over `.spl`
text); they do not depend on which platform is executing the suite.

## Scenarios

### WM false-success family guard — matches must equal the baseline, both directions

#### predicate 1 (uses_native_*_symbols hardcoded true) matches exactly the baselined sites

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- predicate 1 (uses_native_*_symbols hardcoded true) matches exactly the baselined sites
   - Expected: matched_predicate_1().trim() equals `baseline_paths_for_tag("1").trim()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("predicate 1 (uses_native_*_symbols hardcoded true) matches exactly the baselined sites")
# RED if a new uses_native_*_symbols() lands anywhere with a literal
# `true` body (new sibling), or if hosted_backend_cocoa.spl /
# hosted_backend_win32.spl stop matching (stale — site fixed, baseline
# line must be deleted by the fixing lane).
expect(matched_predicate_1().trim()).to_equal(baseline_paths_for_tag("1").trim())
```

</details>

#### predicate 2 (adapter readback() returns bare success sentinel) matches exactly the baselined sites

- predicate 2 (adapter readback() returns bare success sentinel) matches exactly the baselined sites
   - Expected: matched_predicate_2().trim() equals `baseline_paths_for_tag("2").trim()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("predicate 2 (adapter readback() returns bare success sentinel) matches exactly the baselined sites")
# RED if any session backend adapter's readback() stops or starts
# returning bare "".
expect(matched_predicate_2().trim()).to_equal(baseline_paths_for_tag("2").trim())
```

</details>

#### predicate 3 (webgpu cpu_mirror readback is unconditional) matches exactly the baselined sites

- predicate 3 (webgpu cpu_mirror readback is unconditional) matches exactly the baselined sites
   - Expected: matched_predicate_3().trim() equals `baseline_paths_for_tag("3").trim()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("predicate 3 (webgpu cpu_mirror readback is unconditional) matches exactly the baselined sites")
# RED if backend_webgpu.spl's read_pixels_with_source gains a guard
# (stale) or if the shape reappears after a fix regresses.
expect(matched_predicate_3().trim()).to_equal(baseline_paths_for_tag("3").trim())
```

</details>

#### predicate 4 (counter-handle returned as a value) matches exactly the baselined sites

- predicate 4 (counter-handle returned as a value) matches exactly the baselined sites
   - Expected: matched_predicate_4().trim() equals `baseline_paths_for_tag("4").trim()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("predicate 4 (counter-handle returned as a value) matches exactly the baselined sites")
# Covers service.spl's port/window counters and all four
# dxvk_d3d11.spl counter-handle fabrications this guard's own sweep
# found (device, swapchain, resource-id, readback handle) — three
# more than the matrix's single named site 13.
expect(matched_predicate_4().trim()).to_equal(baseline_paths_for_tag("4").trim())
```

</details>

#### predicate 5 (supports_*/supports hardcoded true) matches exactly the baselined sites

- predicate 5 (supports_*/supports hardcoded true) matches exactly the baselined sites
   - Expected: matched_predicate_5().trim() equals `baseline_paths_for_tag("5").trim()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("predicate 5 (supports_*/supports hardcoded true) matches exactly the baselined sites")
# NON-VACUITY: both sides are currently empty — the wm/hosted-backend/
# dxvk file set has no hardcoded-true supports_*() today (the one
# matrix site with this shape, backend_metal_adapter.spl:20, is
# outside this predicate's file scope and is tagged `manual`
# instead). An empty-vs-empty match is still a real oracle: it goes
# RED the moment either side gains an entry the other lacks.
expect(matched_predicate_5().trim()).to_equal(baseline_paths_for_tag("5").trim())
```

</details>

### WM false-success family guard — baseline bookkeeping

#### prints the current baseline line count so shrink is visible per run

- prints the current baseline line count so shrink is visible per run
   - Expected: header_n > 20 is true
   - Expected: n >= 0 is true
   - Expected: n <= 31 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prints the current baseline line count so shrink is visible per run")
val n = baseline_line_count()
print "WM_FALSE_SUCCESS_BASELINE_LINE_COUNT: {n}"
# NON-VACUITY, split into two independent checks (see
# doc/08_tracking/bug/2026-08-05_wm_false_success_family_guard_blocked_by_out_of_scope_gaps.md
# section 2): the data-line count `n` legitimately reaches 0 once
# every real predicate-tracked site is fixed -- that is the goal
# state, not a broken read, so `n` alone can no longer be the
# vacuity floor. Instead:
#   1. the file's `#`-prefixed HEADER never disappears (it is static
#      prose -- enumeration source, predicate-tag legend, deviations,
#      shrink-only rule -- not a per-site line), so a broken/empty/
#      truncated/unreadable file collapses this to ~0 while a
#      genuinely fully-closed baseline still carries dozens of lines;
#   2. `n` itself keeps only the real, always-true floor (`>= 0`) and
#      the upper bound (never more than the matrix's 31 sites).
val header_n = baseline_header_line_count()
expect(header_n > 20).to_equal(true)
expect(n >= 0).to_equal(true)
expect(n <= 31).to_equal(true)
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
- `REQ-WM-HOST-PLATFORM-003`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6eb996ad12977d0097308b19a92eee259266f92ce51b4325f7c2b5a5403b921d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6eb996ad12977d0097308b19a92eee259266f92ce51b4325f7c2b5a5403b921d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6eb996ad12977d0097308b19a92eee259266f92ce51b4325f7c2b5a5403b921d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/gui/wm_host_platform/wm_false_success_family_spec.spl
mirror: doc/06_spec/03_system/gui/wm_host_platform/wm_false_success_family_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/03_system/gui/wm_host_platform/wm_false_success_family_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/wm_host_platform/wm_false_success_family_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: primary workflow
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/wm_host_platform/wm_false_success_family_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/gui/wm_host_platform/wm_false_success_family_spec.spl:148:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'predicate 1 (uses_native_*_symbols hardcoded true) matches exactly the baselined sites' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_host_platform/wm_false_success_family_spec.spl:157:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'predicate 2 (adapter readback() returns bare success sentinel) matches exactly the baselined sites' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_host_platform/wm_false_success_family_spec.spl:164:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'predicate 3 (webgpu cpu_mirror readback is unconditional) matches exactly the baselined sites' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
