# Browser Static Shell Cache Specification

> Tests covering browser backend static shell cache.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Static Shell Cache Specification

## Scenarios

### browser backend static shell cache

#### reuses full static shell html across stable frames

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reuses full static shell html across stable frames
   - Expected: e equals ``
   - Expected: backend.static_shell_html_stores equals `1`
   - Expected: backend.static_shell_html_hits equals `0`
   - Expected: backend.static_frame_stores equals `1`
   - Expected: backend.static_frame_hits equals `0`
   - Expected: backend.static_frame_fast_stores equals `1`
   - Expected: backend.static_frame_fast_hits equals `0`
   - Expected: backend.last_artifact_pixels equals `64 * 48`
   - Expected: backend.static_shell_html_stores equals `1`
   - Expected: backend.static_shell_html_hits equals `0`
   - Expected: backend.static_frame_stores equals `1`
   - Expected: backend.static_frame_hits equals `1`
   - Expected: backend.static_frame_fast_stores equals `1`
   - Expected: backend.static_frame_fast_hits equals `1`
   - Expected: backend.last_artifact_pixels equals `64 * 48`
   - Expected: backend.render_cached_static_frame() is true
   - Expected: backend.static_frame_hits equals `2`
   - Expected: backend.static_frame_fast_hits equals `1`
   - Expected: e equals ``
   - Expected: session.draw_ir_submission_revision equals `1`
   - Expected: backend.static_frame_fast_hits equals `0`
   - Expected: session.draw_ir_submission_revision equals `2`
   - Expected: backend.static_frame_fast_hits equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 53 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reuses full static shell html across stable frames")
val state = static_browser_state()
val backend_result = BrowserBackend.create(64, 48, "software")
match backend_result:
    Err(e):
        expect(e).to_equal("")
    Ok(backend):
        backend.render_frame(state.tree, state)
        expect(backend.static_shell_html_stores).to_equal(1)
        expect(backend.static_shell_html_hits).to_equal(0)
        expect(backend.static_frame_stores).to_equal(1)
        expect(backend.static_frame_hits).to_equal(0)
        expect(backend.static_frame_fast_stores).to_equal(1)
        expect(backend.static_frame_fast_hits).to_equal(0)
        expect(backend.last_artifact_pixels).to_equal(64 * 48)

        backend.render_frame(state.tree, state)
        expect(backend.static_shell_html_stores).to_equal(1)
        expect(backend.static_shell_html_hits).to_equal(0)
        expect(backend.static_frame_stores).to_equal(1)
        expect(backend.static_frame_hits).to_equal(1)
        expect(backend.static_frame_fast_stores).to_equal(1)
        expect(backend.static_frame_fast_hits).to_equal(1)
        expect(backend.last_artifact_pixels).to_equal(64 * 48)

        expect(backend.render_cached_static_frame()).to_equal(true)
        expect(backend.static_frame_hits).to_equal(2)
        expect(backend.static_frame_fast_hits).to_equal(1)

val session = UISession.new(state.tree)
val session_backend_result = BrowserBackend.create(64, 48, "software")
match session_backend_result:
    Err(e):
        expect(e).to_equal("")
    Ok(backend):
        val first = session.submit_widget_draw_ir(
            64, 48, DRAW_IR_BACKEND_GPU
        )
        backend.render_frame_with_composition(
            state.tree, state, first
        )
        expect(session.draw_ir_submission_revision).to_equal(1)
        expect(backend.static_frame_fast_hits).to_equal(0)

        val second = session.submit_widget_draw_ir(
            64, 48, DRAW_IR_BACKEND_GPU
        )
        backend.render_frame_with_composition(
            state.tree, state, second
        )
        expect(session.draw_ir_submission_revision).to_equal(2)
        expect(backend.static_frame_fast_hits).to_equal(1)
```

</details>

#### does not claim cached static frame before first render

- does not claim cached static frame before first render
   - Expected: e equals ``
   - Expected: backend.render_cached_static_frame() is false
   - Expected: backend.static_frame_hits equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("does not claim cached static frame before first render")
val backend_result = BrowserBackend.create(64, 48, "software")
match backend_result:
    Err(e):
        expect(e).to_equal("")
    Ok(backend):
        expect(backend.render_cached_static_frame()).to_equal(false)
        expect(backend.static_frame_hits).to_equal(0)
```

</details>

#### reuses present pixels until framebuffer changes

- reuses present pixels until framebuffer changes
   - Expected: e equals ``
   - Expected: first_pixels.len() equals `64 * 48`
   - Expected: backend.present_pixels_cache_stores equals `1`
   - Expected: backend.present_pixels_cache_hits equals `0`
   - Expected: second_pixels.len() equals `64 * 48`
   - Expected: backend.present_pixels_cache_stores equals `1`
   - Expected: backend.present_pixels_cache_hits equals `1`
   - Expected: third_pixels.len() equals `64 * 48`
   - Expected: backend.present_pixels_cache_stores equals `1`
   - Expected: backend.present_pixels_cache_hits equals `2`
   - Expected: resized_pixels.len() equals `32 * 24`
   - Expected: backend.present_pixels_cache_stores equals `2`
   - Expected: backend.present_pixels_cache_hits equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reuses present pixels until framebuffer changes")
val state = static_browser_state()
val backend_result = BrowserBackend.create(64, 48, "software")
match backend_result:
    Err(e):
        expect(e).to_equal("")
    Ok(backend):
        backend.render_frame(state.tree, state)
        val first_pixels = backend.pixels_rgba_i64()
        expect(first_pixels.len()).to_equal(64 * 48)
        expect(backend.present_pixels_cache_stores).to_equal(1)
        expect(backend.present_pixels_cache_hits).to_equal(0)

        val second_pixels = backend.pixels_rgba_i64()
        expect(second_pixels.len()).to_equal(64 * 48)
        expect(backend.present_pixels_cache_stores).to_equal(1)
        expect(backend.present_pixels_cache_hits).to_equal(1)

        backend.render_cached_static_frame()
        val third_pixels = backend.pixels_rgba_i64()
        expect(third_pixels.len()).to_equal(64 * 48)
        expect(backend.present_pixels_cache_stores).to_equal(1)
        expect(backend.present_pixels_cache_hits).to_equal(2)

        backend.resize(32, 24)
        val resized_pixels = backend.pixels_rgba_i64()
        expect(resized_pixels.len()).to_equal(32 * 24)
        expect(backend.present_pixels_cache_stores).to_equal(2)
        expect(backend.present_pixels_cache_hits).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/browser_static_shell_cache_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering browser backend static shell cache.
- browser backend static shell cache

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0bdeb05df5f939e73d7a9d336a8243fbcbf996c3b2fb8ac5e047b55abc199f7e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0bdeb05df5f939e73d7a9d336a8243fbcbf996c3b2fb8ac5e047b55abc199f7e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0bdeb05df5f939e73d7a9d336a8243fbcbf996c3b2fb8ac5e047b55abc199f7e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/ui/browser_static_shell_cache_spec.spl
mirror: doc/06_spec/01_unit/app/ui/browser_static_shell_cache_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/ui/browser_static_shell_cache_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/ui/browser_static_shell_cache_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/ui/browser_static_shell_cache_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 27 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/ui/browser_static_shell_cache_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reuses full static shell html across stable frames' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ui/browser_static_shell_cache_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not claim cached static frame before first render' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ui/browser_static_shell_cache_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reuses present pixels until framebuffer changes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
