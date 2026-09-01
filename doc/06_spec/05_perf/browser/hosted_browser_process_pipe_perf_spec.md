# Hosted browser process and pipe performance

> Measures the production parent/worker request path, including request encoding,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted browser process and pipe performance

Measures the production parent/worker request path, including request encoding,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/browser/hosted_browser_process_pipe_perf_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Measures the production parent/worker request path, including request encoding,
pipe transport, worker rendering, response SBRF decoding, polling, and
compositor revision-cache routing.

## Scenarios

### hosted browser process and pipe performance

#### reuses an unchanged frame after each changed process reply

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reuses an unchanged frame after each changed process reply
   - Expected: started.ok is true
   - Expected: renderer.state equals `await-init`
   - Expected: initial.ok is true
   - Expected: initial.producer_generation equals `7`
   - Expected: initial_render.pixels.len() equals `4096`
   - Expected: mismatches equals `0`
   - Expected: raster.revision_render_count equals `1 + pairs`
   - Expected: raster.revision_reuse_count equals `pairs`
   - Expected: renderer.close() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 91 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("reuses an unchanged frame after each changed process reply")
val configured = env_get("SIMPLE_HOSTED_BROWSER_EXECUTABLE") ?? ""
val executable = if configured == "": "bin/simple" else: configured
val pairs = pipe_perf_pairs()
var renderer: HostedBrowserRendererProcess = (
    HostedBrowserRendererProcess.create(7, 64, 64)
)
val started: HostedBrowserRendererResult = renderer.start(
    executable, 10000)
expect(started.ok).to_equal(true)
expect(renderer.state).to_equal("await-init")

val initial: HostedBrowserRendererResult = renderer.render(
    "init", PIPE_PERF_HTML, 10000)
expect(initial.ok).to_equal(true)
expect(initial.producer_generation).to_equal(7)
expect(initial.composition_revision).to_be_greater_than(-1)
var raster: Engine2dCompositorBackend = (
    Engine2dCompositorBackend.create_named(64, 64, "software")
)
val initial_render: Engine2dDrawIrAdvResult = (
    raster.render_draw_ir_composition_resources_revision(
        initial.composition,
        initial.image_resources,
        initial.producer_generation,
        initial.composition_revision
    )
)
expect(initial_render.pixels.len()).to_equal(4096)

var changed_samples: [i64] = []
var unchanged_samples: [i64] = []
var mismatches: i64 = 0
var previous_revision = initial.composition_revision
var previous_pixels = initial_render.pixels
var sample: i64 = 0
while sample < pairs:
    val animation_ms = (sample + 1) * 100
    val changed_start = time_now_nanos()
    val changed: HostedBrowserRendererResult = renderer.render(
        "advance", str(animation_ms), 10000)
    val changed_render: Engine2dDrawIrAdvResult = (
        raster.render_draw_ir_composition_resources_revision(
            changed.composition,
            changed.image_resources,
            changed.producer_generation,
            changed.composition_revision
        )
    )
    changed_samples.push(time_now_nanos() - changed_start)

    val unchanged_start = time_now_nanos()
    val unchanged: HostedBrowserRendererResult = renderer.render(
        "advance", str(animation_ms), 10000)
    val unchanged_render: Engine2dDrawIrAdvResult = (
        raster.render_draw_ir_composition_resources_revision(
            unchanged.composition,
            unchanged.image_resources,
            unchanged.producer_generation,
            unchanged.composition_revision
        )
    )
    unchanged_samples.push(time_now_nanos() - unchanged_start)

    if (not changed.ok or not unchanged.ok or
        changed.producer_generation != 7 or
        unchanged.producer_generation != 7 or
        changed.composition_revision <= previous_revision or
        unchanged.composition_revision !=
            changed.composition_revision or
        changed_render.pixels == previous_pixels or
        unchanged_render.pixels != changed_render.pixels):
        mismatches = mismatches + 1
    previous_revision = changed.composition_revision
    previous_pixels = changed_render.pixels
    sample = sample + 1

val changed = pipe_perf_sorted(changed_samples)
val unchanged = pipe_perf_sorted(unchanged_samples)
val changed_p50_ns = changed[changed.len() / 2]
val unchanged_p50_ns = unchanged[unchanged.len() / 2]
print "hosted_process_pipe_perf executable={executable} pairs={pairs} changed_p50_ns={changed_p50_ns} unchanged_p50_ns={unchanged_p50_ns} ratio_x1000={unchanged_p50_ns * 1000 / changed_p50_ns} render_count={raster.revision_render_count} reuse_count={raster.revision_reuse_count} final_revision={previous_revision}"
expect(mismatches).to_equal(0)
expect(raster.revision_render_count).to_equal(1 + pairs)
expect(raster.revision_reuse_count).to_equal(pairs)
expect(changed_p50_ns).to_be_greater_than(0)
expect(unchanged_p50_ns).to_be_greater_than(0)
expect(unchanged_p50_ns).to_be_less_than(changed_p50_ns)
raster.shutdown()
expect(renderer.close()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-PERF`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `834b2ab8c470918faa021af6d0a6a5f0b14bc4b10c88cd693406116b4f86a688`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `834b2ab8c470918faa021af6d0a6a5f0b14bc4b10c88cd693406116b4f86a688`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `834b2ab8c470918faa021af6d0a6a5f0b14bc4b10c88cd693406116b4f86a688`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/05_perf/browser/hosted_browser_process_pipe_perf_spec.spl
mirror: doc/06_spec/05_perf/browser/hosted_browser_process_pipe_perf_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/browser/hosted_browser_process_pipe_perf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/browser/hosted_browser_process_pipe_perf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/browser/hosted_browser_process_pipe_perf_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/05_perf/browser/hosted_browser_process_pipe_perf_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reuses an unchanged frame after each changed process reply' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
