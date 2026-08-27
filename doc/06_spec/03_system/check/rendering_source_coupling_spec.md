# Rendering Source Coupling Guard

> Validates the diff-scoped source-coupling guard for GUI/web/2D rendering work. The guard prevents future Spark, mini, or platform-agent patches from adding raw runtime calls or backend-proof pokes in rendering-scoped files without routing through a facade or a documented compatibility helper.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rendering Source Coupling Guard

Validates the diff-scoped source-coupling guard for GUI/web/2D rendering work. The guard prevents future Spark, mini, or platform-agent patches from adding raw runtime calls or backend-proof pokes in rendering-scoped files without routing through a facade or a documented compatibility helper.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md |
| Design | doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md |
| Research | N/A |
| Source | `test/03_system/check/rendering_source_coupling_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the diff-scoped source-coupling guard for GUI/web/2D rendering work.
The guard prevents future Spark, mini, or platform-agent patches from adding raw
runtime calls or backend-proof pokes in rendering-scoped files without routing
through a facade or a documented compatibility helper.

**Plan:** doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/rendering_source_coupling_spec.spl --mode=interpreter --clean --fail-fast
```

## Acceptance

- A clean rendering diff passes.
- A new raw `rt_*` call in rendering-scoped source fails.
- RenderDoc `rt_renderdoc_*` remains allowed only in the canonical helper path.
- Obvious backend-proof assignment pokes fail.

## Scenarios

### Rendering source coupling guard

#### passes clean rendering diffs

- Create a harmless rendering-scoped diff
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a harmless rendering-scoped diff")
val command = "rm -rf build/test-rendering-source-coupling && mkdir -p build/test-rendering-source-coupling && printf '%s\\n' 'diff --git a/src/app/ui/example.spl b/src/app/ui/example.spl' '--- a/src/app/ui/example.spl' '+++ b/src/app/ui/example.spl' '+pub fn render_facade_entry() -> bool:' '+    true' > build/test-rendering-source-coupling/clean.diff && RENDERING_SOURCE_COUPLING_DIFF_FILE=build/test-rendering-source-coupling/clean.diff sh scripts/check/check-rendering-source-coupling.shs"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)
expect(stdout).to_contain("STATUS: PASS rendering-source-coupling")
```

</details>

#### rejects new raw runtime calls in rendering source

- Create a rendering-scoped diff with a raw rt_env_get call
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a rendering-scoped diff with a raw rt_env_get call")
val command = "rm -rf build/test-rendering-source-coupling && mkdir -p build/test-rendering-source-coupling && printf '%s\\n' 'diff --git a/src/app/ui/bad.spl b/src/app/ui/bad.spl' '--- a/src/app/ui/bad.spl' '+++ b/src/app/ui/bad.spl' '+val backend = rt_env_get(\"SIMPLE_GUI_BACKEND\")' > build/test-rendering-source-coupling/raw-rt.diff && RENDERING_SOURCE_COUPLING_DIFF_FILE=build/test-rendering-source-coupling/raw-rt.diff sh scripts/check/check-rendering-source-coupling.shs"
val (_stdout, stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)
expect(stderr).to_contain("rendering_source_coupling_raw_rt=src/app/ui/bad.spl")
expect(stderr).to_contain("STATUS: FAIL rendering-source-coupling")
```

</details>

#### keeps RenderDoc runtime helper calls isolated to the canonical helper

- Create an allowed RenderDoc helper diff
   - Expected: allowed_code equals `0`
- Create a disallowed RenderDoc runtime call outside the helper
   - Expected: blocked_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create an allowed RenderDoc helper diff")
val allowed = "rm -rf build/test-rendering-source-coupling && mkdir -p build/test-rendering-source-coupling && printf '%s\\n' 'diff --git a/scripts/tool/renderdoc-evidence.shs b/scripts/tool/renderdoc-evidence.shs' '--- a/scripts/tool/renderdoc-evidence.shs' '+++ b/scripts/tool/renderdoc-evidence.shs' '+simple_code=\"rt_renderdoc_begin_capture()\"' > build/test-rendering-source-coupling/renderdoc-helper.diff && RENDERING_SOURCE_COUPLING_DIFF_FILE=build/test-rendering-source-coupling/renderdoc-helper.diff sh scripts/check/check-rendering-source-coupling.shs"
val (allowed_stdout, _allowed_stderr, allowed_code) = process_run("/bin/sh", ["-c", allowed])
expect(allowed_code).to_equal(0)
expect(allowed_stdout).to_contain("STATUS: PASS rendering-source-coupling")

step("Create a disallowed RenderDoc runtime call outside the helper")
val blocked = "printf '%s\\n' 'diff --git a/src/app/ui/bad_renderdoc.spl b/src/app/ui/bad_renderdoc.spl' '--- a/src/app/ui/bad_renderdoc.spl' '+++ b/src/app/ui/bad_renderdoc.spl' '+rt_renderdoc_begin_capture()' > build/test-rendering-source-coupling/renderdoc-bad.diff && RENDERING_SOURCE_COUPLING_DIFF_FILE=build/test-rendering-source-coupling/renderdoc-bad.diff sh scripts/check/check-rendering-source-coupling.shs"
val (_blocked_stdout, blocked_stderr, blocked_code) = process_run("/bin/sh", ["-c", blocked])
expect(blocked_code).to_equal(1)
expect(blocked_stderr).to_contain("rendering_source_coupling_raw_rt=src/app/ui/bad_renderdoc.spl")
```

</details>

#### allows raw runtime calls only inside the canonical GPU provider fixtures

- Create an allowed native provider-fixture diff
   - Expected: allowed_code equals `0`
- Copy the same raw call into a noncanonical GPU checker
   - Expected: blocked_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create an allowed native provider-fixture diff")
val allowed = "rm -rf build/test-rendering-source-coupling && mkdir -p build/test-rendering-source-coupling && printf '%s\\n' 'diff --git a/scripts/check/check-gpu-provider-dynload-registry.shs b/scripts/check/check-gpu-provider-dynload-registry.shs' '--- a/scripts/check/check-gpu-provider-dynload-registry.shs' '+++ b/scripts/check/check-gpu-provider-dynload-registry.shs' '+int64_t rt_gpu_provider_loaded(int64_t);' > build/test-rendering-source-coupling/gpu-provider-fixture.diff && RENDERING_SOURCE_COUPLING_DIFF_FILE=build/test-rendering-source-coupling/gpu-provider-fixture.diff sh scripts/check/check-rendering-source-coupling.shs"
val (allowed_stdout, _allowed_stderr, allowed_code) = process_run("/bin/sh", ["-c", allowed])
expect(allowed_code).to_equal(0)
expect(allowed_stdout).to_contain("STATUS: PASS rendering-source-coupling")

step("Copy the same raw call into a noncanonical GPU checker")
val blocked = "printf '%s\\n' 'diff --git a/scripts/check/check-gpu-provider-copy.shs b/scripts/check/check-gpu-provider-copy.shs' '--- a/scripts/check/check-gpu-provider-copy.shs' '+++ b/scripts/check/check-gpu-provider-copy.shs' '+int64_t rt_gpu_provider_loaded(int64_t);' > build/test-rendering-source-coupling/gpu-provider-copy.diff && RENDERING_SOURCE_COUPLING_DIFF_FILE=build/test-rendering-source-coupling/gpu-provider-copy.diff sh scripts/check/check-rendering-source-coupling.shs"
val (_blocked_stdout, blocked_stderr, blocked_code) = process_run("/bin/sh", ["-c", blocked])
expect(blocked_code).to_equal(1)
expect(blocked_stderr).to_contain("rendering_source_coupling_raw_rt=scripts/check/check-gpu-provider-copy.shs")
```

</details>

#### rejects backend proof assignment pokes

- Create a rendering-scoped diff that forces a backend proof pass
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a rendering-scoped diff that forces a backend proof pass")
val command = "rm -rf build/test-rendering-source-coupling && mkdir -p build/test-rendering-source-coupling && printf '%s\\n' 'diff --git a/src/lib/gc_async_mut/ui/web_render_pixel_backend.spl b/src/lib/gc_async_mut/ui/web_render_pixel_backend.spl' '--- a/src/lib/gc_async_mut/ui/web_render_pixel_backend.spl' '+++ b/src/lib/gc_async_mut/ui/web_render_pixel_backend.spl' '+artifact.backend_status = \"pass\"' > build/test-rendering-source-coupling/backend-poke.diff && RENDERING_SOURCE_COUPLING_DIFF_FILE=build/test-rendering-source-coupling/backend-poke.diff sh scripts/check/check-rendering-source-coupling.shs"
val (_stdout, stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)
expect(stderr).to_contain("rendering_source_coupling_backend_poke=src/lib/gc_async_mut/ui/web_render_pixel_backend.spl")
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


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md`
- **Design:** `doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `23d680d0caa924b3a6f7797a1c9db25fd663cdb83683c6dae989664e9673380b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `23d680d0caa924b3a6f7797a1c9db25fd663cdb83683c6dae989664e9673380b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `23d680d0caa924b3a6f7797a1c9db25fd663cdb83683c6dae989664e9673380b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **78/100**; blockers: **0**.

SSpec documentization score: 78/100
source: test/03_system/check/rendering_source_coupling_spec.spl
mirror: doc/06_spec/03_system/check/rendering_source_coupling_spec.md (current)
findings: 10 blockers: 0
  narrative=80 structure=100 oracle=70
  traceability=80 evidence=70 coverage=100 maintainability=45
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/rendering_source_coupling_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/rendering_source_coupling_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/rendering_source_coupling_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/03_system/check/rendering_source_coupling_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/03_system/check/rendering_source_coupling_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/03_system/check/rendering_source_coupling_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/rendering_source_coupling_spec.spl:1:1: warning SSDOC-TRC-001 [traceability] (-20): no implemented requirement identity
  why: Stable requirement identity connects intent, implementation, and evidence.
  improve: Bind scenarios to stable selected REQ identities.
test/03_system/check/rendering_source_coupling_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes clean rendering diffs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/rendering_source_coupling_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects new raw runtime calls in rendering source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/rendering_source_coupling_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps RenderDoc runtime helper calls isolated to the canonical helper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
