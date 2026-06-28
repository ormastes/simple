# Electron live smoke proof wrapper

> Checks that the Electron live smoke shell wrapper preserves normalized diagnostics and writes a report when the live Electron dependency path is unavailable before a browser process starts.

<!-- sdn-diagram:id=electron_live_smoke_proof_validator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=electron_live_smoke_proof_validator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

electron_live_smoke_proof_validator_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=electron_live_smoke_proof_validator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Electron live smoke proof wrapper

Checks that the Electron live smoke shell wrapper preserves normalized diagnostics and writes a report when the live Electron dependency path is unavailable before a browser process starts.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/production_gui_web_renderer_parity_hardening.md |
| Plan | doc/03_plan/agent_tasks/gui_web_mobile_renderer_hardening_resume_2026-06-28.md |
| Design | doc/05_design/ui/misc/production_gui_web_renderer_parity_hardening.md |
| Research | N/A |
| Source | `test/03_system/check/electron_live_smoke_proof_validator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Checks that the Electron live smoke shell wrapper preserves normalized
diagnostics and writes a report when the live Electron dependency path is
unavailable before a browser process starts.

**Plan:** doc/03_plan/agent_tasks/gui_web_mobile_renderer_hardening_resume_2026-06-28.md
**Requirements:** doc/02_requirements/feature/production_gui_web_renderer_parity_hardening.md
**Research:** N/A
**Design:** doc/05_design/ui/misc/production_gui_web_renderer_parity_hardening.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/electron_live_smoke_proof_validator_spec.spl --mode=interpreter --clean --fail-fast
```

## Acceptance

- Early unavailable exits keep the normalized `electron_live_smoke_*` evidence
  rows.
- Early unavailable exits write a markdown report beside the proof path.
- The wrapper remains wired to the JSON validator and report writer.

## Scenarios

### Electron live smoke proof wrapper

#### keeps report diagnostics on early dependency failures

<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-live-smoke-wrapper-early-fail"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "PATH=/bin:/usr/bin SIMPLE_ELECTRON_PROOF_PATH=" + root + "/proof.json sh scripts/check/check-electron-live-smoke.shs > " + root + "/stdout.env 2> " + root + "/stderr.log; exit 0"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/stdout.env")
expect(evidence).to_contain("electron_live_smoke=unavailable")
expect(evidence).to_contain("error=missing_command:node")
expect(evidence).to_contain("electron_live_smoke_validation_status=unavailable")
expect(evidence).to_contain("electron_live_smoke_validation_reason=missing_command:node")
expect(evidence).to_contain("electron_live_smoke_target=electron")
expect(evidence).to_contain("electron_live_smoke_proof_source=src/app/ui.electron/bridge.js:electronLiveSmokeProofScript")
expect(evidence).to_contain("electron_live_smoke_screenshot_path=" + root + "/proof.json.png")
expect(evidence).to_contain("electron_live_smoke_blur_or_tolerance_used=")

val report = file_read(root + "/proof.json.report.md")
expect(report).to_contain("# Electron Live Smoke")
expect(report).to_contain("- status: unavailable")
expect(report).to_contain("- reason: missing_command:node")
expect(report).to_contain("- proof: " + root + "/proof.json")
expect(report).to_contain("- validation: " + root + "/proof.json.validation.env")
expect(report).to_contain("- browser: engine=chromium electron= chrome=")
expect(report).to_contain("- performance/animation: performance_now= delta_ms= animation= frames= css=")
expect(report).to_contain("- event dispatch: available= count= type= detail= error= input_to_paint_ms=")
expect(report).to_contain("- screenshot artifact: path=" + root + "/proof.json.png file=not-run artifact=not-run")
expect(report).to_contain("- blur_or_tolerance_used:")
```

</details>

#### keeps the wrapper wired to the validator and report writer

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wrapper = file_read("scripts/check/check-electron-live-smoke.shs")
expect(wrapper).to_contain("validate-electron-live-smoke-proof.js")
expect(wrapper).to_contain("REPORT_PATH=\"${SIMPLE_ELECTRON_REPORT_PATH:-${PROOF_PATH}.report.md}\"")
expect(wrapper).to_contain("write_report()")
expect(wrapper).to_contain("write_report pass pass")
expect(wrapper).to_contain("write_report unavailable \"missing_command:$required\"")
expect(wrapper).to_contain("- performance/animation:")
expect(wrapper).to_contain("- event dispatch:")
expect(wrapper).to_contain("- screenshot artifact:")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/production_gui_web_renderer_parity_hardening.md](doc/02_requirements/feature/production_gui_web_renderer_parity_hardening.md)
- **Plan:** [doc/03_plan/agent_tasks/gui_web_mobile_renderer_hardening_resume_2026-06-28.md](doc/03_plan/agent_tasks/gui_web_mobile_renderer_hardening_resume_2026-06-28.md)
- **Design:** [doc/05_design/ui/misc/production_gui_web_renderer_parity_hardening.md](doc/05_design/ui/misc/production_gui_web_renderer_parity_hardening.md)


</details>
