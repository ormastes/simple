# RenderDoc Simple gate

> Validates the fail-closed gate for Simple in-application Vulkan RenderDoc evidence. The local host may not have RenderDoc installed, but the gate must record a deterministic non-pass state and accept only Simple `vulkan-engine2d` `.rdc` evidence.

<!-- sdn-diagram:id=renderdoc_simple_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=renderdoc_simple_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

renderdoc_simple_gate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=renderdoc_simple_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RenderDoc Simple gate

Validates the fail-closed gate for Simple in-application Vulkan RenderDoc evidence. The local host may not have RenderDoc installed, but the gate must record a deterministic non-pass state and accept only Simple `vulkan-engine2d` `.rdc` evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-25.md |
| Source | `test/03_system/check/renderdoc_simple_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the fail-closed gate for Simple in-application Vulkan RenderDoc
evidence. The local host may not have RenderDoc installed, but the gate must
record a deterministic non-pass state and accept only Simple `vulkan-engine2d`
`.rdc` evidence.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-25.md
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
RDOC_SIMPLE_EVIDENCE_ENV=build/renderdoc/canonical-probe/simple/evidence.env \
BUILD_DIR=build/test-renderdoc-simple-gate \
REPORT_PATH=build/test-renderdoc-simple-gate/report.md \
sh scripts/check/check-renderdoc-simple-gate.shs || true
```

## Acceptance

- Missing or failed Simple RenderDoc evidence produces typed non-pass gate
  evidence.
- Passing gate evidence requires Simple backend, `vulkan-engine2d` scene, pass
  status, `RDOC` magic, an existing `.rdc` file, and the canonical
  `src/app/test/renderdoc_vulkan_capture.spl` probe program.
- Passing gate evidence also requires the probe log-derived runtime backend to
  be `vulkan`, RenderDoc availability/start markers, at least one recorded
  capture, and a positive pixel count.
- The `.rdc` capture file must be a regular file, not a symlink to substituted
  or stale evidence.

## Scenarios

### RenderDoc Simple gate

#### writes typed non-pass evidence for missing or failed Simple capture

<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-simple-gate && RDOC_SIMPLE_EVIDENCE_ENV=build/renderdoc/canonical-probe/simple/evidence.env BUILD_DIR=build/test-renderdoc-simple-gate REPORT_PATH=build/test-renderdoc-simple-gate/report.md sh scripts/check/check-renderdoc-simple-gate.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-renderdoc-simple-gate/evidence.env")
expect(evidence).to_contain("rdoc_simple_gate_status=")
expect(evidence).to_contain("rdoc_simple_gate_reason=")
expect(evidence).to_contain("rdoc_simple_gate_source_env=")
expect(evidence).to_contain("rdoc_simple_gate_required_backend=simple")
expect(evidence).to_contain("rdoc_simple_gate_required_scene=vulkan-engine2d")
expect(evidence).to_contain("rdoc_simple_gate_required_program=src/app/test/renderdoc_vulkan_capture.spl")
expect(evidence).to_contain("rdoc_simple_gate_required_status=pass")
expect(evidence).to_contain("rdoc_simple_gate_required_magic=RDOC")
expect(evidence).to_contain("rdoc_simple_gate_required_runtime_backend=vulkan")
expect(evidence).to_contain("rdoc_simple_gate_required_renderdoc_available=1")
expect(evidence).to_contain("rdoc_simple_gate_required_renderdoc_start=1")
expect(evidence).to_contain("rdoc_simple_gate_required_renderdoc_end_recorded=1")
expect(evidence).to_contain("rdoc_simple_gate_required_num_captures_min=1")
expect(evidence).to_contain("rdoc_simple_gate_required_pixel_count_min=1")
expect(evidence).to_contain("rdoc_simple_gate_capture_file_magic=")
expect(evidence).to_contain("rdoc_simple_gate_runtime_backend=")
expect(evidence).to_contain("rdoc_simple_gate_renderdoc_num_captures=")
expect(evidence).to_contain("rdoc_simple_gate_pixel_count=")
expect(evidence).to_contain("rdoc_simple_gate_runtime_metadata_status=")
expect(evidence).to_contain("rdoc_simple_gate_missing_runtime_metadata=")

val status = _value_of(evidence, "rdoc_simple_gate_status")
val reason = _value_of(evidence, "rdoc_simple_gate_reason")
val backend = _value_of(evidence, "rdoc_simple_gate_backend")
val scene = _value_of(evidence, "rdoc_simple_gate_scene")
val program = _value_of(evidence, "rdoc_simple_gate_program")
val capture_status = _value_of(evidence, "rdoc_simple_gate_capture_status")
val magic = _value_of(evidence, "rdoc_simple_gate_capture_magic")
val runtime_backend = _value_of(evidence, "rdoc_simple_gate_runtime_backend")

if status == "pass":
    expect(backend).to_equal("simple")
    expect(scene).to_equal("vulkan-engine2d")
    expect(program).to_contain("src/app/test/renderdoc_vulkan_capture.spl")
    expect(capture_status).to_equal("pass")
    expect(magic).to_equal("RDOC")
    expect(runtime_backend).to_equal("vulkan")
else:
    expect(reason.len()).to_be_greater_than(0)
```

</details>

#### passes with controlled Simple Vulkan RDOC evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-simple-gate-pass && mkdir -p build/test-renderdoc-simple-gate-pass/source && printf 'RDOCsynthetic simple capture\\n' > build/test-renderdoc-simple-gate-pass/source/simple.rdc && printf 'rdoc_backend=simple\\nrdoc_scene=vulkan-engine2d\\nrdoc_program=src/app/test/renderdoc_vulkan_capture.spl\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-renderdoc-simple-gate-pass/source/simple.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_simple_runtime_backend=vulkan\\nrdoc_simple_renderdoc_available=1\\nrdoc_simple_renderdoc_start=1\\nrdoc_simple_renderdoc_end=1\\nrdoc_simple_renderdoc_num_captures=1\\nrdoc_simple_pixel_count=3072\\n' > build/test-renderdoc-simple-gate-pass/source/evidence.env && RDOC_SIMPLE_EVIDENCE_ENV=build/test-renderdoc-simple-gate-pass/source/evidence.env BUILD_DIR=build/test-renderdoc-simple-gate-pass/out REPORT_PATH=build/test-renderdoc-simple-gate-pass/report.md sh scripts/check/check-renderdoc-simple-gate.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-renderdoc-simple-gate-pass/out/evidence.env")
expect(evidence).to_contain("rdoc_simple_gate_status=pass")
expect(evidence).to_contain("rdoc_simple_gate_reason=pass")
expect(evidence).to_contain("rdoc_simple_gate_backend=simple")
expect(evidence).to_contain("rdoc_simple_gate_scene=vulkan-engine2d")
expect(evidence).to_contain("rdoc_simple_gate_program=src/app/test/renderdoc_vulkan_capture.spl")
expect(evidence).to_contain("rdoc_simple_gate_capture_magic=RDOC")
expect(evidence).to_contain("rdoc_simple_gate_capture_file_status=pass")
expect(evidence).to_contain("rdoc_simple_gate_capture_file_magic=RDOC")
expect(evidence).to_contain("rdoc_simple_gate_runtime_backend=vulkan")
expect(evidence).to_contain("rdoc_simple_gate_renderdoc_available=1")
expect(evidence).to_contain("rdoc_simple_gate_renderdoc_start=1")
expect(evidence).to_contain("rdoc_simple_gate_renderdoc_end=1")
expect(evidence).to_contain("rdoc_simple_gate_renderdoc_num_captures=1")
expect(evidence).to_contain("rdoc_simple_gate_pixel_count=3072")
expect(evidence).to_contain("rdoc_simple_gate_runtime_metadata_status=pass")
expect(evidence).to_contain("rdoc_simple_gate_missing_runtime_metadata=")
```

</details>

#### rejects symlinked Simple RDOC artifacts before reading magic

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-renderdoc-simple-gate-symlink-artifact"
val command = "rm -rf " + root + " && mkdir -p " + root + "/source && " +
    "printf 'RDOCsynthetic simple capture\\n' > " + root + "/source/simple-real.rdc && ln -s simple-real.rdc " + root + "/source/simple.rdc && " +
    "printf 'rdoc_backend=simple\\nrdoc_scene=vulkan-engine2d\\nrdoc_program=src/app/test/renderdoc_vulkan_capture.spl\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=" + root + "/source/simple.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_simple_runtime_backend=vulkan\\nrdoc_simple_renderdoc_available=1\\nrdoc_simple_renderdoc_start=1\\nrdoc_simple_renderdoc_end=1\\nrdoc_simple_renderdoc_num_captures=1\\nrdoc_simple_pixel_count=3072\\n' > " + root + "/source/evidence.env && " +
    "RDOC_SIMPLE_EVIDENCE_ENV=" + root + "/source/evidence.env BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-renderdoc-simple-gate.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("rdoc_simple_gate_status=fail")
expect(evidence).to_contain("rdoc_simple_gate_reason=rdc-file-symlink")
expect(evidence).to_contain("rdoc_simple_gate_capture_file_status=symlink")
expect(evidence).to_contain("rdoc_simple_gate_capture_file_magic=")
```

</details>

#### reports every missing Simple runtime metadata field for partial RDOC evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-simple-gate-missing-runtime-metadata && mkdir -p build/test-renderdoc-simple-gate-missing-runtime-metadata/source && printf 'RDOCsynthetic simple capture\\n' > build/test-renderdoc-simple-gate-missing-runtime-metadata/source/simple.rdc && printf 'rdoc_backend=simple\\nrdoc_scene=vulkan-engine2d\\nrdoc_program=src/app/test/renderdoc_vulkan_capture.spl\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-renderdoc-simple-gate-missing-runtime-metadata/source/simple.rdc\\nrdoc_capture_magic=RDOC\\n' > build/test-renderdoc-simple-gate-missing-runtime-metadata/source/evidence.env && RDOC_SIMPLE_EVIDENCE_ENV=build/test-renderdoc-simple-gate-missing-runtime-metadata/source/evidence.env BUILD_DIR=build/test-renderdoc-simple-gate-missing-runtime-metadata/out REPORT_PATH=build/test-renderdoc-simple-gate-missing-runtime-metadata/report.md sh scripts/check/check-renderdoc-simple-gate.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-renderdoc-simple-gate-missing-runtime-metadata/out/evidence.env")
expect(evidence).to_contain("rdoc_simple_gate_status=fail")
expect(evidence).to_contain("rdoc_simple_gate_reason=missing-vulkan-runtime-backend")
expect(evidence).to_contain("rdoc_simple_gate_capture_file_magic=RDOC")
expect(evidence).to_contain("rdoc_simple_gate_runtime_metadata_status=missing")
expect(evidence).to_contain("rdoc_simple_gate_missing_runtime_metadata=rdoc_simple_runtime_backend,rdoc_simple_renderdoc_available,rdoc_simple_renderdoc_start,rdoc_simple_renderdoc_end,rdoc_simple_renderdoc_num_captures,rdoc_simple_pixel_count")
```

</details>

#### rejects Simple captures whose file header is not RDOC

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-simple-gate-bad-file-magic && mkdir -p build/test-renderdoc-simple-gate-bad-file-magic/source && printf 'NOPEsynthetic simple capture\\n' > build/test-renderdoc-simple-gate-bad-file-magic/source/simple.rdc && printf 'rdoc_backend=simple\\nrdoc_scene=vulkan-engine2d\\nrdoc_program=src/app/test/renderdoc_vulkan_capture.spl\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-renderdoc-simple-gate-bad-file-magic/source/simple.rdc\\nrdoc_capture_magic=RDOC\\n' > build/test-renderdoc-simple-gate-bad-file-magic/source/evidence.env && RDOC_SIMPLE_EVIDENCE_ENV=build/test-renderdoc-simple-gate-bad-file-magic/source/evidence.env BUILD_DIR=build/test-renderdoc-simple-gate-bad-file-magic/out REPORT_PATH=build/test-renderdoc-simple-gate-bad-file-magic/report.md sh scripts/check/check-renderdoc-simple-gate.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-renderdoc-simple-gate-bad-file-magic/out/evidence.env")
expect(evidence).to_contain("rdoc_simple_gate_status=fail")
expect(evidence).to_contain("rdoc_simple_gate_reason=missing-rdoc-file-magic")
expect(evidence).to_contain("rdoc_simple_gate_capture_magic=RDOC")
expect(evidence).to_contain("rdoc_simple_gate_capture_file_magic=NOPE")
```

</details>

#### rejects Simple captures from the wrong probe program

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-simple-gate-wrong-program && mkdir -p build/test-renderdoc-simple-gate-wrong-program/source && printf 'RDOCsynthetic simple capture\\n' > build/test-renderdoc-simple-gate-wrong-program/source/simple.rdc && printf 'rdoc_backend=simple\\nrdoc_scene=vulkan-engine2d\\nrdoc_program=src/app/test/other_capture.spl\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-renderdoc-simple-gate-wrong-program/source/simple.rdc\\nrdoc_capture_magic=RDOC\\n' > build/test-renderdoc-simple-gate-wrong-program/source/evidence.env && RDOC_SIMPLE_EVIDENCE_ENV=build/test-renderdoc-simple-gate-wrong-program/source/evidence.env BUILD_DIR=build/test-renderdoc-simple-gate-wrong-program/out REPORT_PATH=build/test-renderdoc-simple-gate-wrong-program/report.md sh scripts/check/check-renderdoc-simple-gate.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-renderdoc-simple-gate-wrong-program/out/evidence.env")
expect(evidence).to_contain("rdoc_simple_gate_status=fail")
expect(evidence).to_contain("rdoc_simple_gate_reason=unexpected-program")
```

</details>

#### rejects Simple captures without Vulkan runtime backend evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-simple-gate-runtime-backend && mkdir -p build/test-renderdoc-simple-gate-runtime-backend/source && printf 'RDOCsynthetic simple capture\\n' > build/test-renderdoc-simple-gate-runtime-backend/source/simple.rdc && printf 'rdoc_backend=simple\\nrdoc_scene=vulkan-engine2d\\nrdoc_program=src/app/test/renderdoc_vulkan_capture.spl\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-renderdoc-simple-gate-runtime-backend/source/simple.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_simple_runtime_backend=software\\nrdoc_simple_renderdoc_available=1\\nrdoc_simple_renderdoc_start=1\\nrdoc_simple_renderdoc_end=1\\nrdoc_simple_renderdoc_num_captures=1\\nrdoc_simple_pixel_count=3072\\n' > build/test-renderdoc-simple-gate-runtime-backend/source/evidence.env && RDOC_SIMPLE_EVIDENCE_ENV=build/test-renderdoc-simple-gate-runtime-backend/source/evidence.env BUILD_DIR=build/test-renderdoc-simple-gate-runtime-backend/out REPORT_PATH=build/test-renderdoc-simple-gate-runtime-backend/report.md sh scripts/check/check-renderdoc-simple-gate.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-renderdoc-simple-gate-runtime-backend/out/evidence.env")
expect(evidence).to_contain("rdoc_simple_gate_status=fail")
expect(evidence).to_contain("rdoc_simple_gate_reason=unexpected-runtime-backend")
expect(evidence).to_contain("rdoc_simple_gate_runtime_backend=software")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md](doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)
- **Research:** [doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-25.md](doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-25.md)


</details>
