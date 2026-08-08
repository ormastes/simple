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
| 11 | 11 | 0 | 0 |

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
| Updated | 2026-07-27 |
| Generator | Manual sync after bounded runtime/docgen limits |

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
- The producer's lowercase SHA-256 must equal hashes recomputed from the
  regular `.rdc` file before and after replay inspection.

## Scenarios

### RenderDoc Simple gate

#### times out the real replay gate path and discards stale replay evidence

The replay inspector runs through portable `timeout`/`gtimeout` resolution with
the bounded `RDOC_SIMPLE_REPLAY_TIMEOUT_SECS` setting. Exit 124 or 137 is
retained in `rdoc_simple_gate_replay_command_exit`, marks
`rdoc_simple_gate_replay_timed_out=1`, and fails with the typed
`simple-replay-inspector-timeout` reason. A host-independent classifier
self-test covers timeout and ordinary nonzero exits without launching Simple or
RenderDoc.

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-renderdoc-simple-gate-timeout"
val hash = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
val command = "rm -rf " + root + " && mkdir -p " + root + "/source " + root + "/renderdoc/bin " + root + "/out/replay && " +
    "printf 'RDOCsynthetic capture\\n' > " + root + "/source/simple_gui_app-frame-7_0.rdc && " +
    "printf '#!/bin/sh\\nexit 0\\n' > " + root + "/renderdoc/bin/renderdoccmd && " +
    "printf '#!/bin/sh\\nsleep 5\\n' > " + root + "/fake-simple && " +
    "chmod +x " + root + "/renderdoc/bin/renderdoccmd " + root + "/fake-simple && " +
    "printf 'rdoc_simple_replay_status=pass\\nrdoc_simple_replay_reason=stale-pass\\nstale_replay_marker=present\\n' > " + root + "/out/replay/evidence.env && " +
    ". scripts/lib/renderdoc-evidence-common.shs && capture=" + root + "/source/simple_gui_app-frame-7_0.rdc && digest=$(rdoc_sha256_file \"$capture\") && " +
    "printf 'rdoc_backend=simple\\nrdoc_scene=vulkan-engine2d\\nrdoc_program=src/app/test/renderdoc_vulkan_capture.spl\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=%s\\nrdoc_capture_magic=RDOC\\nrdoc_capture_sha256=%s\\nrdoc_renderdoc_home=" + root + "/renderdoc\\nrdoc_simple_renderdoc_capture_template=" + root + "/source/simple_gui_app-frame-7\\nrdoc_simple_renderdoc_capture_template_set=1\\nrdoc_simple_runtime_backend=vulkan\\nrdoc_simple_renderdoc_available=1\\nrdoc_simple_renderdoc_start=1\\nrdoc_simple_renderdoc_capturing_before_end=1\\nrdoc_simple_renderdoc_end=1\\nrdoc_simple_renderdoc_num_captures=1\\nrdoc_simple_pixel_count=1\\nrdoc_simple_renderdoc_device=1\\nrdoc_simple_record_valid=1\\nrdoc_simple_semantic_hash=" + hash + "\\nrdoc_simple_record_hash=" + hash + "\\nrdoc_simple_pixel_hash=" + hash + "\\nrdoc_simple_owner_frame_id=frame-7\\nrdoc_simple_capture_frame_id=frame-7\\n' \"$capture\" \"$digest\" > " + root + "/source/evidence.env && " +
    "RDOC_SIMPLE_REPLAY_TIMEOUT_SECS=1 RDOC_SIMPLE_EVIDENCE_ENV=" + root + "/source/evidence.env RDOC_REPLAY_SIMPLE_BIN=" + root + "/fake-simple BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-renderdoc-simple-gate.shs >/dev/null"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/out/evidence.env")
expect(_value_of(evidence, "rdoc_simple_gate_reason")).to_equal("simple-replay-inspector-timeout")
val replay_exit = _value_of(evidence, "rdoc_simple_gate_replay_command_exit")
expect(replay_exit == "124" or replay_exit == "137").to_be(true)
expect(_value_of(evidence, "rdoc_simple_gate_replay_timed_out")).to_equal("1")
expect(_value_of(evidence, "rdoc_simple_gate_replay_timeout_seconds")).to_equal("1")
val replay_evidence = file_read(root + "/out/replay/evidence.env")
expect(replay_evidence.contains("stale_replay_marker=present")).to_be(false)
```

</details>

#### rejects duplicate source and replay evidence keys at the shared parser boundary

The gate's host-independent parser self-test requires one nonempty value for a
key and rejects conflicting duplicate rows. The source contract also requires
typed `duplicate-source-evidence-key` and `duplicate-replay-evidence-key`
failures; last-write-wins `tail -n 1` parsing is forbidden. Runnable source:
`test/03_system/check/renderdoc_simple_gate_spec.spl`.

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "RDOC_SIMPLE_GATE_PARSER_SELF_TEST=1 sh scripts/check/check-renderdoc-simple-gate.shs"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)
expect(stdout).to_contain("rdoc_simple_gate_parser_self_test_status=pass")
val gate = file_read("scripts/check/check-renderdoc-simple-gate.shs")
expect(gate.contains("tail -n 1")).to_be(false)
expect(gate).to_contain("duplicate-source-evidence-key")
expect(gate).to_contain("duplicate-replay-evidence-key")
```

</details>

#### writes typed non-pass evidence for missing or failed Simple capture

<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
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
expect(evidence).to_contain("rdoc_simple_gate_required_capture_sha256=lower-hex-64-match")
expect(evidence).to_contain("rdoc_simple_gate_required_runtime_backend=vulkan")
expect(evidence).to_contain("rdoc_simple_gate_required_renderdoc_available=1")
expect(evidence).to_contain("rdoc_simple_gate_required_renderdoc_start=1")
expect(evidence).to_contain("rdoc_simple_gate_required_renderdoc_end_recorded=1")
expect(evidence).to_contain("rdoc_simple_gate_required_num_captures_min=1")
expect(evidence).to_contain("rdoc_simple_gate_required_pixel_count_min=1")
expect(evidence).to_contain("rdoc_simple_gate_capture_file_magic=")
expect(evidence).to_contain("rdoc_simple_gate_capture_identity_status=")
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

#### rejects a synthetic magic file even with plausible producer metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hash_a = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
val hash_b = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
val hash_c = "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
val command = "rm -rf build/test-renderdoc-simple-gate-pass && mkdir -p build/test-renderdoc-simple-gate-pass/source && printf 'RDOCsynthetic simple capture\\n' > build/test-renderdoc-simple-gate-pass/source/simple_gui_app-frame-7_0.rdc && . scripts/lib/renderdoc-evidence-common.shs && capture_sha=$(rdoc_sha256_file build/test-renderdoc-simple-gate-pass/source/simple_gui_app-frame-7_0.rdc) && printf 'rdoc_backend=simple\\nrdoc_scene=vulkan-engine2d\\nrdoc_program=src/app/test/renderdoc_vulkan_capture.spl\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-renderdoc-simple-gate-pass/source/simple_gui_app-frame-7_0.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_capture_sha256=%s\\nrdoc_renderdoc_home=build/missing-renderdoc\\nrdoc_simple_renderdoc_capture_template=build/test-renderdoc-simple-gate-pass/source/simple_gui_app-frame-7\\nrdoc_simple_renderdoc_capture_template_set=1\\nrdoc_simple_runtime_backend=vulkan\\nrdoc_simple_renderdoc_available=1\\nrdoc_simple_renderdoc_start=1\\nrdoc_simple_renderdoc_capturing_before_end=1\\nrdoc_simple_renderdoc_end=1\\nrdoc_simple_renderdoc_num_captures=1\\nrdoc_simple_pixel_count=3072\\nrdoc_simple_renderdoc_device=41\\nrdoc_simple_record_valid=1\\nrdoc_simple_semantic_hash=" + hash_a + "\\nrdoc_simple_record_hash=" + hash_b + "\\nrdoc_simple_pixel_hash=" + hash_c + "\\nrdoc_simple_owner_frame_id=frame-7\\nrdoc_simple_capture_frame_id=frame-7\\n' \"$capture_sha\" > build/test-renderdoc-simple-gate-pass/source/evidence.env && RDOC_SIMPLE_EVIDENCE_ENV=build/test-renderdoc-simple-gate-pass/source/evidence.env BUILD_DIR=build/test-renderdoc-simple-gate-pass/out REPORT_PATH=build/test-renderdoc-simple-gate-pass/report.md sh scripts/check/check-renderdoc-simple-gate.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read("build/test-renderdoc-simple-gate-pass/out/evidence.env")
expect(evidence).to_contain("rdoc_simple_gate_status=fail")
expect(evidence).to_contain("rdoc_simple_gate_reason=renderdoccmd-missing")
expect(evidence).to_contain("rdoc_simple_gate_backend=simple")
expect(evidence).to_contain("rdoc_simple_gate_scene=vulkan-engine2d")
expect(evidence).to_contain("rdoc_simple_gate_program=src/app/test/renderdoc_vulkan_capture.spl")
expect(evidence).to_contain("rdoc_simple_gate_capture_magic=RDOC")
expect(evidence).to_contain("rdoc_simple_gate_capture_file_status=pass")
expect(evidence).to_contain("rdoc_simple_gate_capture_file_magic=RDOC")
expect(evidence).to_contain("rdoc_simple_gate_capture_hash_status=pass")
expect(evidence).to_contain("rdoc_simple_gate_runtime_backend=vulkan")
expect(evidence).to_contain("rdoc_simple_gate_renderdoc_available=1")
expect(evidence).to_contain("rdoc_simple_gate_renderdoc_start=1")
expect(evidence).to_contain("rdoc_simple_gate_renderdoc_end=1")
expect(evidence).to_contain("rdoc_simple_gate_renderdoc_num_captures=1")
expect(evidence).to_contain("rdoc_simple_gate_pixel_count=3072")
expect(evidence).to_contain("rdoc_simple_gate_runtime_metadata_status=pass")
expect(evidence).to_contain("rdoc_simple_gate_missing_runtime_metadata=")
expect(evidence).to_contain("rdoc_simple_gate_replay_status=fail")
expect(evidence).to_contain("rdoc_simple_gate_replay_reason=renderdoccmd-missing")
```

</details>

#### rejects equal echoed IDs when the captured path names another frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-renderdoc-simple-gate-frame-path"
val hash = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
val command = "rm -rf " + root + " && mkdir -p " + root + "/source && printf 'RDOCsynthetic simple capture\\n' > " + root + "/source/simple_gui_app-frame-8_0.rdc && printf 'rdoc_backend=simple\\nrdoc_scene=vulkan-engine2d\\nrdoc_program=src/app/test/renderdoc_vulkan_capture.spl\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=" + root + "/source/simple_gui_app-frame-8_0.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_renderdoc_home=build/missing-renderdoc\\nrdoc_simple_renderdoc_capture_template=" + root + "/source/simple_gui_app-frame-8\\nrdoc_simple_renderdoc_capture_template_set=1\\nrdoc_simple_runtime_backend=vulkan\\nrdoc_simple_renderdoc_available=1\\nrdoc_simple_renderdoc_start=1\\nrdoc_simple_renderdoc_capturing_before_end=1\\nrdoc_simple_renderdoc_end=1\\nrdoc_simple_renderdoc_num_captures=1\\nrdoc_simple_pixel_count=3072\\nrdoc_simple_renderdoc_device=41\\nrdoc_simple_record_valid=1\\nrdoc_simple_semantic_hash=" + hash + "\\nrdoc_simple_record_hash=" + hash + "\\nrdoc_simple_pixel_hash=" + hash + "\\nrdoc_simple_owner_frame_id=frame-7\\nrdoc_simple_capture_frame_id=frame-7\\n' > " + root + "/source/evidence.env && RDOC_SIMPLE_EVIDENCE_ENV=" + root + "/source/evidence.env BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-renderdoc-simple-gate.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)
val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("rdoc_simple_gate_status=fail")
expect(evidence).to_contain("rdoc_simple_gate_reason=capture-frame-path-mismatch")
expect(evidence).to_contain("rdoc_simple_gate_capture_identity_status=fail")
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

#### binds passing replay evidence to unchanged capture bytes

The executable SSpec builds one deterministic fake replay seam. Its complete
evidence creates a regular replay XML file and passes with equal current
capture/XML hashes and byte counts. The receipt explicitly records passing XML
file and hash status plus matching claimed/current XML hashes and byte counts.
Missing, symlinked, or changed replay XML
produces `replay-xml-missing`, `replay-xml-symlink`, or
`replay-xml-hash-mismatch`. Removing the capture hash, replacing it with
malformed text, or appending a byte to the `.rdc` produces
`missing-capture-sha256`, `invalid-capture-sha256`, and
`capture-sha256-mismatch`, respectively. Runnable source:
`test/03_system/check/renderdoc_simple_gate_spec.spl`.

<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-renderdoc-simple-gate-hash"
val hash = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
val command = "rm -rf " + root + " && mkdir -p " + root + "/source " + root + "/renderdoc/bin && " +
    "printf 'RDOCsynthetic capture\\n' > " + root + "/source/simple_gui_app-frame-7_0.rdc && " +
    "printf '#!/bin/sh\\nexit 0\\n' > " + root + "/renderdoc/bin/renderdoccmd && " +
    "printf '%s\\n' '#!/bin/sh' 'xml=$6/replay.xml' 'mkdir -p $6' 'rm -f $xml' 'printf replay-xml > $xml' 'xml_hash=0e7ba3dc516098a2f83448d059ea1e1f7b310ea2a43e7e190fdde1fa7969ea46' 'xml_bytes=10' 'if [ \"$FAKE_REPLAY_MODE\" = tamper ]; then printf x >> $xml; fi' 'if [ \"$FAKE_REPLAY_MODE\" = missing ]; then rm -f $xml; fi' 'if [ \"$FAKE_REPLAY_MODE\" = symlink ]; then printf target > $6/target.xml; rm -f $xml; ln -s target.xml $xml; fi' 'echo rdoc_simple_replay_status=pass' 'echo rdoc_simple_replay_reason=pass' 'echo rdoc_simple_replay_driver=vulkan' 'echo rdoc_simple_replay_capture_path=$5' 'echo rdoc_simple_replay_xml_path=$xml' 'echo rdoc_simple_replay_xml_hash=$xml_hash' 'echo rdoc_simple_replay_xml_bytes=$xml_bytes' 'echo rdoc_simple_replay_chunk_count=1' 'echo rdoc_simple_replay_relevant_action_count=1' 'echo rdoc_simple_replay_pipeline_count=1' 'echo rdoc_simple_replay_shader_count=1' 'echo rdoc_simple_replay_resource_count=1' 'echo rdoc_simple_replay_convert_exit_code=0' 'echo rdoc_simple_owner_agreement_status=pass' 'echo rdoc_simple_owner_api=vulkan' > " + root + "/fake-simple && " +
    "chmod +x " + root + "/renderdoc/bin/renderdoccmd " + root + "/fake-simple && . scripts/lib/renderdoc-evidence-common.shs && capture=" + root + "/source/simple_gui_app-frame-7_0.rdc && digest=$(rdoc_sha256_file \"$capture\") && " +
    "printf 'rdoc_backend=simple\\nrdoc_scene=vulkan-engine2d\\nrdoc_program=src/app/test/renderdoc_vulkan_capture.spl\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=%s\\nrdoc_capture_magic=RDOC\\nrdoc_capture_sha256=%s\\nrdoc_renderdoc_home=" + root + "/renderdoc\\nrdoc_simple_renderdoc_capture_template=" + root + "/source/simple_gui_app-frame-7\\nrdoc_simple_renderdoc_capture_template_set=1\\nrdoc_simple_runtime_backend=vulkan\\nrdoc_simple_renderdoc_available=1\\nrdoc_simple_renderdoc_start=1\\nrdoc_simple_renderdoc_capturing_before_end=1\\nrdoc_simple_renderdoc_end=1\\nrdoc_simple_renderdoc_num_captures=1\\nrdoc_simple_pixel_count=1\\nrdoc_simple_renderdoc_device=1\\nrdoc_simple_record_valid=1\\nrdoc_simple_semantic_hash=" + hash + "\\nrdoc_simple_record_hash=" + hash + "\\nrdoc_simple_pixel_hash=" + hash + "\\nrdoc_simple_owner_frame_id=frame-7\\nrdoc_simple_capture_frame_id=frame-7\\n' \"$capture\" \"$digest\" > " + root + "/source/evidence.env && " +
    "RDOC_SIMPLE_EVIDENCE_ENV=" + root + "/source/evidence.env RDOC_REPLAY_SIMPLE_BIN=" + root + "/fake-simple BUILD_DIR=" + root + "/pass REPORT_PATH=" + root + "/pass.md sh scripts/check/check-renderdoc-simple-gate.shs >/dev/null && " +
    "FAKE_REPLAY_MODE=missing RDOC_SIMPLE_EVIDENCE_ENV=" + root + "/source/evidence.env RDOC_REPLAY_SIMPLE_BIN=" + root + "/fake-simple BUILD_DIR=" + root + "/missing-xml REPORT_PATH=" + root + "/missing-xml.md sh scripts/check/check-renderdoc-simple-gate.shs >/dev/null || true; " +
    "FAKE_REPLAY_MODE=symlink RDOC_SIMPLE_EVIDENCE_ENV=" + root + "/source/evidence.env RDOC_REPLAY_SIMPLE_BIN=" + root + "/fake-simple BUILD_DIR=" + root + "/symlink-xml REPORT_PATH=" + root + "/symlink-xml.md sh scripts/check/check-renderdoc-simple-gate.shs >/dev/null || true; " +
    "FAKE_REPLAY_MODE=tamper RDOC_SIMPLE_EVIDENCE_ENV=" + root + "/source/evidence.env RDOC_REPLAY_SIMPLE_BIN=" + root + "/fake-simple BUILD_DIR=" + root + "/tamper-xml REPORT_PATH=" + root + "/tamper-xml.md sh scripts/check/check-renderdoc-simple-gate.shs >/dev/null || true; " +
    "sed -i '/^rdoc_capture_sha256=/d' " + root + "/source/evidence.env && RDOC_SIMPLE_EVIDENCE_ENV=" + root + "/source/evidence.env RDOC_REPLAY_SIMPLE_BIN=" + root + "/fake-simple BUILD_DIR=" + root + "/missing REPORT_PATH=" + root + "/missing.md sh scripts/check/check-renderdoc-simple-gate.shs >/dev/null || true; " +
    "printf 'rdoc_capture_sha256=bad\\n' >> " + root + "/source/evidence.env; RDOC_SIMPLE_EVIDENCE_ENV=" + root + "/source/evidence.env RDOC_REPLAY_SIMPLE_BIN=" + root + "/fake-simple BUILD_DIR=" + root + "/invalid REPORT_PATH=" + root + "/invalid.md sh scripts/check/check-renderdoc-simple-gate.shs >/dev/null || true; " +
    "sed -i 's/^rdoc_capture_sha256=.*/rdoc_capture_sha256='\"$digest\"'/' " + root + "/source/evidence.env; printf x >> \"$capture\"; RDOC_SIMPLE_EVIDENCE_ENV=" + root + "/source/evidence.env RDOC_REPLAY_SIMPLE_BIN=" + root + "/fake-simple BUILD_DIR=" + root + "/tamper REPORT_PATH=" + root + "/tamper.md sh scripts/check/check-renderdoc-simple-gate.shs >/dev/null || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val passing = file_read(root + "/pass/evidence.env")
expect(passing).to_contain("rdoc_simple_gate_status=pass")
expect(passing).to_contain("rdoc_simple_gate_capture_hash_status=pass")
val expected = _value_of(passing, "rdoc_simple_gate_capture_sha256")
val actual = _value_of(passing, "rdoc_simple_gate_capture_file_sha256")
expect(expected).to_equal(actual)
expect(expected.len()).to_equal(64)
expect(passing).to_contain("rdoc_simple_gate_replay_xml_file_status=pass")
expect(passing).to_contain("rdoc_simple_gate_replay_xml_hash_status=pass")
expect(_value_of(passing, "rdoc_simple_gate_replay_xml_hash")).to_equal(
    _value_of(passing, "rdoc_simple_gate_replay_xml_file_sha256"))
expect(_value_of(passing, "rdoc_simple_gate_replay_xml_bytes")).to_equal(
    _value_of(passing, "rdoc_simple_gate_replay_xml_file_bytes"))
expect(file_read(root + "/missing-xml/evidence.env")).to_contain("rdoc_simple_gate_reason=replay-xml-missing")
expect(file_read(root + "/symlink-xml/evidence.env")).to_contain("rdoc_simple_gate_reason=replay-xml-symlink")
expect(file_read(root + "/tamper-xml/evidence.env")).to_contain("rdoc_simple_gate_reason=replay-xml-hash-mismatch")

expect(file_read(root + "/missing/evidence.env")).to_contain("rdoc_simple_gate_reason=missing-capture-sha256")
expect(file_read(root + "/invalid/evidence.env")).to_contain("rdoc_simple_gate_reason=invalid-capture-sha256")
expect(file_read(root + "/tamper/evidence.env")).to_contain("rdoc_simple_gate_reason=capture-sha256-mismatch")
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


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md](doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)
- **Research:** [doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-25.md](doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-25.md)


</details>
