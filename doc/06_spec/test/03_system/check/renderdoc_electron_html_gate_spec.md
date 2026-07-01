# RenderDoc Electron HTML gate

> Validates the fail-closed gate for Electron Chromium/Vulkan HTML/CSS RenderDoc evidence. The local host may not have RenderDoc installed, but the gate must record a deterministic non-pass state and accept only Electron `.rdc` evidence that also proves the requested Chromium Vulkan/ANGLE launch contract.

<!-- sdn-diagram:id=renderdoc_electron_html_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=renderdoc_electron_html_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

renderdoc_electron_html_gate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=renderdoc_electron_html_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RenderDoc Electron HTML gate

Validates the fail-closed gate for Electron Chromium/Vulkan HTML/CSS RenderDoc evidence. The local host may not have RenderDoc installed, but the gate must record a deterministic non-pass state and accept only Electron `.rdc` evidence that also proves the requested Chromium Vulkan/ANGLE launch contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | doc/09_report/renderdoc_electron_html_gate_2026-06-25.md |
| Source | `test/03_system/check/renderdoc_electron_html_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the fail-closed gate for Electron Chromium/Vulkan HTML/CSS RenderDoc
evidence. The local host may not have RenderDoc installed, but the gate must
record a deterministic non-pass state and accept only Electron `.rdc` evidence
that also proves the requested Chromium Vulkan/ANGLE launch contract.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** doc/09_report/renderdoc_electron_html_gate_2026-06-25.md
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/renderdoc/canonical-probe/electron-html/evidence.env \
BUILD_DIR=build/test-renderdoc-electron-html-gate \
REPORT_PATH=build/test-renderdoc-electron-html-gate/report.md \
sh scripts/check/check-renderdoc-electron-html-gate.shs || true
```

## Acceptance

- Missing or failed Electron RenderDoc evidence produces typed non-pass gate
  evidence.
- Passing gate evidence requires Electron backend, `html-css-electron` scene,
  pass status, `RDOC` magic, an existing `.rdc` file, the canonical HTML/CSS
  RenderDoc fixture, the repo Electron shell binary, the live-bitmap capture
  script, and Vulkan requested API/ANGLE/features launch fields.
- Passing gate evidence also requires the Electron live-bitmap ARGB JSON proof
  to have the expected dimensions, `argb-u32` format, the
  `electron-chromium-capture` producer, complete pixel data, and nonblank
  rendered pixels.
- Electron live-bitmap ARGB dimensions, native dimensions, and pixels must be
  real safe JSON integers; stringified or unsafe exponential values are not
  accepted as rendered bitmap proof.
- The `.rdc` capture file and Electron ARGB JSON proof must be regular files,
  not symlinks to substituted or stale artifacts.

## Evidence Contract

The gate emits both declarative metadata and verified filesystem facts. The
producer may claim `rdoc_capture_magic=RDOC`, but the gate independently reads
the first four bytes of the referenced capture file and emits
`rdoc_electron_html_gate_capture_file_magic`. It also emits
`rdoc_electron_html_gate_capture_file_status` so reports can distinguish a
missing `.rdc` from a file that exists with the wrong magic.
Symlinked `.rdc` and ARGB artifacts are rejected before the gate reads their
contents.

The ARGB proof is separate from RenderDoc proof. A nonblank Electron bitmap can
prove Chromium rendered the fixture, but it does not prove RenderDoc captured
the browser GPU process. For that reason, pass requires both a valid `.rdc` and
valid ARGB proof.

## Failure Classes

Missing source evidence reports `missing-source-evidence`. A missing `.rdc`
reports `missing-rdc-file` or the capture reason from the source evidence. Bad
file magic reports `missing-rdoc-file-magic`. Vulkan/ANGLE launch mistakes
report the missing requested API, angle, feature, or launch flag.

The gate also reads the Chromium/Electron log when available. If the log shows
ANGLE Vulkan initialization failure, the gate reports the Vulkan log reason
instead of accepting a fallback bitmap render.
If the log shows Electron GPU process crashes while the `.rdc` is missing, the
gate preserves the exit count and exit codes as diagnostics while still failing
closed.
The gate also classifies launch metadata presence. Fresh capture evidence should
emit `rdoc_electron_launch_exit_code` and `rdoc_electron_launch_timed_out`; old
or hand-written evidence without both rows reports
`rdoc_electron_html_gate_launch_metadata_status=missing` or `partial`.
If the source evidence predates the shared RenderDoc capture helper, the gate
also emits `rdoc_electron_html_gate_source_contract_status=stale` with a
stale-source launch-metadata reason. Stale evidence remains non-pass; this only
separates a retained old capture from a fresh failed launch.

## Debugging

Inspect `build/test-renderdoc-electron-html-gate/evidence.env` for the active
host result. The most important keys are `rdoc_electron_html_gate_status`,
`rdoc_electron_html_gate_reason`,
`rdoc_electron_html_gate_capture_file_status`,
`rdoc_electron_html_gate_capture_file_magic`,
`rdoc_electron_html_gate_argb_status`, and
`rdoc_electron_html_gate_vulkan_log_status`.
Use `rdoc_electron_html_gate_launch_metadata_status` and
`rdoc_electron_html_gate_launch_metadata_reason` to distinguish stale evidence
from a fresh host run that completed or timed out.
Use `rdoc_electron_html_gate_source_contract_status` and
`rdoc_electron_html_gate_source_contract_reason` when deciding whether to
refresh retained Electron RenderDoc evidence before debugging the host.

When the top-level GUI RenderDoc aggregate is incomplete but ARGB parity passes,
this gate usually names the remaining native RenderDoc blocker. A prepared host
must turn the capture file status to `pass` and the file magic to `RDOC`.

## Evidence Checklist

- `rdoc_electron_html_gate_status=pass` is required for completion.
- `rdoc_electron_html_gate_capture_file_status=pass` proves the `.rdc` path
  exists and is nonempty.
- `rdoc_electron_html_gate_capture_file_magic=RDOC` proves the file bytes are a
  RenderDoc capture, not only a claimed path.
- `rdoc_electron_html_gate_argb_status=pass` proves the Electron-rendered bitmap
  was nonblank and structurally valid.
- `rdoc_electron_html_gate_requested_api=vulkan` and
  `rdoc_electron_html_gate_requested_angle=vulkan` prove the requested browser
  backing.
- `rdoc_electron_html_gate_vulkan_log_status=pass` or `not-recorded` keeps log
  diagnostics explicit; a Vulkan-unavailable log must fail the gate.
- `rdoc_electron_html_gate_launch_metadata_status=pass` means the source
  evidence recorded both the Electron launch exit code and timeout flag.

## Platform Notes

Linux verification usually exercises this gate with Electron Chromium launched
under RenderDoc and ANGLE Vulkan flags. macOS may use the same Electron evidence
shape when MoltenVK and RenderDoc are available, but platform setup can remain
blocked by RenderDoc packaging or upstream capture support. Windows may later
pair this gate with PIX or GPU debugger logs; those native logs can add fields,
but they must not remove the common capture-file status and magic evidence.

The gate is deliberately conservative across all platforms: a fallback bitmap,
software rendering path, or browser log that rejects Vulkan is not enough to
close the Electron RenderDoc requirement.

## Scenarios

### RenderDoc Electron HTML gate

#### writes typed non-pass evidence for missing or failed Electron capture

<details>
<summary>Executable SSpec</summary>

Runnable source: 70 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderdoc_common = rt_file_read_text("scripts/lib/renderdoc-evidence-common.shs") ?? ""
expect(renderdoc_common).to_contain("xvfb-run -a --server-args=")
expect(renderdoc_common).to_contain("-screen 0 ")
expect(renderdoc_common).to_contain("chromium-gpu-process-crashed-under-renderdoc")

val command = "rm -rf build/test-renderdoc-electron-html-gate && RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/renderdoc/canonical-probe/electron-html/evidence.env BUILD_DIR=build/test-renderdoc-electron-html-gate REPORT_PATH=build/test-renderdoc-electron-html-gate/report.md sh scripts/check/check-renderdoc-electron-html-gate.shs || true"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = _read_evidence("build/test-renderdoc-electron-html-gate/evidence.env")
expect(evidence).to_contain("rdoc_electron_html_gate_status=")
expect(evidence).to_contain("rdoc_electron_html_gate_reason=")
expect(evidence).to_contain("rdoc_electron_html_gate_source_env=")
expect(evidence).to_contain("rdoc_electron_html_gate_required_backend=electron")
expect(evidence).to_contain("rdoc_electron_html_gate_required_scene=html-css-electron")
expect(evidence).to_contain("rdoc_electron_html_gate_required_status=pass")
expect(evidence).to_contain("rdoc_electron_html_gate_required_magic=RDOC")
expect(evidence).to_contain("rdoc_electron_html_gate_required_api=vulkan")
expect(evidence).to_contain("rdoc_electron_html_gate_required_angle=vulkan")
expect(evidence).to_contain("rdoc_electron_html_gate_required_features=Vulkan")
expect(evidence).to_contain("rdoc_electron_html_gate_required_html_path_suffix=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html")
expect(evidence).to_contain("rdoc_electron_html_gate_required_electron_suffix=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron|tools/electron-shell/node_modules/.bin/electron")
expect(evidence).to_contain("rdoc_electron_html_gate_required_capture_script_suffix=tools/electron-live-bitmap/capture_html_argb.js")
expect(evidence).to_contain("rdoc_electron_html_gate_required_argb_status=pass")
expect(evidence).to_contain("rdoc_electron_html_gate_required_argb_format=argb-u32")
expect(evidence).to_contain("rdoc_electron_html_gate_required_argb_producer=electron-chromium-capture")
expect(evidence).to_contain("rdoc_electron_html_gate_required_argb_nonblank_pixel_count_min=1")
expect(evidence).to_contain("rdoc_electron_html_gate_required_launch_flag_enable_features=--enable-features=Vulkan")
expect(evidence).to_contain("rdoc_electron_html_gate_required_launch_flag_use_angle=--use-angle=vulkan")
expect(evidence).to_contain("rdoc_electron_html_gate_required_vulkan_log_no_angle_failure=1")
expect(evidence).to_contain("rdoc_electron_html_gate_capture_file_status=")
expect(evidence).to_contain("rdoc_electron_html_gate_capture_file_magic=")
expect(evidence).to_contain("rdoc_electron_html_gate_launch_metadata_status=")
expect(evidence).to_contain("rdoc_electron_html_gate_launch_metadata_reason=")
expect(evidence).to_contain("rdoc_electron_html_gate_source_contract_status=")
expect(evidence).to_contain("rdoc_electron_html_gate_source_contract_reason=")
expect(evidence).to_contain("rdoc_electron_html_gate_source_contract=scripts/lib/renderdoc-evidence-common.shs")
expect(evidence).to_contain("rdoc_electron_html_gate_log=")
expect(evidence).to_contain("rdoc_electron_html_gate_vulkan_log_status=")
expect(evidence).to_contain("rdoc_electron_html_gate_vulkan_log_reason=")

val status = _value_of(evidence, "rdoc_electron_html_gate_status")
val reason = _value_of(evidence, "rdoc_electron_html_gate_reason")
val backend = _value_of(evidence, "rdoc_electron_html_gate_backend")
val scene = _value_of(evidence, "rdoc_electron_html_gate_scene")
val capture_status = _value_of(evidence, "rdoc_electron_html_gate_capture_status")
val magic = _value_of(evidence, "rdoc_electron_html_gate_capture_magic")
val html_path = _value_of(evidence, "rdoc_electron_html_gate_html_path")
val electron = _value_of(evidence, "rdoc_electron_html_gate_electron")
val capture_script = _value_of(evidence, "rdoc_electron_html_gate_capture_script")
val api = _value_of(evidence, "rdoc_electron_html_gate_requested_api")
val angle = _value_of(evidence, "rdoc_electron_html_gate_requested_angle")
val features = _value_of(evidence, "rdoc_electron_html_gate_requested_features")
val flags = _value_of(evidence, "rdoc_electron_html_gate_launch_flags")

if status == "pass":
    expect(backend).to_equal("electron")
    expect(scene).to_equal("html-css-electron")
    expect(capture_status).to_equal("pass")
    expect(magic).to_equal("RDOC")
    expect(html_path).to_contain("test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html")
    expect(electron).to_contain("tools/electron-shell/node_modules/")
    expect(capture_script).to_contain("tools/electron-live-bitmap/capture_html_argb.js")
    expect(api).to_equal("vulkan")
    expect(angle).to_equal("vulkan")
    expect(features).to_contain("Vulkan")
    expect(flags).to_contain("--enable-features=Vulkan")
    expect(flags).to_contain("--use-angle=vulkan")
else:
    expect(reason.len()).to_be_greater_than(0)
```

</details>

#### passes with controlled Electron Vulkan RDOC evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-electron-html-gate-pass && mkdir -p build/test-renderdoc-electron-html-gate-pass/source && printf 'RDOCsynthetic electron capture\\n' > build/test-renderdoc-electron-html-gate-pass/source/electron.rdc && printf '{\"width\":2,\"height\":2,\"format\":\"argb-u32\",\"producer\":\"electron-chromium-capture\",\"nativeWidth\":2,\"nativeHeight\":2,\"pixels\":[4294967295,4278190335,4294967295,4294967295]}\\n' > build/test-renderdoc-electron-html-gate-pass/source/electron_argb.json && printf 'rdoc_backend=electron\\nrdoc_scene=html-css-electron\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-renderdoc-electron-html-gate-pass/source/electron.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_electron=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron\\nrdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js\\nrdoc_electron_argb=build/test-renderdoc-electron-html-gate-pass/source/electron_argb.json\\nrdoc_electron_width=2\\nrdoc_electron_height=2\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=Vulkan\\nrdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --enable-features=Vulkan --use-angle=vulkan\\nrdoc_electron_launch_exit_code=0\\nrdoc_electron_launch_timed_out=false\\n' > build/test-renderdoc-electron-html-gate-pass/source/evidence.env && RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/test-renderdoc-electron-html-gate-pass/source/evidence.env BUILD_DIR=build/test-renderdoc-electron-html-gate-pass/out REPORT_PATH=build/test-renderdoc-electron-html-gate-pass/report.md sh scripts/check/check-renderdoc-electron-html-gate.shs"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = _read_evidence("build/test-renderdoc-electron-html-gate-pass/out/evidence.env")
expect(evidence).to_contain("rdoc_electron_html_gate_status=pass")
expect(evidence).to_contain("rdoc_electron_html_gate_reason=pass")
expect(evidence).to_contain("rdoc_electron_html_gate_backend=electron")
expect(evidence).to_contain("rdoc_electron_html_gate_scene=html-css-electron")
expect(evidence).to_contain("rdoc_electron_html_gate_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html")
expect(evidence).to_contain("rdoc_electron_html_gate_electron=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron")
expect(evidence).to_contain("rdoc_electron_html_gate_required_electron_suffix=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron|tools/electron-shell/node_modules/.bin/electron")
expect(evidence).to_contain("rdoc_electron_html_gate_capture_script=tools/electron-live-bitmap/capture_html_argb.js")
expect(evidence).to_contain("rdoc_electron_html_gate_capture_magic=RDOC")
expect(evidence).to_contain("rdoc_electron_html_gate_capture_file_status=pass")
expect(evidence).to_contain("rdoc_electron_html_gate_capture_file_magic=RDOC")
expect(evidence).to_contain("rdoc_electron_html_gate_requested_api=vulkan")
expect(evidence).to_contain("rdoc_electron_html_gate_requested_angle=vulkan")
expect(evidence).to_contain("rdoc_electron_html_gate_requested_features=Vulkan")
expect(evidence).to_contain("rdoc_electron_html_gate_launch_metadata_status=pass")
expect(evidence).to_contain("rdoc_electron_html_gate_launch_metadata_reason=pass")
expect(evidence).to_contain("rdoc_electron_html_gate_source_contract_status=pass")
expect(evidence).to_contain("rdoc_electron_html_gate_source_contract_reason=pass")
expect(evidence).to_contain("rdoc_electron_html_gate_required_features=Vulkan")
expect(evidence).to_contain("rdoc_electron_html_gate_launch_flags=--no-sandbox --disable-gpu-sandbox --enable-features=Vulkan --use-angle=vulkan")
expect(evidence).to_contain("rdoc_electron_html_gate_argb_file_status=pass")
expect(evidence).to_contain("rdoc_electron_html_gate_argb_status=pass")
expect(evidence).to_contain("rdoc_electron_html_gate_argb_reason=pass")
expect(evidence).to_contain("rdoc_electron_html_gate_argb_format=argb-u32")
expect(evidence).to_contain("rdoc_electron_html_gate_argb_producer=electron-chromium-capture")
expect(evidence).to_contain("rdoc_electron_html_gate_argb_pixel_count=4")
expect(evidence).to_contain("rdoc_electron_html_gate_argb_nonblank_pixel_count=1")
expect(evidence).to_contain("rdoc_electron_html_gate_vulkan_log_status=not-recorded")
expect(evidence).to_contain("rdoc_electron_html_gate_required_vulkan_log_no_angle_failure=1")
```

</details>

#### rejects symlinked Electron RDOC and ARGB artifacts

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-renderdoc-electron-html-gate-symlink-artifacts"
val command = "rm -rf " + root + " && mkdir -p " + root + "/source && " +
    "printf 'RDOCsynthetic electron capture\\n' > " + root + "/source/electron-real.rdc && ln -s electron-real.rdc " + root + "/source/electron.rdc && " +
    "printf '{\"width\":2,\"height\":2,\"format\":\"argb-u32\",\"producer\":\"electron-chromium-capture\",\"nativeWidth\":2,\"nativeHeight\":2,\"pixels\":[4294967295,4278190335,4294967295,4294967295]}\\n' > " + root + "/source/electron_argb-real.json && ln -s electron_argb-real.json " + root + "/source/electron_argb.json && " +
    "printf 'rdoc_backend=electron\\nrdoc_scene=html-css-electron\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=" + root + "/source/electron.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_electron=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron\\nrdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js\\nrdoc_electron_argb=" + root + "/source/electron_argb.json\\nrdoc_electron_width=2\\nrdoc_electron_height=2\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=Vulkan\\nrdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --enable-features=Vulkan --use-angle=vulkan\\n' > " + root + "/source/evidence.env && " +
    "RDOC_ELECTRON_HTML_EVIDENCE_ENV=" + root + "/source/evidence.env BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-renderdoc-electron-html-gate.shs || true"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = _read_evidence(root + "/out/evidence.env")
expect(evidence).to_contain("rdoc_electron_html_gate_status=fail")
expect(evidence).to_contain("rdoc_electron_html_gate_reason=rdc-file-symlink")
expect(evidence).to_contain("rdoc_electron_html_gate_capture_file_status=symlink")
expect(evidence).to_contain("rdoc_electron_html_gate_capture_file_magic=")
expect(evidence).to_contain("rdoc_electron_html_gate_argb_file_status=symlink")
expect(evidence).to_contain("rdoc_electron_html_gate_argb_status=fail")
expect(evidence).to_contain("rdoc_electron_html_gate_argb_reason=electron-argb-symlink")
```

</details>

#### keeps nonblank Electron ARGB proof while failing a missing RDOC capture

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-electron-html-gate-missing-rdc-with-argb && mkdir -p build/test-renderdoc-electron-html-gate-missing-rdc-with-argb/source && printf '{\"width\":2,\"height\":2,\"format\":\"argb-u32\",\"producer\":\"electron-chromium-capture\",\"nativeWidth\":2,\"nativeHeight\":2,\"pixels\":[4294967295,4278190335,4294967295,4294967295]}\\n' > build/test-renderdoc-electron-html-gate-missing-rdc-with-argb/source/electron_argb.json && printf '[1:1:ERROR:content/browser/gpu/gpu_process_host.cc:998] GPU process exited unexpectedly: exit_code=139\\n[1:1:ERROR:content/browser/gpu/gpu_process_host.cc:998] GPU process exited unexpectedly: exit_code=139\\n' > build/test-renderdoc-electron-html-gate-missing-rdc-with-argb/source/renderdoc-electron-html.log && printf 'rdoc_backend=electron\\nrdoc_scene=html-css-electron\\nrdoc_capture_status=fail\\nrdoc_capture_reason=missing-rdc\\nrdoc_capture_file=\\nrdoc_capture_magic=\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_electron=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron\\nrdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js\\nrdoc_electron_argb=build/test-renderdoc-electron-html-gate-missing-rdc-with-argb/source/electron_argb.json\\nrdoc_electron_width=2\\nrdoc_electron_height=2\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=Vulkan\\nrdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --no-zygote --ozone-platform=x11 --enable-features=Vulkan,DefaultANGLEVulkan,VulkanFromANGLE --ignore-gpu-blocklist --enable-gpu-rasterization --use-angle=vulkan\\nrdoc_log=build/test-renderdoc-electron-html-gate-missing-rdc-with-argb/source/renderdoc-electron-html.log\\n' > build/test-renderdoc-electron-html-gate-missing-rdc-with-argb/source/evidence.env && RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/test-renderdoc-electron-html-gate-missing-rdc-with-argb/source/evidence.env BUILD_DIR=build/test-renderdoc-electron-html-gate-missing-rdc-with-argb/out REPORT_PATH=build/test-renderdoc-electron-html-gate-missing-rdc-with-argb/report.md sh scripts/check/check-renderdoc-electron-html-gate.shs || true"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = _read_evidence("build/test-renderdoc-electron-html-gate-missing-rdc-with-argb/out/evidence.env")
expect(evidence).to_contain("rdoc_electron_html_gate_status=fail")
expect(evidence).to_contain("rdoc_electron_html_gate_reason=missing-rdc")
expect(evidence).to_contain("rdoc_electron_html_gate_capture_status=fail")
expect(evidence).to_contain("rdoc_electron_html_gate_capture_reason=missing-rdc")
expect(evidence).to_contain("rdoc_electron_html_gate_capture_file=")
expect(evidence).to_contain("rdoc_electron_html_gate_argb_status=pass")
expect(evidence).to_contain("rdoc_electron_html_gate_argb_reason=pass")
expect(evidence).to_contain("rdoc_electron_html_gate_argb_pixel_count=4")
expect(evidence).to_contain("rdoc_electron_html_gate_argb_nonblank_pixel_count=1")
expect(evidence).to_contain("rdoc_electron_html_gate_launch_exit_code=")
expect(evidence).to_contain("rdoc_electron_html_gate_launch_timed_out=")
expect(evidence).to_contain("rdoc_electron_html_gate_launch_metadata_status=missing")
expect(evidence).to_contain("rdoc_electron_html_gate_launch_metadata_reason=missing-launch-exit-metadata")
expect(evidence).to_contain("rdoc_electron_html_gate_gpu_process_exit_status=fail")
expect(evidence).to_contain("rdoc_electron_html_gate_gpu_process_exit_count=2")
expect(evidence).to_contain("rdoc_electron_html_gate_gpu_process_exit_codes=139")
expect(evidence).to_contain("rdoc_electron_html_gate_gpu_process_exit_reason=gpu-process-exited-unexpectedly")
expect(evidence).to_contain("rdoc_electron_html_gate_launch_flags=--no-sandbox --disable-gpu-sandbox --no-zygote --ozone-platform=x11 --enable-features=Vulkan,DefaultANGLEVulkan,VulkanFromANGLE --ignore-gpu-blocklist --enable-gpu-rasterization --use-angle=vulkan")
```

</details>

#### classifies old Electron evidence that predates the capture-helper launch metadata contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-renderdoc-electron-html-gate-stale-source-contract"
val command = "rm -rf " + root + " && mkdir -p " + root + "/source && " +
    "printf '{\"width\":2,\"height\":2,\"format\":\"argb-u32\",\"producer\":\"electron-chromium-capture\",\"nativeWidth\":2,\"nativeHeight\":2,\"pixels\":[4294967295,4278190335,4294967295,4294967295]}\\n' > " + root + "/source/electron_argb.json && " +
    "printf 'rdoc_backend=electron\\nrdoc_scene=html-css-electron\\nrdoc_capture_status=fail\\nrdoc_capture_reason=missing-rdc\\nrdoc_capture_file=\\nrdoc_capture_magic=\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_electron=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron\\nrdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js\\nrdoc_electron_argb=" + root + "/source/electron_argb.json\\nrdoc_electron_width=2\\nrdoc_electron_height=2\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=Vulkan\\nrdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --enable-features=Vulkan --use-angle=vulkan\\n' > " + root + "/source/evidence.env && " +
    "touch -t 200001010000 " + root + "/source/evidence.env && " +
    "RDOC_ELECTRON_HTML_EVIDENCE_ENV=" + root + "/source/evidence.env BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-renderdoc-electron-html-gate.shs || true"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = _read_evidence(root + "/out/evidence.env")
expect(evidence).to_contain("rdoc_electron_html_gate_status=fail")
expect(evidence).to_contain("rdoc_electron_html_gate_reason=missing-rdc")
expect(evidence).to_contain("rdoc_electron_html_gate_launch_metadata_status=missing")
expect(evidence).to_contain("rdoc_electron_html_gate_launch_metadata_reason=missing-launch-exit-metadata")
expect(evidence).to_contain("rdoc_electron_html_gate_source_contract_status=stale")
expect(evidence).to_contain("rdoc_electron_html_gate_source_contract_reason=stale-source-missing-launch-exit-metadata")
expect(evidence).to_contain("rdoc_electron_html_gate_source_contract=scripts/lib/renderdoc-evidence-common.shs")
```

</details>

#### rejects Electron captures missing live-bitmap ARGB rendered pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-electron-html-gate-missing-argb && mkdir -p build/test-renderdoc-electron-html-gate-missing-argb/source && printf 'RDOCsynthetic electron capture\\n' > build/test-renderdoc-electron-html-gate-missing-argb/source/electron.rdc && printf 'rdoc_backend=electron\\nrdoc_scene=html-css-electron\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-renderdoc-electron-html-gate-missing-argb/source/electron.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_electron=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron\\nrdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js\\nrdoc_electron_argb=build/test-renderdoc-electron-html-gate-missing-argb/source/electron_argb.json\\nrdoc_electron_width=2\\nrdoc_electron_height=2\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=Vulkan\\nrdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --enable-features=Vulkan --use-angle=vulkan\\n' > build/test-renderdoc-electron-html-gate-missing-argb/source/evidence.env && RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/test-renderdoc-electron-html-gate-missing-argb/source/evidence.env BUILD_DIR=build/test-renderdoc-electron-html-gate-missing-argb/out REPORT_PATH=build/test-renderdoc-electron-html-gate-missing-argb/report.md sh scripts/check/check-renderdoc-electron-html-gate.shs || true"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = _read_evidence("build/test-renderdoc-electron-html-gate-missing-argb/out/evidence.env")
expect(evidence).to_contain("rdoc_electron_html_gate_status=fail")
expect(evidence).to_contain("rdoc_electron_html_gate_reason=missing-electron-argb-file")
expect(evidence).to_contain("rdoc_electron_html_gate_argb_status=missing")
expect(evidence).to_contain("rdoc_electron_html_gate_argb_pixel_count=0")
expect(evidence).to_contain("rdoc_electron_html_gate_required_argb_status=pass")
```

</details>

#### rejects unsafe or stringified Electron ARGB bitmap proof values

- Confirm Electron ARGB bitmap proof rejects coerced numeric values
   - Expected: unsafe does not contain `rdoc_electron_html_gate_argb_width=1e+21`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-renderdoc-electron-html-gate-argb-types"
val command = "rm -rf " + root + " && mkdir -p " + root + "/source && " +
    "printf 'RDOCsynthetic electron capture\\n' > " + root + "/source/electron.rdc && " +
    "printf '{\"width\":1e21,\"height\":2,\"format\":\"argb-u32\",\"producer\":\"electron-chromium-capture\",\"nativeWidth\":2,\"nativeHeight\":2,\"pixels\":[4294967295,4278190335,4294967295,4294967295]}\\n' > " + root + "/source/unsafe_argb.json && " +
    "printf '{\"width\":2,\"height\":2,\"format\":\"argb-u32\",\"producer\":\"electron-chromium-capture\",\"nativeWidth\":2,\"nativeHeight\":2,\"pixels\":[4294967295,\"4278190335\",4294967295,4294967295]}\\n' > " + root + "/source/string_pixel_argb.json && " +
    "printf 'rdoc_backend=electron\\nrdoc_scene=html-css-electron\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=" + root + "/source/electron.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_electron=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron\\nrdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js\\nrdoc_electron_argb=" + root + "/source/unsafe_argb.json\\nrdoc_electron_width=2\\nrdoc_electron_height=2\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=Vulkan\\nrdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --enable-features=Vulkan --use-angle=vulkan\\n' > " + root + "/source/unsafe.env && " +
    "RDOC_ELECTRON_HTML_EVIDENCE_ENV=" + root + "/source/unsafe.env BUILD_DIR=" + root + "/unsafe-out REPORT_PATH=" + root + "/unsafe-report.md sh scripts/check/check-renderdoc-electron-html-gate.shs || true; " +
    "printf 'rdoc_backend=electron\\nrdoc_scene=html-css-electron\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=" + root + "/source/electron.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_electron=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron\\nrdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js\\nrdoc_electron_argb=" + root + "/source/string_pixel_argb.json\\nrdoc_electron_width=2\\nrdoc_electron_height=2\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=Vulkan\\nrdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --enable-features=Vulkan --use-angle=vulkan\\n' > " + root + "/source/string-pixel.env && " +
    "RDOC_ELECTRON_HTML_EVIDENCE_ENV=" + root + "/source/string-pixel.env BUILD_DIR=" + root + "/string-pixel-out REPORT_PATH=" + root + "/string-pixel-report.md sh scripts/check/check-renderdoc-electron-html-gate.shs || true"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val unsafe = _read_evidence(root + "/unsafe-out/evidence.env")
val string_pixel = _read_evidence(root + "/string-pixel-out/evidence.env")
step("Confirm Electron ARGB bitmap proof rejects coerced numeric values")
expect(unsafe).to_contain("rdoc_electron_html_gate_status=fail")
expect(unsafe).to_contain("rdoc_electron_html_gate_reason=missing-electron-argb-dimensions")
expect(unsafe).to_contain("rdoc_electron_html_gate_argb_status=invalid")
expect(unsafe).to_contain("rdoc_electron_html_gate_argb_width=")
expect(unsafe.contains("rdoc_electron_html_gate_argb_width=1e+21")).to_equal(false)
expect(string_pixel).to_contain("rdoc_electron_html_gate_status=fail")
expect(string_pixel).to_contain("rdoc_electron_html_gate_reason=unexpected-electron-argb-pixel-type")
expect(string_pixel).to_contain("rdoc_electron_html_gate_argb_status=invalid")
```

</details>

#### rejects Electron captures from an unexpected binary path

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-electron-html-gate-wrong-electron && mkdir -p build/test-renderdoc-electron-html-gate-wrong-electron/source && printf 'RDOCsynthetic electron capture\\n' > build/test-renderdoc-electron-html-gate-wrong-electron/source/electron.rdc && printf '{\"width\":2,\"height\":2,\"format\":\"argb-u32\",\"producer\":\"electron-chromium-capture\",\"nativeWidth\":2,\"nativeHeight\":2,\"pixels\":[4294967295,4278190335,4294967295,4294967295]}\\n' > build/test-renderdoc-electron-html-gate-wrong-electron/source/electron_argb.json && printf 'rdoc_backend=electron\\nrdoc_scene=html-css-electron\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-renderdoc-electron-html-gate-wrong-electron/source/electron.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_electron=/tmp/not-simple-electron\\nrdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js\\nrdoc_electron_argb=build/test-renderdoc-electron-html-gate-wrong-electron/source/electron_argb.json\\nrdoc_electron_width=2\\nrdoc_electron_height=2\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=Vulkan\\nrdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --enable-features=Vulkan --use-angle=vulkan\\n' > build/test-renderdoc-electron-html-gate-wrong-electron/source/evidence.env && RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/test-renderdoc-electron-html-gate-wrong-electron/source/evidence.env BUILD_DIR=build/test-renderdoc-electron-html-gate-wrong-electron/out REPORT_PATH=build/test-renderdoc-electron-html-gate-wrong-electron/report.md sh scripts/check/check-renderdoc-electron-html-gate.shs || true"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = _read_evidence("build/test-renderdoc-electron-html-gate-wrong-electron/out/evidence.env")
expect(evidence).to_contain("rdoc_electron_html_gate_status=fail")
expect(evidence).to_contain("rdoc_electron_html_gate_reason=unexpected-electron-binary")
expect(evidence).to_contain("rdoc_electron_html_gate_electron=/tmp/not-simple-electron")
expect(evidence).to_contain("rdoc_electron_html_gate_required_electron_suffix=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron|tools/electron-shell/node_modules/.bin/electron")
```

</details>

#### rejects Electron captures whose file header is not RDOC

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-electron-html-gate-bad-file-magic && mkdir -p build/test-renderdoc-electron-html-gate-bad-file-magic/source && printf 'NOPEsynthetic electron capture\\n' > build/test-renderdoc-electron-html-gate-bad-file-magic/source/electron.rdc && printf 'rdoc_backend=electron\\nrdoc_scene=html-css-electron\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-renderdoc-electron-html-gate-bad-file-magic/source/electron.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_electron=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron\\nrdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=Vulkan\\nrdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --enable-features=Vulkan --use-angle=vulkan\\n' > build/test-renderdoc-electron-html-gate-bad-file-magic/source/evidence.env && RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/test-renderdoc-electron-html-gate-bad-file-magic/source/evidence.env BUILD_DIR=build/test-renderdoc-electron-html-gate-bad-file-magic/out REPORT_PATH=build/test-renderdoc-electron-html-gate-bad-file-magic/report.md sh scripts/check/check-renderdoc-electron-html-gate.shs || true"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = _read_evidence("build/test-renderdoc-electron-html-gate-bad-file-magic/out/evidence.env")
expect(evidence).to_contain("rdoc_electron_html_gate_status=fail")
expect(evidence).to_contain("rdoc_electron_html_gate_reason=missing-rdoc-file-magic")
expect(evidence).to_contain("rdoc_electron_html_gate_capture_magic=RDOC")
expect(evidence).to_contain("rdoc_electron_html_gate_capture_file_magic=NOPE")
```

</details>

#### rejects Electron captures whose log proves Vulkan ANGLE was unavailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-electron-html-gate-vulkan-log-fail && mkdir -p build/test-renderdoc-electron-html-gate-vulkan-log-fail/source && printf 'RDOCsynthetic electron capture\\n' > build/test-renderdoc-electron-html-gate-vulkan-log-fail/source/electron.rdc && printf '{\"width\":2,\"height\":2,\"format\":\"argb-u32\",\"producer\":\"electron-chromium-capture\",\"nativeWidth\":2,\"nativeHeight\":2,\"pixels\":[4294967295,4278190335,4294967295,4294967295]}\\n' > build/test-renderdoc-electron-html-gate-vulkan-log-fail/source/electron_argb.json && printf '[1:1:ERROR:gl_factory.cc(102)] Requested GL implementation (gl=egl-angle,angle=vulkan) not found in allowed implementations: [(gl=egl-angle,angle=metal)]\\n[1:1:ERROR:viz_main_impl.cc(181)] Exiting GPU process due to errors during initialization\\n' > build/test-renderdoc-electron-html-gate-vulkan-log-fail/source/renderdoc-electron-html.log && printf 'rdoc_backend=electron\\nrdoc_scene=html-css-electron\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-renderdoc-electron-html-gate-vulkan-log-fail/source/electron.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_electron=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron\\nrdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js\\nrdoc_electron_argb=build/test-renderdoc-electron-html-gate-vulkan-log-fail/source/electron_argb.json\\nrdoc_electron_width=2\\nrdoc_electron_height=2\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=Vulkan\\nrdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --enable-features=Vulkan --use-angle=vulkan\\nrdoc_log=build/test-renderdoc-electron-html-gate-vulkan-log-fail/source/renderdoc-electron-html.log\\n' > build/test-renderdoc-electron-html-gate-vulkan-log-fail/source/evidence.env && RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/test-renderdoc-electron-html-gate-vulkan-log-fail/source/evidence.env BUILD_DIR=build/test-renderdoc-electron-html-gate-vulkan-log-fail/out REPORT_PATH=build/test-renderdoc-electron-html-gate-vulkan-log-fail/report.md sh scripts/check/check-renderdoc-electron-html-gate.shs || true"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = _read_evidence("build/test-renderdoc-electron-html-gate-vulkan-log-fail/out/evidence.env")
expect(evidence).to_contain("rdoc_electron_html_gate_status=fail")
expect(evidence).to_contain("rdoc_electron_html_gate_reason=vulkan-angle-unavailable")
expect(evidence).to_contain("rdoc_electron_html_gate_vulkan_log_status=fail")
expect(evidence).to_contain("rdoc_electron_html_gate_vulkan_log_reason=vulkan-angle-unavailable")
expect(evidence).to_contain("rdoc_electron_html_gate_log=build/test-renderdoc-electron-html-gate-vulkan-log-fail/source/renderdoc-electron-html.log")
```

</details>

#### rejects Electron captures missing the Vulkan ANGLE launch flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-electron-html-gate-missing-angle; mkdir -p build/test-renderdoc-electron-html-gate-missing-angle/source; printf 'RDOCsynthetic electron capture\\n' > build/test-renderdoc-electron-html-gate-missing-angle/source/electron.rdc; printf 'rdoc_backend=electron\\nrdoc_scene=html-css-electron\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-renderdoc-electron-html-gate-missing-angle/source/electron.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_electron=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron\\nrdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=Vulkan\\nrdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --enable-features=Vulkan\\n' > build/test-renderdoc-electron-html-gate-missing-angle/source/evidence.env; RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/test-renderdoc-electron-html-gate-missing-angle/source/evidence.env BUILD_DIR=build/test-renderdoc-electron-html-gate-missing-angle/out REPORT_PATH=build/test-renderdoc-electron-html-gate-missing-angle/report.md sh scripts/check/check-renderdoc-electron-html-gate.shs || true"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = _read_evidence("build/test-renderdoc-electron-html-gate-missing-angle/out/evidence.env")
expect(evidence).to_contain("rdoc_electron_html_gate_status=fail")
expect(evidence).to_contain("rdoc_electron_html_gate_reason=missing-vulkan-angle-flag")
```

</details>

#### rejects Electron captures missing the Vulkan requested feature field

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-electron-html-gate-missing-feature && mkdir -p build/test-renderdoc-electron-html-gate-missing-feature/source && printf 'RDOCsynthetic electron capture\\n' > build/test-renderdoc-electron-html-gate-missing-feature/source/electron.rdc && printf 'rdoc_backend=electron\\nrdoc_scene=html-css-electron\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-renderdoc-electron-html-gate-missing-feature/source/electron.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_electron=tools/electron-shell/node_modules/electron/dist/Electron.app/Contents/MacOS/Electron\\nrdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=\\nrdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --enable-features=Vulkan --use-angle=vulkan\\n' > build/test-renderdoc-electron-html-gate-missing-feature/source/evidence.env && RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/test-renderdoc-electron-html-gate-missing-feature/source/evidence.env BUILD_DIR=build/test-renderdoc-electron-html-gate-missing-feature/out REPORT_PATH=build/test-renderdoc-electron-html-gate-missing-feature/report.md sh scripts/check/check-renderdoc-electron-html-gate.shs || true"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = _read_evidence("build/test-renderdoc-electron-html-gate-missing-feature/out/evidence.env")
expect(evidence).to_contain("rdoc_electron_html_gate_status=fail")
expect(evidence).to_contain("rdoc_electron_html_gate_reason=missing-vulkan-requested-feature")
expect(evidence).to_contain("rdoc_electron_html_gate_requested_features=")
expect(evidence).to_contain("rdoc_electron_html_gate_required_features=Vulkan")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md](doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)
- **Research:** [doc/09_report/renderdoc_electron_html_gate_2026-06-25.md](doc/09_report/renderdoc_electron_html_gate_2026-06-25.md)


</details>
