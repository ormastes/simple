# RenderDoc Capture Infrastructure

Use the shared RenderDoc interface for both capture styles:

```sh
scripts/setup/setup-renderdoc-env.shs --check
scripts/setup/setup-renderdoc-env.shs --register-vulkan-layer
scripts/tool/renderdoc-evidence.shs capture-simple
scripts/tool/renderdoc-evidence.shs capture-html
RDOC_EXTERNAL_RUN_CAPTURE=1 sh scripts/check/check-renderdoc-external-host-capture.shs
```

## Interfaces

- `scripts/tool/renderdoc-evidence.shs env` prints resolved paths.
- `scripts/tool/renderdoc-evidence.shs capture-simple` runs the Simple
  in-application `rt_renderdoc_*` Vulkan Engine2D capture.
- `scripts/tool/renderdoc-evidence.shs capture-html` runs original
  `renderdoccmd capture` around Chrome for the HTML/CSS fixture.
- `test/helpers/renderdoc_capture_helper.shs` exposes the same interface for
  test scripts.

Compatibility wrappers remain:

- `scripts/check/check-renderdoc-vulkan-capture.shs`
- `scripts/check/check-renderdoc-html-capture.shs`

## Environment

Common variables:

- `RDOC_HOME`: RenderDoc install root containing `bin/renderdoccmd`.
  On macOS, this may also be a `RenderDoc.app` bundle containing
  `Contents/MacOS/renderdoccmd`.
- `RDOC_CHROME`: Chrome/Chromium binary for HTML capture.
- `RDOC_OUTPUT_DIR`: base output directory.
- `RDOC_CAPTURE_TIMEOUT_SECS`: bounded capture timeout.
- `RDOC_HTML_PATH`: HTML fixture for `capture-html`.
- `RDOC_SIMPLE_PROG`: Simple capture program for `capture-simple`.

The helper validates `.rdc` files by checking the `RDOC` magic header. If a host
cannot provide Chrome Vulkan or a non-CPU Vulkan device, record the concrete
reason in `doc/09_report/` instead of duplicating ad hoc capture commands.

## Evidence Artifacts

Each capture command writes an `evidence.env` file under its output directory.
Important keys:

- `rdoc_backend`: `simple` or `original`.
- `rdoc_scene`: capture scenario name.
- `rdoc_log`: capture log path.
- `rdoc_capture_status`: `pass`, `fail`, or `unavailable`.
- `rdoc_capture_reason`: concrete pass/fail/unavailable reason.
- `rdoc_capture_file`: `.rdc` path when one exists.
- `rdoc_capture_magic`: `RDOC` for a valid RenderDoc capture.

The current canonical evidence contract is:

- Simple in-application path:
  `build/renderdoc/canonical-probe/simple/evidence.env` must report
  `rdoc_capture_status=pass`, `rdoc_capture_magic=RDOC`, and an existing
  `.rdc` file. If that env/file is missing, the GUI RenderDoc goal remains
  incomplete with `missing-simple-rdoc`.
- Original Chrome HTML/CSS path:
  `build/renderdoc/canonical-probe/html/evidence.env`, or an external-host
  evidence env, must pass the original-backend gate with `RDOC` magic. A local
  failed capture or missing env is not completion evidence.

## External Host Gate

Use the gate when another host or CI job supplies the original
RenderDoc+Chrome evidence:

```sh
RDOC_EXTERNAL_RUN_CAPTURE=1 sh scripts/check/check-renderdoc-external-host-capture.shs

RDOC_HTML_EVIDENCE_ENV=build/renderdoc/canonical-probe/html/evidence.env \
  sh scripts/check/check-renderdoc-html-external-host-gate.shs
```

The external-host wrapper runs setup, capture, and the gate. The low-level gate
passes only when the source evidence contains:

- `rdoc_backend=original`
- `rdoc_capture_status=pass`
- `rdoc_capture_magic=RDOC`
- an existing `.rdc` path in `rdoc_capture_file`

Otherwise it writes fail-closed evidence under
`build/renderdoc/html-external-host-gate/evidence.env`.

Without `RDOC_EXTERNAL_RUN_CAPTURE=1`, the wrapper performs a readiness-only
run and writes `rdoc_external_host_capture_status=unavailable` with
`rdoc_external_host_capture_reason=capture-not-requested`.

## macOS Notes

macOS does not provide native Vulkan drivers. Use the LunarG Vulkan SDK with
MoltenVK, or another Metal-backed Vulkan portability implementation, when
testing the Simple Vulkan path on macOS.

The setup helper resolves either an unpacked RenderDoc tree with
`bin/renderdoccmd` or a macOS `RenderDoc.app` bundle, and prints both
`LD_LIBRARY_PATH` and `DYLD_LIBRARY_PATH` exports for prepared capture hosts.

The shared CLI remains the preferred interface:

```sh
scripts/setup/setup-renderdoc-env.shs --check
scripts/tool/renderdoc-evidence.shs capture-simple
scripts/tool/renderdoc-evidence.shs capture-html
sh scripts/check/check-renderdoc-macos-portability-probe.shs
```

Treat macOS results as portability evidence unless they produce the same
original RenderDoc+Chrome `.rdc` contract required by
`scripts/check/check-renderdoc-html-external-host-gate.shs`. If Chrome renders
through Metal/ANGLE or Vulkan-over-Metal, record that distinction in
`doc/09_report/`. Use Xcode GPU Frame Capture for Metal-level inspection when
RenderDoc cannot capture the macOS path.

By default the macOS probe records availability only. Set
`RDOC_MACOS_RUN_CAPTURES=1` on a prepared macOS host to run the Simple
RenderDoc capture and exploratory Chrome capture through the shared CLI.
