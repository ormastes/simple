# HTML/CSS RenderDoc Restart Audit - 2026-06-18

## Scope

Restart audit for `doc/03_plan/sys_test/html_css_spec_traceability.md`.
This audit intentionally does not rerun the known-crashing local
Chrome-under-RenderDoc capture path.

## Current Inventory Check

Command:

```sh
sh scripts/check/check-html-css-sspec-traceability.shs
```

Result:

- `PASS: HTML/CSS SSpec traceability html_tags=105 css_properties=394`
- Implemented CSS subset owner:
  `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_generated_html_css_combinations_spec.spl`
- Unsupported CSS inventory owner:
  `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_inventory_traceability_spec.spl`

This preserves the current-spec evidence for HTML tags, implemented CSS, and
inventory-only CSS traceability.

## Local RenderDoc Setup

Command:

```sh
scripts/setup/setup-renderdoc-env.shs --check
```

Result:

- `rdoc_status=ready`
- `rdoc_home=/home/ormastes/dev/pub/simple/build/tools/renderdoc`
- `rdoc_chrome=/home/ormastes/.cache/ms-playwright/chromium-1223/chrome-linux64/chrome`
- `rdoc_timeout_secs=45`

## Existing Evidence Artifacts

Simple in-application Vulkan RenderDoc evidence:

- `build/renderdoc/canonical-probe/simple/evidence.env`
- `rdoc_backend=simple`
- `rdoc_capture_status=pass`
- `rdoc_capture_magic=RDOC`
- `rdoc_capture_file=build/renderdoc/canonical-probe/simple/simple_gui_capture.rdc`

Original Chrome HTML/CSS RenderDoc evidence:

- `build/renderdoc/canonical-probe/html/evidence.env`
- `rdoc_backend=original`
- `rdoc_capture_status=fail`
- `rdoc_capture_reason=missing-rdc`
- `rdoc_capture_magic=` empty
- `rdoc_capture_file=` empty

External-host gate against the failed local evidence:

```sh
RDOC_HTML_EVIDENCE_ENV=build/renderdoc/canonical-probe/html/evidence.env \
  sh scripts/check/check-renderdoc-html-external-host-gate.shs
```

Result:

- `rdoc_html_external_gate_status=fail`
- `rdoc_html_external_gate_reason=missing-rdc`
- `rdoc_html_external_gate_required_backend=original`
- `rdoc_html_external_gate_required_status=pass`
- `rdoc_html_external_gate_required_magic=RDOC`

## Restart Verdict

Completed evidence remains current for:

- HTML element traceability;
- CSS property traceability;
- generated GUI HTML/CSS SSpec coverage;
- Simple in-application Vulkan RenderDoc `.rdc` capture;
- local RenderDoc setup and fail-closed external-host gate behavior.

Remaining evidence is unchanged:

- original Chrome HTML/CSS RenderDoc capture must be produced on a host where
  Chrome-on-Vulkan can run under RenderDoc without the documented GPU-process
  crash; or
- macOS/MoltenVK portability evidence may be added as supplemental evidence,
  but it does not replace the original Chrome-on-Linux-Vulkan RenderDoc gate.
