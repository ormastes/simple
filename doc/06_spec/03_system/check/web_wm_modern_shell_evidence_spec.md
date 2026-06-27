# Web WM Modern Shell Evidence Wrapper

## Overview

This system spec validates the lightweight evidence contract for
`scripts/check/check-web-wm-modern-shell-evidence.shs`.

The wrapper may fail closed when the host cannot launch the Simple runtime or
Electron. Even in that state, it must emit both the legacy artifact keys and the
canonical `*_path` aliases consumed by
`scripts/check/check-gui-renderdoc-feature-coverage-status.shs`.

## Operator Flow

Run:

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/web_wm_modern_shell_evidence_spec.spl --mode=interpreter --clean --fail-fast
```

The spec forces an early unavailable wrapper exit with `SIMPLE_CMD=/bin/false`
so it does not depend on Electron, RenderDoc, Vulkan, or a working GUI host.

## Acceptance

- The wrapper exits successfully for a diagnostic unavailable state.
- `web_wm_modern_shell_evidence_status=environment-unavailable` is retained.
- Legacy artifact keys such as `web_wm_modern_shell_evidence_html` are emitted.
- Canonical aliases such as `web_wm_modern_shell_evidence_html_path` are emitted.
- Interaction artifact aliases are emitted for JSON, PNG, and log outputs.

## Related Guide

See `doc/07_guide/tooling/renderdoc_capture_infra.md` for the aggregate GUI
RenderDoc evidence contract and remaining completion gates.
