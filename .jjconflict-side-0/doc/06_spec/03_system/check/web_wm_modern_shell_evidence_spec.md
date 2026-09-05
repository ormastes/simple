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
It also checks that PATH-based `simple` discovery remains opt-in for the wrapper
and is enabled by the aggregate nested Web WM evidence run. The aggregate also
refreshes the default stale `simple-runtime-unavailable` Web WM evidence env
when no explicit `WEB_WM_MODERN_SHELL_EVIDENCE_ENV` override is supplied.

## Acceptance

- The wrapper exits successfully for a diagnostic unavailable state.
- `web_wm_modern_shell_evidence_status=environment-unavailable` is retained.
- Legacy artifact keys such as `web_wm_modern_shell_evidence_html` are emitted.
- Canonical aliases such as `web_wm_modern_shell_evidence_html_path` are emitted.
- Interaction artifact aliases are emitted for JSON, PNG, and log outputs.
- The direct wrapper uses `ALLOW_PATH_SIMPLE_CMD=1` before considering
  `command -v simple`.
- The aggregate Web WM nested run sets `ALLOW_PATH_SIMPLE_CMD=1` so clean jj
  worktrees can use the installed Simple binary without hardcoded host paths.
- The aggregate does not reuse the default `simple-runtime-unavailable` Web WM
  env forever; it reruns the wrapper with the PATH fallback opt-in.

## Related Guide

See `doc/07_guide/tooling/renderdoc_capture_infra.md` for the aggregate GUI
RenderDoc evidence contract and remaining completion gates.
