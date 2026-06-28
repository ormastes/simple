# GUI RenderDoc Feature Coverage SSpec Daemon Timeout

Date: 2026-06-28
Status: open
Owner: rendering verification lane

## Summary

`test/03_system/check/gui_renderdoc_feature_coverage_status_spec.spl` timed out
under the SPipe test daemon during a focused verification pass for Electron
RenderDoc launch diagnostics.

## Evidence

Command:

```sh
SIMPLE_LIB=src bin/simple test \
  test/03_system/check/gui_renderdoc_feature_coverage_status_spec.spl \
  --mode=interpreter --clean --fail-fast
```

Observed output:

```text
ERROR: test daemon timed out: test/03_system/check/gui_renderdoc_feature_coverage_status_spec.spl
```

The same verification pass showed:

- `test/03_system/check/renderdoc_electron_html_gate_spec.spl`: PASS, 11 examples.
- `scripts/check/check-gui-renderdoc-feature-coverage-status.shs`: completed
  and forwarded the Electron gate launch fields plus GPU process exit fields.
- `sh scripts/audit/direct-env-runtime-guard.shs --working`: PASS.

## Impact

The script-level aggregate evidence is available, but the SSpec wrapper is not
reliable enough on this host to use as a release-quality green check.

## Next Step

Profile the SSpec daemon path for this aggregate spec and reduce fixture setup or
daemon timeout pressure without weakening the wrapper contract assertions.
