<!-- codex-design -->

# Browser WASM WebGPU Infra TUI Design

This feature has no end-user terminal UI. Terminal-visible behavior is limited
to SPipe and evidence command output.

## Operator Output

Specs should expose concise status lines in generated manuals:

- BrowserSession script/WASM specs show module counts, statuses, body/title
  state, and deterministic warnings.
- Chrome evidence specs show `status`, `backend_target`, `source_format`,
  output/readback counts, and mismatch counts.
- Compiler/codegen specs show target ordering, WebGPU opt-in, WGSL/source-only
  format, and host-import diagnostics.

## Capture Policy

No TUI screenshots are required. Generated `doc/06_spec` manuals are the
operator-facing artifact. Hardware or browser probe logs may be linked as text
or JSON evidence only when produced by explicit evidence wrappers.

