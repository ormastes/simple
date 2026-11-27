# Generated RV64 RTL bundle fails its own debuggability lint (2026-10-30)

Status: open
Area: lib/hardware/fpga_linux/riscv_fpga_linux (generator), compiler/35.semantics/lint/riscv_rtl_debuggability_lint.spl

## Symptom

In `test/01_unit/compiler/lint/riscv_rtl_debuggability_spec.spl`, 3 of 14 examples fail with
`expected true to equal false`:

- accepts clean generated RV64 debug sidecars
- accepts sidecars with non-canonical whitespace
- accepts board boot products manifests with reordered acceptance markers and relaxed spacing

In each case, linting the core from `generate_default_riscv_fpga_rtl_bundle` reports at least one
RTLDBG001, RTLDBG002 or RTLDBG003 finding. The 11 drift and negative examples pass.

The spec could not run at all before PR #5447. The 2026-09-29 transplant had renamed its helper
without updating the call sites.

## Notes

- The run takes about 390 s on the seed interpreter.
- A side finding: a spec-local `fn shell` is shadowed by the std `shell(text) -> ProcessResult`.
  A local definition should win over an imported one.

## Unblock

Identify which RTLDBG code fires on the clean bundle. Then fix the generator's sidecar/manifest
output, or the lint's acceptance of it, and remove the `pending` markers that link here.
