# Stage 3 bootstrap real-LLVM entry IR loads imported globals it never declares

- Status: OPEN
- Date: 2026-10-20
- Platform: aarch64-unknown-linux-gnu
- Severity: P2 (blocks any bootstrap entry that reads an imported `pub val`)

## Observation

A probe Stage 3 (diagnostic relink `s2diag17`, tree 44a4b94ae95) whose
entry `bootstrap_main.spl` reads `PROBE_GLOBAL` (from
`app.cli.closure_probe_types`) and `BLOCK_STORED` (from
`std.nogc_sync_mut.compression.gzip.types`) lowered MIR with 0 errors, then
`llc` rejected the entry IR:

```
error: use of undefined value '@g_app_cli_closure_probe_types__PROBE_GLOBAL'
  %l9 = load i64, ptr @g_app_cli_closure_probe_types__PROBE_GLOBAL, align 8
```

The IR loads both `@g_app_cli_closure_probe_types__PROBE_GLOBAL` and
`@g_lib_nogc_sync_mut_compression_gzip_types__BLOCK_STORED` and defines or
declares neither. `[bootstrap-real-llvm] statics 2`: both statics are
external.

## Cause

`emit_bootstrap_statics` (src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl)
skips every `bootstrap_mir_static_external_at(index)` row on the assumption
that "aggregate bootstrap IR contains the provider definition". The probe's
entry IR does not contain the closure modules: their functions appear only
as `declare`. The normal codegen path emits `@g_X = external global <ty>`
for the same case.

## Reach

The real `src/app/cli/bootstrap_main.spl` imports only functions and types
and declares no module-level `val`/`var`, so its entry IR does not hit this.
Whether closure-module IR goes through this path is shown by the full
diagnostic Stage 3.

## Fix direction

Emit `@g_<name> = external global <ty>` for external rows (deduplicated)
instead of skipping them, matching the normal path.
