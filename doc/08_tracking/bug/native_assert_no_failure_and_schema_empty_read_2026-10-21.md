# Native assertion continuation and empty schema input

Status: OPEN; blocks native diagnostic acceptance and Phase 3.
Producer: bootstrap-r17 stage2, SHA-256
`29dd8539f3fe8e01df9b227e0621b20953fd736e239dafef8bafae8918abb3c2`.

The built `nogc_schema_input_probe` printed `hir_types_exists=true`,
`hir_types_bytes=0`, `source_lines=1`, `nonempty_lines=0`,
`module_headers=0`, `module_offset=-1`, and `hir_type_variants=0`.
Its source asserted bytes >1000, lines >100, one module header and variants >10.
Execution nevertheless reached its success print and exited 0.
Logs: `build/nogc-hardening/schema-input-build.log`, `schema-input-run.log`.
Build: 129.89 s, max RSS 4,947,408 KiB, compile exit0.

The schema CLI also generated zero variants and zero productions with exit0;
codec generation exited1 because HirModule was found zero times. Explicit
SIMPLE_REPO_ROOT did not change the result. Outputs were isolated under build/;
no empty generated output was copied into tracked artifacts.

Root causes of assertion continuation and empty file/session read remain
unconfirmed. Do not assume a successful file_exists proves file_read_result.
Do not accept native test exit0 without proving its failure path.

Mitigation under verification: replace fixture assertions with distinctly named
bool/text guards that print a failure and call io_runtime.exit(1). The dedicated
`nogc_fail_guard_probe.spl` invokes a false guard and must exit1 without its
unreachable marker. Then requalify all affected diagnostics. This mitigation
is not a repair of the language assertion builtin or schema I/O.

## Assertion root cause and mitigation control

Disassembly of the original schema probe showed `rt_alloc(16)`, storage of
(condition, message), then a zero check of the allocation pointer. The flat parser
consumed `assert(condition, message)` as one tuple expression and passed that tuple
as the sole `__assert` argument. This is a parenthesized argument parsing defect,
not evidence that every assertion form is a no-op. Current source now normalizes
parenthesized assertion arguments and has authored parser tests; the r17 producer
itself is unchanged. Direct current-parser execution is pending.

The explicit named failure-guard negative control PASSED: build129.73 s,
4,918,644 KiB max RSS; execution exited exactly1 and its unreachable marker was
absent (`fail-guard-build.log`, `fail-guard-run.log`). All affected native fixtures
now use distinct named bool/text guards with explicit exit1. Guarded requalification
is underway; no earlier assertion-only acceptance claim is restored by this control.

## Confirmed file-open ABI root cause

The guarded input probe, after the packed-byte codegen repair, compiled and exited1
with `failed to open` for the existing HIR source. Disassembly proves a real
three-word provider at0x23500: x0 pointer, x1 length, x2 mode. Its facade at0x15c10
called rt_interp_cstr, moved semantic mode to x1 and branched at0x15c20 without
setting x2. Read mode0 therefore became path length0. The pure text-extern table
was missing rt_io_file_open/exists/delete, although the Rust twin already lists
them. Pure table rows and semantic arities are now repaired; the unchanged r17
producer still embeds the old table, so full source/runtime qualification awaits
a rebuilt producer. This is distinct from the parenthesized assertion bug.
