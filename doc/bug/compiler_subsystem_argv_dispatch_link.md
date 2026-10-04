# Argument-only compiled products pull optional CLI dispatch providers

Source baseline: `b1668eac56919dc6c48a3dfece87333c51683eb5`.

The subsystem generator, main-verdict tool, and generated aggregate entry import
`cli_get_args` from `std.sffi.cli`. Native module closure retains that module's
optional `rt_cli_*` dispatch externs. A core-runtime native fixture using this
same import failed linking with 35 unavailable dispatch symbols, before any
test could execute. This is distinct from the HTTP client link-owner defect.

Move the unchanged `sys_get_args` wrapper and three argument helpers into
`std.nogc_sync_mut.sffi.cli_args`, retain the old facade exports, and expose
`std.sffi.cli_args` for argument-only callers. The sync runtime boundary and
out-of-range empty-text behavior remain unchanged. No missing dispatch provider
is replaced with a stub.

## Verification

`test/04_smoke/cli_args_native_probe.spl` checks count/array agreement, executable
argument access, negative/end/large indexes, and plain/spaced/Unicode arguments.
Compile with the actual Phase 2 producer and core runtime, then invoke with
`plain`, `two words`, and `한글` as three arguments. Require the real output
`CLI args: 8 checks, 0 failures` and exit zero. Also build and run the subsystem
generator, verdict tool, and rendered aggregate products; the smoke alone does
not establish that those full closures link.

Native execution is pending. The live bootstrap source is not modified by this
isolated candidate. Record producer/backend/runtime identities and actual
results before claiming a pass.
