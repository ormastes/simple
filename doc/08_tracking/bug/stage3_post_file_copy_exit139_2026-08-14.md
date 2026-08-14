# Stage 3 downstream high-memory exit 139

Date: 2026-08-14
Status: OPEN / BLOCKED
Owner: compiler MIR module/function lowering
Source frontier: `src/compiler/50.mir/_MirLowering/function_lowering.spl`

## Evidence

After the `runtime_error` static-owner repair, the admitted Stage 2 build passed
the former receiver-corruption frontier. Cycle 2 ended after lowering
`dir_create_all` and `file_copy`; the final guarded Cycle 3 ended while entering
statement 1 of `eval_binop`. Both exited 139 near the prior high-memory region
without a symbolized diagnostic, so neither function name is yet a proven
root cause. Final log SHA-256:
`51877e1e469e9504934b68097db3a8250bbf85f666247aa652e3e1c676606a5b`.

This is a new downstream frontier. The repaired run contains none of the old
`runtime_error`, impossible receiver-local, or unsupported-expression markers.

## Unblock condition

Capture a symbolized native backtrace plus peak-RSS evidence, or add a bounded
transition trace that identifies the shared operation behind the varying
`file_copy`/`eval_binop` terminal frontiers. Reduce that operation to a
candidate-bound fixture, repair its smallest owner, then resume the existing
Stage 3 cache in a fresh lane with a materially changed source identity. This
lane consumed all three cycles; do not retry here or use the Rust seed as
acceptance authority.
