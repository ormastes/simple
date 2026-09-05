# Stage 3 downstream high-memory exit 139

Date: 2026-08-14
Status: FOCUSED PASS / STAGE 3 VERIFICATION PENDING
Owner: compiler MIR local HIR metadata
Source: `src/compiler/50.mir/mir_lowering_types.spl:414`

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

## Symbolized root cause

A fresh admitted-Stage-2 run under GDB captured SIGSEGV with this exact stack:

1. `MirLowering.remember_local_hir_type`
2. `MirLowering.maybe_copy_array_value`
3. `MirLowering.lower_stmt_impl`
4. `MirLowering.lower_block_expected`

The crash occurs on statement 1 of `eval_binop`. `maybe_copy_array_value`
retrieved a `HirType` aggregate and passed it into another native method. Under
the Stage 2 ABI that aggregate transport corrupts the callee, matching the
already-proven static-receiver class. GDB log:
`build/native_probe/stage3-gdb/gdb.log`, SHA-256
`25f6fb3c1cf8585ed0bfee4c589386e2cc89dff8c60e74d9eab652719d6064ab`.

The repair adds `copy_local_hir_type_metadata(source_id, destination_id)`, whose
arguments are scalar and which copies the aggregate only inside the owning
aligned arrays. It rejects the same nil/raw-zero sentinel as
`find_local_hir_type` before mutating the destination.

On 2026-08-16, `sh scripts/check/check-native-scalar-metadata-copy.shs` passed
once with admitted pure-Simple Stage 2 SHA-256
`f879f1bd1116cb8ac8fe04fdeff278a5dbc01821b993ace5bce3b16b96167218`.
The source-bound native fixture proves append, update, missing-source,
isolation-state, and resource-state behavior. Retained build/run log SHA-256:
`ca75a6820599c35df0b69d23367bd2a5eb1ec807a41fc92ecb071e95f0bfde24` /
`d2cc0ff5f73a1a44d26603310738107eebcccd0a050ff62a57ec424195159add`.
This is focused Stage-2 evidence only; Stage 3 verification remains pending.

## Unblock condition

Run the materially changed cache-preserving Stage 3 build once. It must pass
the symbolized `remember_local_hir_type` frontier and produce an admitted
candidate; then run Stage 4 and the essential-tools gates. Do not use the Rust
seed as acceptance authority.
