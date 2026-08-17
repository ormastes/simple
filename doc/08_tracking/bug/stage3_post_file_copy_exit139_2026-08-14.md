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


## Triage 2026-08-17 — DEFERRED, blocker recorded

Reviewed in the lines 32-46 backlog sweep. Not actionable from this session: requires a full bootstrap (Stage 2 -> Stage 3) to reproduce. This lane is
explicitly forbidden from building the main compiler, and no admitted Stage 2/3
binary exists on this host. The record itself states the driver console was not
retained, so there is no artifact here to analyse either.

**Unblock:** one bootstrap run with the Stage-3 console RETAINED (redirect and
keep `build/bootstrap/logs/<triple>/stage3-native-build.log` plus the driver
stdout). Until a crash site is bound to a hash, exit 139 stays an unretained
observation and no code change is defensible.

Status unchanged. Recorded so future sweeps skip this in O(1) instead of
re-deriving the same blocker.

## Current-source audit 2026-08-17

Status remains **FOCUSED PASS / STAGE 3 VERIFICATION PENDING**. The linked
repair criteria are present in current source and no additional code gap was
found:

- `maybe_copy_array_value` passes only scalar local IDs to
  `copy_local_hir_type_metadata`;
- the `HirType` aggregate is read and copied only inside the aligned metadata
  arrays owned by `MirLowering`;
- missing source IDs and the same `nil`/raw-zero sentinel rejected by
  `find_local_hir_type` return before destination mutation;
- append and update copy isolation and resource state with the type value.

The retained focused fixture and gate remain correctly scoped: append, update,
missing-source, isolation-state, and resource-state behavior are executable,
and the gate binds the production caller/helper plus the admitted compiler's
receipt hash before building the fixture. The 2026-08-16 hashes above remain
the latest positive provenance; they were not replaced by source inspection.

The focused gate was invoked once in this worktree and failed immediately with
`STATUS: FAIL scalar-metadata-copy reason=compiler-missing-or-symlink` because
`build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple` is
absent. No admitted compiler/receipt or bounded Stage-3 resume artifact exists
under `build/bootstrap`, so Stage 3 was not started. No production or test edit
is justified until an admitted artifact can re-run the existing focused gate;
after that passes, run the single materially changed cache-preserving Stage 3
resume required by the unblock condition.
