# Stage 3 `mir_hir_let_type` SIGSEGV and gdb false zero

Date: 2026-08-11  
Status: SOURCE FIX VERIFIED PAST ORIGINAL CRASH; downstream LLVM PHI blocker open

An isolated LLVM stage3 diagnostic consumed approximately 22 GiB RSS and
terminated with SIGSEGV in:

```text
compiler.mir.mir_lowering_stmts.mir_hir_let_type
MirLowering.lower_stmt_impl
MirLowering.lower_stmt
MirLowering.lower_block_expected
MirLowering.lower_function_with_gpu_metadata
```

The retained trace is
`/home/ormastes/dev/pub/simple-stage3-fix-codex/build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-renamed-gdb.log`.
No stage3 executable was produced.

The ad-hoc gdb wrapper wrote status `0` because batch gdb itself exited
successfully after printing the inferior crash. This is not an admitted build
receipt. Any diagnostic wrapper used for promotion must include
`-ex "quit $_exitcode"` or independently require the expected artifact and
scan for signal termination; gdb's process status alone is insufficient.

The retained admitted Stage2 binary contains the symbol
`compiler__mir__mir_lowering_stmts__mir_hir_let_type_value` at `0x6a6a70`.
The crash log's earlier build names the corresponding helper
`mir_hir_let_type` at `0x6a6d00`, immediately after `lower_expr` completed.
The isolated source introduced this helper solely to extract the nullable
second payload of `HirStmtKind.Let(symbol, type_, init)`.  This is therefore
strong evidence for a native enum/nullable-struct payload extraction defect,
not evidence that initializer MIR lowering itself failed.  It is not yet safe
to patch around this by changing language semantics or defaulting every
declared type.

`scripts/check/run-gdb-inferior-strict.shs` now rejects a signalled/nonzero
inferior even when batch gdb returns zero, and optionally requires the expected
executable artifact.  Its unit gate covers normal exit, SIGSEGV, and missing
artifact.

## Corrective repair evidence

The minimized fixture at
`test/fixtures/repro/compiler/nullable_middle_enum_payload/nullable_middle_enum_payload_repro.spl`
covers both nil and present values in the middle payload. MIR Let lowering now
reads the annotation from the already-validated symbol-table entry instead of
extracting that nullable payload again. HIR lowering stores the identical
annotation in both locations, so inferred and explicit declaration semantics
are preserved.

The single corrective native run passed both Let constructions and the former
`mir_hir_let_type` SIGSEGV boundary. It then reached LLVM verification and
failed on a separate malformed PHI (`%l38`, predecessor mismatch).

The earliest broken boundary is textual LLVM emission, not `llvm-as`, bitcode,
or target code generation. MIR's `SsaPhiPlan` retains the complete
`pred_block_ids`/`pred_value_local_ids` lists and encodes every pair in the
`__simple_ssa_phi` arguments. The textual consumer nevertheless read only the
first two pairs (`args[0..3]`). For an N-way join this emitted a plausible PHI
whose incoming list did not match the join's real predecessor set, so LLVM's
verifier correctly rejected it.

`MirToLlvm.emit_ssa_phi_intrinsic` now validates an even pair list, determines
the common type across every value, and renders every predecessor/value arm
through `llvm_phi_incoming_text`. The focused regression covers a three-way
join and rejects mismatched value/predecessor counts. A fresh fixture-only
native LLVM build also runs with `nil=41` and `present=42`; this is focused
diagnostic evidence only. No Stage3 admission or server-build claim is made
until one RSS-bounded Stage3 build produces and verifies its executable.
