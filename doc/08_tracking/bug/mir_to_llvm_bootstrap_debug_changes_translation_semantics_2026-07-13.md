# MIR-to-LLVM bootstrap debug changes translation semantics
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Symptom

Setting `SIMPLE_BOOTSTRAP_DEBUG=1` does more than enable diagnostics. In
`MirToLlvm.translate_module` it selects the bootstrap-global function registry,
changes function emission, and suppresses TBAA. On the SimpleOS filesystem
compiler this path faults in `bootstrap_mir_function_count+0x18` because that
registry is not initialized for the normal module translation path.

## Required fix

Separate diagnostic output from translation mode. A debug flag must not change
function sources, emitted bodies, or metadata. Keep any deliberate bootstrap
translation mode behind a separately named, explicit mode flag.

## Regression gate

Translate the same MIR module with diagnostics off and on. Require identical
LLVM IR after removing diagnostic output, and require the same function count
and body sources in both runs.

## 2026-10-10 pure-Simple reproduction

Still **OPEN**. Producer
`/dev/shm/simple-phase2-latest-ord-20261010/build/simple` (source
`a0e3b4ff2b7aa8e3d4b7c9accc83bfc8c897dbf4`) compiled a ten-line byte-status
fixture from isolated source `c6f5fc3f5643cea498d860189fc33445a971b293` plus
the fixture. Both bootstrap-flat and normal-AOT object probes with
`SIMPLE_BOOTSTRAP_DEBUG=1` exited zero but produced a 504-byte ELF containing
only null and FILE symbols, no function. Normal-AOT tracing recorded
`lower_to_mir ... functions=1` and completed borrow checking before emission.

Evidence is retained under
`/home/ormastes/simple-astra-cast-evidence-20261010/`: `byte-owned.log`,
`byte.o`, `byte-full.log`, `byte-full.o`, and `fixture/byte_status.spl`.
`readelf -s byte-full.o` independently confirms the missing function symbols.
These diagnostic artifacts are not compilation correctness PASS evidence.

The source owner remains
`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`:
`translate_module_with_entry_policy` selects its function registry using
`bootstrap_debug`, not the normal MIR module. Without
`SIMPLE_BOOTSTRAP_REAL_LLVM=1`, the same branch also emits synthetic
`ret i64 0` bodies when the bootstrap registry is populated. The diagnostic
toggle therefore must not be used to attribute an ordinary compile result.

