# Cranelift backend has no `Ref` arm -- MIR shard workers abort in codegen (2026-10-24)

**Symptom.** Phase-3 run-16 (producer `bootstrap-p2shard-9`, source `7d86e04a5ab`,
`SIMPLE_MIR_SHARDING=1 SIMPLE_CODEGEN_MODULE_SCOPE=1`): both MIR shard workers lowered and
claimed every module (735 + 736), then died with SIGABRT in `native_compile`:

```
[cranelift] E-BACKEND-CRANELIFT-INST-Ref: Cranelift backend does not lower Ref
compile error: E-BACKEND-CRANELIFT-INST-Ref: Cranelift backend does not lower Ref
[mir-shard] owner=0/2@0 status=CRASH exit=-134 claimed=735 sealed=735 finished=false
```

**Root cause.** Explicit unary `&x` / `&mut x` lowers to `MirInstKind.Ref`
(`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:5834-5836`). The LLVM backend lowers
it as an identity (`_MirToLlvm/aggregate_intrinsics.spl` `llvm_ref_impl`), but
`cranelift_codegen_adapter.spl` had no arm, so it fell into the catch-all `case _:` that
`panic`s (policy 2026-08-23). The abort does not depend on sharding or codegen scope. Run-16 was
the first phase-3 run whose codegen got far enough to reach a module that uses `&`.

**Coordinator effect.** The seal writes CRASH terminals for every claim. `hir_shard_recovery_can_replace`
then still launches `@1` replacement workers. Those workers reload the full HIR (about 6 GB each),
but they can claim nothing, so the retry is wasted work.

**Fix.** Add a `case Ref(dest, _, place)` arm. It loads `place.local` and stores the value the
same way the `Copy` arm does.

**Workaround without a rebuild.** None is safe. `SIMPLE_ALLOW_UNLOWERED_MIR=1` drops the
instruction and leaves `dest` undefined, which is a miscompile.

**Not covered by this fix.** In the same run, these per-module AOT failures would still block
the link:
- `lean_backend`: verifier argument-count mismatch.
- `cuda_type_mapper`: duplicate definition of `CudaTypeMapper.map_array`.
- `_ParserPrimary.asm_match_suffix`: an imported non-public module static.
- `expr_dispatch`: return signature mismatch.
