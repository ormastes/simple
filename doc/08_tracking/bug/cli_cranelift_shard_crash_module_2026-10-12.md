# compiler_cli_build shard crash — module identification attempt (2026-10-12)

## The crash

The phase-2 matrix `compiler_cli_build` row's HIR shard dies at startup with
a macOS SIGABRT (crash report `compiler.snapshot-2026-10-12-040049.ips`):

```
__pthread_kill / pthread_kill / abort / std::process::abort
rt_panic
cranelift_codegen_adapter.cl_translate_instruction
cranelift_codegen_adapter.compile_function
CraneliftCodegenAdapter.compile_module
static_backend_cranelift_port._cranelift_run
```

The shard ledger records `claimed=0, failed_modules=0` and the panic text is
swallowed (the matrix harness does not capture worker stderr), so the
unlowered-instruction NAME — which the panic message carries
(`E-BACKEND-CRANELIFT-INST-<kind>`) — was not directly recoverable from the
matrix artifacts.

## Bisection methodology and results

Binary: the matrix's `compiler.snapshot` (mtime 2026-10-12 03:48) copied to
/tmp (the co-owned worktree was execute-only throughout). Method:
per-module `native-build --emit-object --backend=cranelift --threads 1`
(single-module compiles lower only the entry module's MIR under the
bootstrap-flat lane, so a module that aborts ALONE is the target).

| module | result |
|---|---|
| lib/nogc_sync_mut/rt_hal/parallel_executor.spl | rc=1, 6 unresolved-method errors (the known fn-field family) — NO abort |
| 70.backend/backend/native/mach_inst.spl | rc=1, ordinary MIR errors (module-static annotations) — NO abort |
| 70.backend/backend/llvm_ir_types.spl | path absent at this vintage (renamed upstream) |
| 70.backend/backend/cranelift_codegen_adapter.spl | in progress at budget cap (HIR ~40 min cold; not verdicted) |
| 70.backend/backend/cranelift_gemm_fusion.spl | in progress at budget cap (reached MIR phase) — no abort observed |
| 50.mir/_MirLoweringExpr/{method_calls_literals,enum_constructor_payload,expr_dispatch}.spl | in progress at budget cap |

No per-module run SIGABRTed within the time budget. Compiler-module closures
are ~180-340 modules with cold caches (~30-60 min each single-threaded), so
the coarse pass could not verdict all candidates.

## Full-closure reproduction attempts (all failed EARLIER than the crash)

Reproducing the matrix's exact closure
(`--source src/compiler src/app src/lib src/os src/plugins src/compositions`,
entry `src/app/cli/_CliMain/main_and_help.spl`, sources pinned to the
snapshot's vintage 40b5bfee423 via a scratch worktree of an unrelated repo
checkout) three times:

- WITHOUT `src/os`: fails at source-closure (`os.*` imports unresolved) —
  the mission-stated source set omits `src/os`, but the cli closure requires
  it (the lane's own invocations include it or equivalent roots).
- WITH `src/os`, sources at the snapshot's exact vintage: HIR shard reports
  POISONED modules (`arch_rules.spl` missing predicate surfaces,
  `bidirectional_checking.spl` 88 unresolved-name errors, `pci.spl`
  `_pci_ecam_base`) and ends "HIR aggregate failure" (exit=1) in ~100 s —
  the matrix's shard recorded `failed_modules=0` at the same vintage.

Conclusion: the crash is NOT reproducible standalone — the lane's full
driver environment (the `bootstrap-phase-verification.shs` wrapper's env:
ABI policy, recovery/collect-all diagnostics switches, warm lane caches,
`--backend=llvm --low-memory`, and the shard-worker protocol) is required
for HIR to reach the clean state the matrix enjoyed before the panic. The
panic text and the crashing module are therefore only obtainable from a lane
that replicates that environment (or instruments it).

## Classification

**Most probable: (a) a symptom of the same seed-native divergence
(#3213).** Evidence: (1) the crash binary is seed-natively compiled; the
divergence is proven to corrupt native-lane lowering state
(registry/metadata), which can manufacture MIR the backend has no lowering
for — `cl_translate_instruction`'s catch-all panic is exactly where a
corrupted-instruction lands; (2) the identical stack occurred on 2026-10-11
(hmac closure) where the root cause turned out to be module-static shapes
that the SOURCES have since fixed (#3090) — i.e. this stack has history of
being a source-shape issue that a source fix clears, and of being a
divergence artifact that no source fix should chase; (3) the matrix's
`failed_modules=0` means HIR was clean, so the unlowerable instruction
appears during MIR/codegen — the same phase the divergence corrupts.

**(b) a genuine unsupported MIR op** cannot be ruled out without the panic
text; the identification path is: re-run the lane with worker-stderr capture
(or `SIMPLE_ALLOW_UNLOWERED_MIR=1`, which prints every unlowered
instruction's NAME and continues) — one flag run names both the instruction
kind and, via the driver's current-module receipts, the module.

## Recommended next steps (lane owners)

1. Re-run `compiler_cli_build` with `SIMPLE_ALLOW_UNLOWERED_MIR=1` in the
   shard worker env (or fix the harness to retain worker stderr) — the
   `E-BACKEND-CRANELIFT-INST-<name>` lines name the construct directly.
2. If the named instruction is a genuine gap, implement it in
   `cl_translate_instruction` following the existing arms; if the MIR looks
   corrupted (impossible operand/type shapes), route to the seed-codegen
   lane per #3213.
3. Cache-warmed per-module bisection (one full-closure build first, then
   `--emit-object` per module reuses the HIR cache) remains the fallback to
   name the module without the lane.
