# Item 6 Phase 2 diagnostic — 2026-10-10

**STATUS: BLOCKED for feature verification.** This report records two actual
compiler invocations, not successful executable acceptance or release readiness.
The implementation from PR #2310 is already merged; this report changes no code.

## Source and ownership

Release baseline: `f92764f2b97f99de8b60db2d454208de55564be2`.
Isolated worktree: `C:/dev/simple-item6-phase2-verify-owner-20261010`.
Other active item-6 and bootstrap worktrees were not changed. The user requested
a smaller model: GPT-6 Luna performed read-only provenance/source review; the
primary agent checked its findings against receipts, hashes and source.

Entrypoint: `src/app/test/package_index_acceptance.spl`.
SHA256: `0881c0716d41acc61564035f22ed9a1a5b436424c515de9679e15fdb6cdab669`.

## Compiler evidence

The `rel-p3run` Phase 2 provenance and sanity receipts bind compiler
`49cbd0052706c055d16e9e36c98ac138f70ce228e24c4d081c48da134bc9eb7e`.
Its current stage2 executable instead hashes to
`5d97a3dc32147a3dc002ebafde549f07979966eafffdff0ffb3f22cbedadded2`.
Do not transfer the old receipts to that executable.

The diagnostic used the hash-matching preserved compiler:
`C:/dev/simple-bootstrap-storage/rel-p3run/build/bootstrap/phase2-runtime-capsules/49cbd0052706c055d16e9e36c98ac138f70ce228e24c4d081c48da134bc9eb7e/simple.exe`.
The matching archived admission is under
`stage3/x86_64-pc-windows-msvc/stage2-admitted.prior-attempt-20261010T043511-2238089/`.
Its original absolute evidence paths are not a freshly replayed admission.
This historical pure-Simple candidate is diagnostic-only for this source revision.
The separate `rel-s2rebuild/frozen/simple.exe` hash `b0e786...566c` has runtime
capsule metadata but no matching provenance/sanity receipt found in the audited
tree; it was not substituted.

## Executed checks

Both calls used LLVM, one worker, object output, `core-c-bootstrap`,
`SIMPLE_NO_STUB_FALLBACK=1`, and cold SCV inventory initialization. Each native
Windows job collector bounded logs to 4 MiB and execution to 180 seconds.

| Invocation | Observed result |
|---|---|
| Relative entry path | Exit 1: source loader reported zero source files; no object |
| Absolute entry plus explicit compiler/app/lib roots and entry closure | Timeout 124; collector cleanup `reaped`; SCV snapshot reached; last logged parse progress 145/672, zero cached; no object |

Second compiler argv, with the verified executable as `<compiler>`:

```text
<compiler> native-build C:/dev/simple-item6-phase2-verify-owner-20261010/src/app/test/package_index_acceptance.spl --source src/compiler --source src/app --source src/lib --entry-closure --emit-object --backend=llvm --threads 1 --cache-dir build/native_probe/item6-phase2-check/cache -o build/native_probe/item6-phase2-check/acceptance.o
```

Local evidence directory: `build/native_probe/item6-phase2-check/`.
`compile.log` SHA256:
`08dcd8d3d08d5737048d28161f5ec024d78f33c2b09df43241f886ac3d5ad284`.
`compile-absolute.log` SHA256:
`f67c73fe2f916ebdb8a3328db59e366c6c76ea91352abe908f96b4eb69b15827`.
Matching `.receipt` files retain native exit/timeout and cleanup results.
Collector wall time includes startup/inventory work; logged parse elapsed time
is not the entire invocation duration. No test suite or full 44-scenario contract
passed, and no performance target is established by this timeout.

## Remaining work

- Replay complete admission for the exact compiler/runtime, provide sufficient
  disk headroom, and resume the preserved cache with a justified compile budget.
- Build the acceptance binary and test runner, then execute owner and system
  scenarios separately. Do not treat owner observations as whole-compiler PASS.
- Stable root authority remains unresolved: `cold_full_index_producer_v1.spl`
  supplies `snapshot.tree_id` as root-generation input. Conservative invalidation
  remains necessary across incompatible roots.
- `cold_hir_compiled_package_outputs_v1.spl` still supplies declaration and receipt
  from the same artifact. `generated_source_receipt.spl` validates consistency;
  independent selected-build-plan authorization remains required.

No authority check, test assertion, cache identity or admission requirement was
weakened to obtain this evidence. Full runtime, crash, performance and cross-mode
verification remains outstanding.
