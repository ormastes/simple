# CUDA optimizer dependency surface ownership

Status: OPEN compiler defect; explicit owner-import workaround passes actual CUDA HIR.

On release/1.0 `c48d5fb07cc5d75777c63252f2e0659b9bd8e248`, native compilation
of `src/plugins/backend_cuda/cuda_backend.spl` reaches HIR but rejects imported
payload types in `inline.spl` (`LocalId`) and `loop_opt.spl`, `loop_licm.spl`,
`auto_vectorize_cost.spl` (`BlockId`). These callers import structures or
re-export functions whose signatures contain the types; their declared owners
are `compiler.mir.mir_types` and `compiler.mir.mir_instruction_support`.
The workaround imports those owners explicitly without changing transforms.
Remove the imports after native imported-surface projection preserves ownership
and the actual CUDA closure compiles without them.

Producer: unadmitted pure-Simple explicit-call-types diagnostic candidate,
SHA-256 `72b495b3f2cbb72b3a1f8c6bf01e7962a4d38fda17d905a2c7a0e004c066c6a5`.
Evidence: `build/native_probe/cuda-compile/plugin-native-fixed.log` in the
isolated `simple-astra-cuda-compile-20261010` worktree. This run cleared the
repaired CallTerminator patterns but failed five HIR modules, including the
independently stale two-field `Send` pattern in `outline.spl`.

Separate source defects repaired in this lane: CallTerminator has seven fields,
so copy propagation must preserve `unwind_payload_dest` and
`unwind_type_tag_dest`; successor/use analyses ignore them as definitions.
Send has three fields, and its result destination is not an operand use.
Regression specification:
`test/01_unit/compiler/mir_opt/call_terminator_unwind_destinations_spec.spl`.
Its runtime execution requires a qualified full test runner and is pending.

This report does not claim CUDA execution, an aggregate compiler bootstrap PASS,
or ARM/RISC-V object/runtime qualification.

## Bounded verification evidence

- Final native HIR: **157/157 PASS**, ten completed workers, zero failed modules,
  zero unfinished records. The actual plugin CUDA module has a `CACHE_STORED`
  PASS record. Ledger: `build/native_probe/cuda-compile/plugin-mono-symbol-cache/default/frontend/queue-776027-0`.
  Frozen source snapshot: `8ba15b1d4baff5c3190c2f7509a87684a1c41273a713532838c4a7b248792df7`.
- Native build log: `build/native_probe/cuda-compile/plugin-native-final-scoped.log`.
  The producer SHA is pinned above; it remains an unadmitted diagnostic tool.
  Final result: exit **117**, worker **SIGSEGV/-139** during MIR lowering,
  after monomorphization reported 2 generic functions, 24 calls, 9
  specializations, and 0 unresolved. No binary was produced. Three scoped
  compile cycles are exhausted; this remaining compiler crash is handed off,
  not retried. RISC-V codegen cannot be qualified past this shared MIR crash.
- Independent SMF path with named-variant producer SHA-256
  `8288ec48e1ee0ef92273a9e42c8faf97bfed80c252298e863f091d0761e5147d`:
  HIR completed, generic functions=2, call sites=24, specializations=9,
  unresolved=0; then SIGSEGV (exit 139) entering MIR lowering. Log:
  `build/native_probe/cuda-compile/plugin-smf-final.log`. No artifact PASS.
- Source-layout gate: zero `*_spec.spl` under `doc/06_spec`.
- Working and staged direct-env-runtime guards: PASS. These changes add no environment or
  process calls. Regression SSpec runtime and broad compiler/lib/MCP checks are
  pending a qualified full test/check CLI; the available native producer offers
  only compile/native-build.

Reproduction uses `SIMPLE_NO_STUB_FALLBACK=1`,
`SIMPLE_SCV_INVENTORY_COLD_INIT=1`, and the pinned producer's `native-build` with
`--source src/compiler --source src/app --source src/lib
--source src/plugins/backend_cuda --source src/compositions/kernel_llvm_cranelift
--entry-closure --entry src/plugins/backend_cuda/cuda_backend.spl --threads 10
--cache-dir build/native_probe/cuda-compile/plugin-mono-symbol-cache
--runtime-path /home/yoon/dev/simple-release-1.0-codex/src/compiler_rust/target/bootstrap
--output build/native_probe/cuda-compile/plugin`.

Pre-compile attempts also exposed snapshot-index drift when comments changed
during inventory admission, the producer's unsupported
`--refresh-source-authority` option, and an existing malformed workaround marker
at the top of `auto_vectorize_cost.spl`. Sources were frozen before the final
run; that existing marker now immediately precedes its affected OR-pattern arm.
The canonical bug database reports pending WAL checkpoint before workaround
refresh; its database/index was not modified by this lane.
