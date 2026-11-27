# CUDA optimizer dependency surface ownership

Status: FIX-IMPLEMENTED-VERIFICATION-PENDING (2026-11-22). Owner imports removed; the native CUDA port closure passes HIR 514/514 without them. Remaining verification: the next Phase 3 full-CLI bootstrap build whose source contains this removal (inline, loop_opt, loop_licm and auto_vectorize_cost are compiler modules, so that build compiles them).

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

## Bootstrap repro/prevention 2026-11-05
Spec: test/01_unit/compiler/mir_opt/cuda_optimizer_owner_imports_spec.spl (owners + 4 optimizer modules import together; passes on seed). Status: verification-pending; retire the explicit imports only after a stage3 producer compiles the CUDA closure without them.

## 2026-11-10 P2 triage (lane p2-compiler-triage-20261110)

VERDICT: LIVE, blocked on native closure grant. Workaround still required and
pinned on current source: explicit owner imports at
60.mir_opt/mir_opt/inline.spl:4 (mir_types.LocalId), loop_opt.spl:9,
loop_licm.spl:8, auto_vectorize_cost.spl:8 (mir_instruction_support.BlockId);
@workaround tag at auto_vectorize_cost.spl:7. Retained specs green on the
deployed seed (interpreter): cuda_optimizer_owner_imports_spec.spl 2/2,
call_terminator_unwind_destinations_spec.spl 4/4. The underlying native
MIR-lowering SIGSEGV (exit 139 after HIR 157/157) remains unresolved; per b519
triage no current producer trace exists. Cycles: 1. Grant command recorded in
build/review/p2fix-compiler-20261110.sdn.

## 2026-11-11 triage (lane p3fix-p2a-20261111) — LIVE; evidence gate repaired, workaround pins re-verified

Re-verified at release/1.0.0 tip (worktree @ 79d5af6723f6, deployed seed
bin/simple.exe @ 46fe8f6b6def):

- **Workaround pins still required and present**: inline.spl:3-4
  (`@workaround` + `use compiler.mir.mir_types.{LocalId}`),
  auto_vectorize_cost.spl:7-8 (`@workaround` +
  `use compiler.mir.mir_instruction_support.{BlockId}`), loop_opt.spl:9,
  loop_licm.spl:8. The 2026-11-07 hir-nominal-generic-owner merge did NOT
  retire them; no owner-projection fix commit found
  (`git log --grep` over all refs: only this bug's own triage commits).
- **Regression spec repaired (was RED at tip on the pinned seed).**
  `call_terminator_unwind_destinations_spec.spl` ERRORed with 0 executed:
  the 2026-11-10 20:55 seed refresh (f919ff81626d → 46fe8f6b6def) includes
  the 11-09 seed visibility fix 6d15331f91eb ("error on cross-directory call
  of a private fn"), and the spec's imported constructors/analyzers were
  private: `copypropagation_new`, `copypropagation_propagate_terminator`
  (copy_prop.spl) and `get_terminator_successors`, `get_terminator_uses`,
  `_outline_get_inst_uses` (outline.spl). The 11-10 "4/4 green" was on the
  pre-refresh seed whose glob/no-import leak allowed the private calls.
  Fix: mark those five fns `pub` (visibility-only widening, no behavior
  change). Spec now 4/4 PASS on the pinned seed; sibling
  `cuda_optimizer_owner_imports_spec.spl` re-verified 2/2 PASS.
- **Verdict: LIVE**, consistent with 2026-11-10: the workaround can be
  retired only after a stage3-admitted producer compiles the actual CUDA
  closure without the owner imports. Grant command (verbatim, from
  build/review/p2fix-compiler-20261110.sdn):
  `SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_SCV_INVENTORY_COLD_INIT=1 bin/simple native-build --source src/compiler --source src/app --source src/lib --source src/plugins/backend_cuda --source src/compositions/kernel_llvm_cranelift --entry-closure --entry src/plugins/backend_cuda/cuda_backend.spl --threads 10 --cache-dir build/native_probe/cuda-compile/plugin-mono-symbol-cache --output build/native_probe/cuda-compile/plugin`
  — blocked here: no stage3-admitted producer / self-hosted check worker on
  this host (policy: no heavy entry-closure builds from bug lanes), and the
  closure still SIGSEGVs at MIR lowering per the bounded evidence above.

## 2026-11-22 verification (lane work/cuda-compiler-bugs) — workaround removed, verification pending

Producer: integ25 Stage 2 admitted native-build
(`.../bootstrap-s2probe-integ25/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple`,
sha256 `ef46f0d2ab4274c4550530851db407bf9bad7f21bfabd50f9b56e87e77fd58d6`,
runtime `stage2-runtime-authority`), host Linux aarch64 (GB10), base
`origin/release/1.0.0` `3c2e4556b6d`.

Failing-first probe: deleted the explicit owner imports and their `@workaround`
tags (inline.spl `LocalId`; loop_opt.spl, loop_licm.spl,
auto_vectorize_cost.spl `BlockId`; and, for sibling
`cuda_port_imported_method_surface_type_owner_2026_10_16`,
cuda_backend_port.spl `MirType, MirSignature`). Each symbol appeared only in
its import line. Then native-built the fixture
`test/native/cuda_compiler_bugs/port_owner/main.spl` (imports
`plugins.backend_cuda.cuda_backend_port`, so the closure covers CudaBackend and
the four optimizer modules):

```
SIMPLE_BOOTSTRAP=1 SIMPLE_NATIVE_GO_TO_END=1 SIMPLE_FILE_WORKERS=0 SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1 \
  systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 <stage2> native-build \
  --source src/compiler --source src/app --source src/lib --source src/plugins/backend_cuda \
  --source src/compositions/kernel_llvm_cranelift --source test/native/cuda_compiler_bugs/port_owner \
  --entry-closure --entry test/native/cuda_compiler_bugs/port_owner/main.spl --runtime-path <stage2-runtime-authority> ...
```

Result: entry closure 514 modules; **HIR 514/514, failed=0**, including
`compiler.mir_opt.{inline,loop_opt,loop_licm,auto_vectorize_cost}` and
`plugins.backend_cuda.cuda_backend_port`; no `LocalId`/`BlockId`/`MirType`
diagnostic anywhere in the log. The defect this record tracks (HIR rejecting
imported payload types) does not reproduce, so the workaround imports are
removed. The build was then OOM-killed by the lane's 8 GiB cgroup cap during
whole-program MIR (`[mir] 200/514 rss_mib=5670`, systemd `oom-kill`), so no
binary was produced; the old MIR SIGSEGV is NOT re-assessed by this run. A
full link needs a run without the 8 GiB cap.
`cuda_optimizer_owner_imports_spec.spl` docstring updated (still imports the
owners directly, which is its purpose).

Negative control (same producer, env and flags): a fixture with `fn take(x: NoSuchOwnerType)` fails HIR with `[ERROR] HIR lowering error ... unresolved type: NoSuchOwnerType` (build rc=1). So `failed=0` on the 514-module closure is evidence that can fail, not a vacuous pass.
Importer audit: no file under src/ or test/ that imports the four optimizer modules or `cuda_backend_port` names `LocalId`, `BlockId`, `MirType` or `MirSignature` without the owner import. The only matches are commented-out code in `mir_opt_spec.spl` and the intentional `mir_owner_adapter/cuda_adapter_import_only.spl` fixture.
**Residual crash:** the 2026-10-10 CUDA-closure crash at MIR entry (SIGSEGV, exit 139) is now filed as `native_build_mir_entry_sigsegv_cuda_backend_closure_2026-10-10`.

## 2026-11-22 follow-up: 20 GiB run (coordinator-approved) — no binary; cgroup-dependent compiler SIGSEGV

Each run used the same Stage 2 (`ef46f0d2...`) and `stage2-runtime-authority`, with
`systemd-run --user --scope -p MemoryMax=20G -p MemorySwapMax=0`, launched serially
only when MemAvailable was at least 45 GiB (actual 63-70 GiB). Peak RSS comes from
`/usr/bin/time -v`.

| run | config | result | peak RSS |
|-----|--------|--------|----------|
| fx12b | 20G, default threads (HIR worker pool sized to 1) | SIGSEGV (worker exit -139, build rc 117) at HIR 82/514 | 4.01 GB |
| fx12c | 20G, `--threads 1` | SIGSEGV at HIR 82/514 | 4.01 GB |
| fx12d | 20G, `SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB=8388608` (HIR in-process, threads=0, same as the 8G run) | SIGSEGV at HIR 82/514 | 4.01 GB |
| fx12e | control: original 8G command, unchanged | passed HIR 82 and reached 202/514 (stopped deliberately) | n/a |

The original 8G run (`fx12`) got through HIR 514/514. Only the cgroup
`memory.max` differs, so the crash is triggered by the cgroup cap, not by
memory pressure. In the 20G runs the HIR module order diverges right after
`lib.nogc_sync_mut.io.process_ops` (it goes to `compiler.mir_opt.perf_facts`
instead of `lib.nogc_sync_mut.sffi.runtime`), and the crash follows.

A crash report exists at
`/var/crash/_home_yoon_dev_simple-integ5-20261116_..._stage2-admitted_simple.1000.crash`.
Filed as `native_build_hir_sigsegv_under_20g_cgroup_cuda_port_closure_2026-11-22`.

Result: still no linked binary.
- Bugs 1 and 2 keep the HIR 514/514 evidence from the 8G run (with the negative control).
- End-to-end (link + run) evidence is blocked between the 8G OOM at MIR 200/514
  and the 20G HIR SIGSEGV at 82/514.
- The bug 3 fixture was not run, since the success of this run was its precondition.

## 2026-11-22 status correction (review P2)

The retirement criterion was "the CUDA closure compiles without them". That has
not happened yet: the build OOMs at MIR 200/514 under 8G, and SIGSEGVs at HIR
82/514 under 20G. So the status is `fix-implemented-verification-pending`, not
`resolved-disappeared`. The import removal is kept.

To close, either of these must succeed:
- the next Phase 3 full-CLI bootstrap build whose source contains this removal; or
- a native link and run of `test/native/cuda_compiler_bugs/port_owner`, whose
  stdout must match `expected_output.txt`.
