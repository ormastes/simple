# CUDA port imported method surface loses MIR type owners

Status: FIX-IMPLEMENTED-VERIFICATION-PENDING (2026-11-22). Workaround import removed; HIR passes without it. Remaining verification: the next Phase 3 full-CLI build whose source contains this removal, or a native link and run of test/native/cuda_compiler_bugs/port_owner.
Canonical bug DB reconciliation is pending: the qualified database CLI is not
available in this diagnostic lane. Bug identifier:
`cuda_port_imported_method_surface_type_owner_2026_10_16`.

Phase 3 cycle 2 used source `1e93dca4ce3d7be2187da1b67cfeb1180179682e`
and pure-Simple producer SHA256
`a174b8e70b0a0ea4531db2ac5b8553f216590a7fbad0567cd9e40fd8e4630994`.
Its real HIR fatal ledger marks `plugins.backend_cuda.cuda_backend_port`
FAILED/UNCACHED with 28 errors. The first ten printed errors are nine
`unresolved type: MirType` and one `unresolved type: MirSignature`.
These are terminal diagnostics, unlike neighboring reexport advisories.

The port imports `CudaBackend` and calls `create_with_options().compile_module`.
Its own declarations mention neither failed type. `CudaBackend` already imports
both from `compiler.mir.mir_types`, and its method signatures/fields use them.
The evidence points to imported method surface owner projection; the precise
compiler-owner defect remains unproved. Adding explicit owner imports to the
port is a narrow temporary workaround, not a demonstrated compiler fix.
CUDA static composition, capability advertisement, real PTX emission and
incompatible-target errors remain unchanged.

Original evidence is retained at
`C:/dev/simple-bootstrap-storage/phase3-validation-20261016/phase3-a174-1e93dca4-cli-bootstrap-cycle2/compile.log`
and its frozen source snapshot and HIR ledger. Workaround implementation commit:
[`b114fbe355e257f6265b0fa9c738dcc21dea55b7`](https://github.com/ormastes/simple/commit/b114fbe355e257f6265b0fa9c738dcc21dea55b7).
The commit is not yet landed or runtime qualified. Background owner: compiler
HIR import/surface projection lane.

Recovery: fix and qualify imported class method/field owner projection, then
remove only this tagged import and rerun the original CUDA port HIR/native
closure with CUDA static selection enabled. An unrelated green test or fetched
fix does not establish recovery. Existing
`test/01_unit/compiler/backend/cuda_backend_port_spec.spl` checks real PTX output,
capabilities and wrong-target rejection. Run it with a qualified full CLI;
authored checks and static review alone do not prove native HIR/object success.

For bounded manual reproduction, use the exact corrected Phase 3 source
selectors and `native-build --entry src/plugins/backend_cuda/cuda_backend_port.spl
--emit-object`, with isolated SCV/cache ownership, immutable producer/source
pins and retained nonzero failures. The public command traverses dependencies;
it is not a private HIR queue replay or exact single-object publication bypass.

## 2026-11-11 triage (lane p3fix-p2a-20261111) — LIVE; workaround landed and pinned, verification still grant-blocked

Re-verified at release/1.0.0 tip (worktree @ 79d5af6723f6):

- **The workaround commit has landed and is pinned**: `b114fbe355e` is an
  ancestor of HEAD; `src/plugins/backend_cuda/cuda_backend_port.spl:10-11`
  carries the `@workaround bug=cuda_port_imported_method_surface_type_owner_2026_10_16`
  tag and `use compiler.mir.mir_types.{MirType, MirSignature}`. The doc's
  "not yet landed" state is stale.
- **No owner-projection fix commit found** (`git log --all --grep` over the
  bug id / "owner projection" / "imported surface"): the explicit import is
  still required; the 2026-11-07 hir-nominal-generic-owner merge did not
  retire it.
- **Fresh spec evidence** (deployed seed bin/simple.exe @ 46fe8f6b6def,
  interpreter, --no-cache): `test/01_unit/compiler/backend/cuda_backend_port_spec.spl`
  3/3 PASS (real PTX output, capabilities, wrong-target rejection).
- **Verdict: LIVE**, same gate as cuda_optimizer_surface_owner_2026_10_10:
  recovery requires fixing + qualifying imported method/field owner
  projection and rerunning the CUDA port HIR/native closure
  (`native-build --entry src/plugins/backend_cuda/cuda_backend_port.spl
  --emit-object`) under a stage3-admitted producer. That build class is not
  sanctioned for this bug lane (no stage3 producer / self-hosted check
  worker on this host); the exact grant command is recorded in
  build/review/p2fix-compiler-20261110.sdn.

Status stays open. Code change in this lane: none for this row (the Row 7
evidence-gate repair — pub widening of five mir_opt constructors/analyzers —
also keeps this row's closure compilable for the future qualification run).

## 2026-11-22 verification (lane work/cuda-compiler-bugs)

The explicit `use compiler.mir.mir_types.{MirType, MirSignature}` import and its
`@workaround` tag are removed from `src/plugins/backend_cuda/cuda_backend_port.spl`.
The fixture `test/native/cuda_compiler_bugs/port_owner/main.spl` imports the port.
It was native-built with the integ25 Stage 2 admitted producer (sha256
`ef46f0d2ab4274c4550530851db407bf9bad7f21bfabd50f9b56e87e77fd58d6`, aarch64,
base `3c2e4556b6d`).

Result: `plugins.backend_cuda.cuda_backend_port` completed HIR, and the 514-module
closure finished with `failed=0`. Zero `unresolved type: MirType` or
`MirSignature` diagnostics, against 28 errors in the 2026-10-16 cycle-2 ledger.

Not proven:
- The build was OOM-killed by the lane's 8 GiB cgroup cap during whole-program
  MIR (200/514 modules, rss 5670 MiB), so no object or binary was produced.
- PTX emission is not re-qualified by this run.

The full command and context are in
`doc/08_tracking/bug/cuda_optimizer_surface_owner_2026_10_10.md` (2026-11-22).

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
