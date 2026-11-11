# CUDA port imported method surface loses MIR type owners

Status: OPEN; explicit-import workaround awaiting actual HIR/object verification.
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
