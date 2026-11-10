# Kernel closure: 10 residual K0 -> P_STATIC imports (2026-09-07)

Status: FIXED for the 10 recorded edges (2026-11-11, lane ne13) — the guard
still FAILs on 19 newer edges unmasked by this triage; see the 2026-11-11
addendum at the end of this file before trusting any per-edge claim here.
Guard: `sh scripts/check/check-kernel-closure.shs`.
Partition authority: `doc/04_architecture/compiler/plugin_arch/kernel_pluggable_partition.md` §3.
Migration plan: `doc/03_plan/compiler/plugin_arch/kernel_plugin_migration_plan.md`.

## Verdict, before and after

```
before: FAIL — 1908 file(s) classified, 0 unclassified, 17 K0->P imports
after:  FAIL — 1908 file(s) classified, 0 unclassified, 10 K0->P imports
```

7 of 17 edges were misclassifications and are fixed in `kernel_closure.sdn`.
The remaining 10 are REAL violations and are recorded here rather than
baselined or opted out. Nothing about the checker was weakened; it was
strengthened (see § Checker gap closed).

## Fixed: 7 edges, by correcting the classification (not the code)

`src/compiler/90.tools/` is a directory of convenience, not a partition
boundary. Four files under it are kernel components by §3. Each got a
file-level row ahead of the blanket `P_STATIC|src/compiler/90.tools/**`.

| file | new class | §3 citation | evidence |
|---|---|---|---|
| `90.tools/api_surface.spl` | K0 | "Interface/ABI digest computation ... K0 — Identity must be computed by the party it protects" | zero imports; pure `ApiSurface` data record consumed by `35.semantics/interface/{compile_interface,module_identity}.spl` |
| `90.tools/aop.spl` | K0 (provisional) | "Compile-time weaver ... K0. Advice *bodies* are P; the weaver is K0"; §3.1 lists the weaver as never-leaves-kernel | defines `AopWeaver`, a **field** of `driver_types.spl:494` and `pipeline/compiler_context.spl:21`; imports only `compiler.core.aop` (00.common) and `compiler.frontend.core.aop_debug_log` |
| `90.tools/async_integration.spl` | K0 | "Frontend..MIR ... K0 — HIR/MIR stay internal; exposing them as plugin interfaces freezes internals (Hyrum)" | imports only `compiler.mir.*` / `compiler.hir.*`; runs as a default pipeline pass (`driver_pipeline_passes.spl:32`) |
| `90.tools/header_gen/shared_lib_flags.spl` | K1 | "Linker wrappers mold/lld/flavor/sysroot — K1 — env-selected at run time already" | host-OS shared-lib compile/link flag selection; imports only `std.io_runtime.{env_get_opt, process_run}`; no compiler types |

Edges cleared: `compile_interface -> api_surface`, `module_identity ->
api_surface`, `driver_types -> aop`, `compiler_context -> aop`, `pipeline_fn
-> aop`, `driver_pipeline_passes -> async_integration`,
`driver_api_project_build -> shared_lib_flags`.

**Caveat on `aop.spl`, stated rather than hidden.** The file also holds
`LogAspect`, `TracingAspect` and `ContractAspect` — advice *bodies*, which §3
classes as P. The K0 row classifies the file by its kernel half because the
checker is file-granular. Phase 7 of the migration plan (aspects as APK packs)
must split the bodies out; the row is provisional until it does. Do not read it
as a permanent decision that advice bodies are kernel.

## Not fixed: 9 VHDL edges (Phase 5 of the migration plan)

```
driver_aot_vhdl_output.spl    -> backend.hwir_to_vhdl
driver_aot_vhdl_output.spl    -> backend.vhdl.vhdl_design_catalog
driver_aot_vhdl_output.spl    -> backend.vhdl_backend
driver_riscv_gen2_product.spl -> backend.hwir_to_vhdl
driver_vhdl_artifact_build.spl-> backend.vhdl.vhdl_design_catalog
driver_vhdl_artifact_build.spl-> backend.vhdl.vhdl_helpers
driver_vhdl_artifact_build.spl-> backend.vhdl.vhdl_abi
driver_vhdl_artifact_build.spl-> backend.vhdl_type_mapper
driver_vhdl_artifacts.spl     -> backend.hwir_to_vhdl
```

These are genuine, and §3 confirms both ends: "Non-bootstrap backends:
Native/C, Wasm, Cuda, Hip, OpenCl, **Vhdl**, IrTc, Lean, Byl, Vulkan, LlvmLib —
**P-static**", and "Driver core ... **K0**". The driver hard-links the VHDL
backend by direct symbol import.

**Why reclassifying the four driver files P_STATIC was considered and
rejected.** It would look like a fix — the count drops — while being one. The
four are reached from the K0 driver hub:

```
driver_aot_output.spl:8       use     compiler.driver.driver_aot_vhdl_output.*
driver.spl:22                 pub use compiler.driver.driver_riscv_gen2_product.{...}
```

so the red moves to `driver_aot_output.spl` and `driver.spl` rather than
disappearing. That is relocation, not repair.

**The correct fix is Phase 5** of the migration plan: `BackendPort` becomes
`trait BackendPlugin` + `BackendPortV1`, `backend_factory_full.spl:113-137` and
`codegen_factory.spl:37-41` dispatch through a table, and the non-bootstrap
backends (VHDL among them) move under `src/plugins/backend_*/`. The driver then
holds the K0 interface, not the implementation. That is a multi-file
architectural change with a bootstrap-fixpoint acceptance bar
(`test/02_integration/bootstrap/plugin_edit_no_rebuild_spec.spl` per the plan)
and does not belong in a classification-repair PR.

## Not fixed: 1 layer-call-scan edge

```
35.semantics/layer_call_wiring.spl -> compiler.tools.verify.layer_call_scan
```

Real, and **not** a misclassification in either direction:

- `90.tools/verify/layer_call_scan.spl` is a genuine verify tool — it imports
  `std.nogc_sync_mut.io.{dir_ops.dir_walk, file_ops.file_exists, file_read}`.
  Marking it K0 would make the checker pass while being false: the checker does
  not scan `std.*` imports, so a filesystem-walking scanner would sit inside
  the kernel unremarked.
- Relocating `layer_call_wiring.spl` into `90.tools/verify/` does not help
  either: `80.driver/driver_source_pipeline_parsing.spl:50` imports
  `check_project_layer_calls`, so the K0->P edge would simply reappear one hop
  out, at the driver.
- The pure-text half cannot be lifted out on its own: `scan_source_calls`'s
  import resolution is `file_exists`-gated (noted in
  `layer_call_wiring.spl:132`), so it is not a pure function of its arguments.

The real fix is the one the file's own header already names: derive layer call
edges from AST/HIR inside the kernel instead of from a text/regex scan of
source files, at which point the fs-walking tool is not on the path at all
("Gating compilation on this is future work once call edges come from AST/HIR
instead of text", `layer_call_wiring.spl:31-33`). Until then the driver's parse
pipeline genuinely depends on a P-static text scanner.

## Checker gap closed in the same change (a strengthening)

`pub use` was not matched by the import scan — only bare `use` was — so a K0
file that RE-EXPORTS a P module was invisible. `driver.spl:22` is exactly that
shape. Widening the scan to `^[[:space:]]*(pub[[:space:]]+)?use` can only add
edges, never remove one; measured, it surfaced **0** additional violations
today (still 10), so the count above is not inflated by it. A new `--selftest`
fixture pins it: a K0 file whose only P dependency is a `pub use` must FAIL.

Scope of the census this widening now covers: 34 `pub use compiler.` lines
across 13 files under `src/compiler`.

## Reproduce

```
sh scripts/check/check-kernel-closure.shs --selftest   # 4 fixture rounds, fatal
sh scripts/check/check-kernel-closure.shs              # FAIL, 10 K0->P imports
```

## Addendum 2026-11-11 (lane ne13) — recorded 10 edges are FIXED; guard still red, two layers

**Verification actually run** (this lane, worktree simple-p3-ne13-20261111,
release/1.0.0 tip c8b6d0ebe90e):

```
sh scripts/check/check-kernel-closure.shs --selftest   # kernel closure self-test OK (11 fixtures)
sh scripts/check/check-kernel-closure.shs
# before this lane's manifest repair:
#   FAIL — 2621 classified, 20 unclassified   (all 20 = src/compiler/bootstrap_admission/**)
# after:
#   FAIL — 2641 classified, 0 unclassified, 1 K0->P, 3 K1->P, 15 kernel->app/os, 0 unresolved
```

**The 10 recorded K0->P_STATIC edges are gone.** None of the nine VHDL edges
nor the `layer_call_wiring -> compiler.tools.verify.layer_call_scan` edge
appears in the current violation scan. The fixing change is the Phase 5
backend-plugin migration this doc names as the correct fix: the non-bootstrap
backend implementations and their driver outputs now live under
`src/plugins/backend_*/` (e.g. `driver_aot_vhdl_output.spl` is now
`plugins/backend_vhdl/driver/driver_aot_vhdl_output`, the VHDL impl under
`plugins/backend_vhdl/vhdl/`; `src/compiler/backend/` no longer exists). The
kernel scan covers only `src/compiler`, so the recorded hard-links are out of
the kernel by construction, and the live scan confirms zero K0->P_STATIC edges
for the recorded files. The K0 driver holds the interface, not the
implementation — the architecture this doc asked for.

**Layer 1 (fixed in this lane): 20 unclassified `bootstrap_admission` files
were masking the entire edge scan.** The checker is fail-closed: while any
file is unclassified it prints only KERNEL-CLOSURE-001 and exits BEFORE the
import scan (`END { if (missing > 0) exit 1 }`). `src/compiler/bootstrap_admission/`
(20 files incl. `signature_owner_diagnostic/`) landed after the manifest was
written and never got a row. Fixed by adding one `entries:` row:
`P_STATIC|src/compiler/bootstrap_admission/**` — admission fixtures compiled by
bootstrap verification scripts (`check-bootstrap-stage2-struct-receiver.shs`,
`candidate_frontend_admission.shs`, `bootstrap-from-scratch.sh` and peers), no
`src/` importer outside the directory, not on any kernel path — same precedent
as `src/compiler/test/**` and the §3 "not on any kernel path" reading. The
`rules:` projection was deliberately NOT touched (the manifest's own NOTE:
editing it changes the bootstrap kernel-inputs hash, which cannot be verified
without a bootstrap run — out of this lane's grant).

**Layer 2 (unmasked, NEW, needs the architecture owner — do not read this doc
as "guard green"):** with classification complete the edge scan now reports 19
boundary edges introduced by KPF-worker / dynsmf / backend_plugin work
(2026-10/11), invisible since `bootstrap_admission` landed:

- 1 K0->P: `80.driver/driver_aot_pipeline.spl -> plugins.backend_vhdl.driver.driver_aot_vhdl_output`
- 3 K1->P: `70.backend/backend/_VhdlProcess/process_codegen.spl -> plugins.backend_vhdl.vhdl.{vhdl_builder,vhdl_helpers}`, `70.backend/backend/_VhdlProcess/terminator_codegen.spl -> plugins.backend_vhdl.vhdl.vhdl_builder`
- 15 K0/K1->app/os, incl. `99.loader/{module_loader_compat,loader/module_loader}.spl -> os.smf.{dynsmf_owned_v2,smf_dynlib,smf_generation}`, `70.backend/backend_plugin/kpf_worker/session.spl -> os.smf.kernel_plugin.*` (5), `70.backend/linker/linker_pack{,_entry}.spl -> os.smf.*`, `70.backend/introspection/elf_artifact_gate.spl -> app.io.file_ops`, `95.interp/execution/mod.spl -> app.io.jit_sffi`, `70.backend/linker/test/smf_header_reader_parity_spec.spl -> {os.smf.*, app.startup.launch_metadata}`

These are genuine per the WP-05-widened checker and each needs a §3-cited
owner decision (reclassify the source file, relocate the import behind a K0
interface, or record an explicit manifest exemption). They are NOT the 10
edges recorded above; this lane routed them here instead of leaving them
masked behind the unclassified failure.
