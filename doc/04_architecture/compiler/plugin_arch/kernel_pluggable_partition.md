# Kernel / Pluggable Partition of the Simple Compiler and Runtime

Status: PROPOSED (2026-08-28). Architecture only; no code change.
Research: `doc/01_research/compiler/plugin_arch/kernel_plugin_versioning_research_2026-08-28.md`.
Design: `doc/05_design/compiler/plugin_arch/versioned_param_objects_and_interfaces.md`.
Plan: `doc/03_plan/compiler/plugin_arch/kernel_plugin_migration_plan.md`.

Scope pin: "MDSOC+" = the ECS-business-layer rule set in
`doc/04_architecture/compiler/mdsoc/mdsoc_architecture_tobe.md:360-459`
(kernel and drivers MDSOC-only, no ECS `:372-378`; userland = "MDSOC capsule
outside, ECS inside"). The unrelated proposal
`mdsoc_plus_tagged_structural_compute_architecture.md` (status Proposed `:9`)
is not a basis for this document.

## 1. Goal and the invariant

Goal: changing a plugin or a parameter never forces a kernel rebuild, and the
bootstrap closure shrinks to the kernel.

Today the opposite holds by construction: the bootstrap rebuild gate hashes
**every** `src/compiler/**/*.spl` plus any `SIMPLE_*(AOP|MDSOC|WEAV|LOAD|...)`
env var (`scripts/bootstrap/bootstrap-from-scratch.sh:1018-1028`). A lint rule,
an MCP tool table row, a coverage-wrapper string, or an AOP log-level env var is
a kernel input. Aspect parameters are passed as typed objects, env strings, and
generated source text in three different places (research §7).

The invariant, three legs:

1. **Interface identity is `(name, major, abi_digest)`**, recorded in a manifest
   and re-checked at link (P-static) or load (P-dyn).
2. **Parameter objects are versioned records with explicit presence** — never
   env strings, never generated source — so a new parameter is a new ordinal,
   not a new kernel.
3. **Negotiation is fail-closed** with a named code; silent nil is a defect
   (`doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`).

## 2. Partition classes

| Class | Definition | Rebuild consequence |
|---|---|---|
| **K0 kernel-irremovable** | Needed to compile the compiler (bootstrap fixpoint) or to execute any Simple binary, and nothing could verify a replacement of it. | Change = kernel rebuild (full bootstrap). Keep small, freeze its ABI. |
| **K1 kernel-replaceable** | In the kernel binary, behind a K0-owned interface, chosen at build time (exactly one implementation must be present for the fixpoint). | Swap = relink of the kernel binary against another implementation; K0 objects unchanged. |
| **P-static** | Implements a versioned interface; compiled as its own unit; linked into the shipped binary. | Plugin rebuild + relink; kernel object cache keys unchanged (§4.3). |
| **P-dyn** | Implements a versioned interface; loaded at run time via the aspect-pack loader or the SFFI dynamic loader; negotiated. | No relink. |

Membership test for K0: "if this were a plugin, who loads it, and who checks
the loader?" If the answer is "itself", it is K0.

## 3. Partition table

| Subsystem (where) | Class | Reason |
|---|---|---|
| Value ABI: array/list/buffer/dict/string representation across seed, pure-Simple, C runtime (`doc/04_architecture/compiler/array_value_abi_contract.md`; `src/runtime/runtime.h`) | **K0** | It is the surface every param object crosses; nothing sits under it. |
| C runtime core `rt_*` value/alloc/string/array/dict (`src/runtime/*.c`; guarded by `scripts/check/check-runtime-api-regression-push.shs`) | **K0** | Hot path + ABI. Not swappable: `libsimple_runtime.so` does not exist (0 hits); only `.a` (`src/compiler/70.backend/backend/simpleos_native_symbols.spl:76,82`). |
| SFFI trampoline + dynamic loader (`src/lib/nogc_sync_mut/sffi/*`; `src/runtime/runtime_dynload.c:447-503` `spl_dlopen*`/`spl_dlsym*`) | **K0** | Loads P-dyn; cannot be P-dyn. (No `rt_dlopen` exists.) |
| Aspect-pack loader + facet registry + gate + signature (`src/lib/common/aspect_pack.spl:1753-2205,2607-2623`; `src/lib/common/facet_registry.spl:57-230`; `src/compiler/99.loader/aspect_pack_*.spl`, `module_loader_compat.spl:442,560`) | **K0** | The plugin host. |
| Module resolver, source loading, entry closure (`src/compiler/99.loader/module_resolver/`; `80.driver/driver.spl`; `bootstrap_build_modes.md:26-33`) | **K0** | Bootstrap cycle. |
| Frontend..MIR: `10.frontend`, `15.blocks`, `20.hir`, `25.traits`, `30.types`, `35.semantics`, `40.mono`, `50.mir`, `55.borrow` | **K0** | Bootstrap cycle. HIR/MIR stay internal; exposing them as plugin interfaces freezes internals (Hyrum). |
| Compile-time weaver `80.driver/driver_pipeline_aop.spl:47-112` + weaving types `85.mdsoc/weaving/` | **K0** | Runs in the default pipeline (`driver_pipeline_execution.spl:27`, `driver_orchestration.spl:306`, `driver_aot_pipeline.spl:121-123`). Advice *bodies* are P; the weaver is K0. |
| Interface/ABI digest computation (`35.semantics/interface/compile_interface.spl:27-131`; `80.driver/cache/action_key.spl:250-301`) | **K0** | Identity must be computed by the party it protects. |
| Driver core, producer identity, manifests, receipts (`80.driver/driver_build/incremental.spl:250-301`; `watcher/smf_manifest.spl:26-46`; `src/app/build/bootstrap_receipt_planner.spl`) | **K0** | The evidence for "no rebuild". |
| MDSOC layer/capsule/visibility checkers (`85.mdsoc/types/virtual_capsule.spl:10-37`; law `mdsoc_architecture_tobe.md:123-130,279-297`) | **K0** | Enforces this partition. |
| `BackendPort` (the codegen interface) (`70.backend/backend_port.spl:15-25`, typed per design §4) | **K0** | The interface is K0; implementations are not. |
| LLVM backend (bootstrap default: `bootstrap-from-scratch.sh:112,1482`; `src/app/cli/bootstrap_main.spl:229-237,273-277`) and Cranelift backend (alternative; hardcoded in `80.driver/bootstrap_main_minimal.spl:9`, `bootstrap_types_main.spl:8`) | **K1** | Exactly one native backend must be linked for the fixpoint; either satisfies it. Selection today is `enum BackendKind` + `case` in 7 files (`70.backend/backend/backend_types.spl:20-32`, `backend_factory_full.spl:113-137`, `codegen_factory.spl:37-41`, `00.common/mir_target_context.spl:91-95`, `60.mir_opt/mir_opt/pattern/rule_engine.spl:41,106-118`, `80.driver/cache/compile_options_hash.spl:239,251`). Statically linked: large external dependency; backend is part of the cache scope key (`incremental.spl:292-301`). |
| Non-bootstrap backends: Native/C, Wasm, Cuda, Hip, OpenCl, Vhdl, IrTc, Lean, Byl, Vulkan, LlvmLib (`backend_types.spl:20-32`) | **P-static** | Same `BackendPort`; not needed for the fixpoint; statically linked for the reasons in §3.2. |
| MIR optimizer passes (`60.mir_opt/optimizer_plugin.spl:267-319` `optimizer_plugin_registry_*`) | **K1** | Descriptor registry exists; passes touch MIR (internal), so in-binary and registry-selected, never P-dyn. |
| Linker wrappers mold/lld/flavor/sysroot (`70.backend/linker/mold.spl:95-118`; `_LinkerWrapper/native_linking.spl:748-750`; `backend/llvm_cross_target.spl:9,433`) | **K1** | Env-selected at run time already. |
| Interpreter / tiered JIT (`95.interp/execution/tiered_jit.spl:272-274`) | **K1** | Behind the driver. |
| Runtime bundle (`SIMPLE_NATIVE_RUNTIME_BUNDLE`, `70.backend/backend/llvm_native_link_orchestrator.spl:119-121`; fingerprinted `incremental.spl:250-260`) | **K1** | No `RuntimeBundle` type exists; a bundle change changes producer identity and forces relink — correct for K1. Design §6 gives it a descriptor record. |
| Aspects with advice bodies: logging, coverage/MCDC, trace, assurance probes (`test_executor_parsing.spl:792-869`; `mcdc/dynamic_aspect.spl:128-163`; env vars `driver_pipeline_aop.spl:68-80`) | **P-static** (bootstrap gate lanes) / **P-dyn** (dev/test lanes) | Today: source rewriting + env strings. Target: one `AspectParamsV1` param object (design §2.3) and an APK pack; `APK_ACT_STATIC` in the bootstrap lane, `LAZY_FACET`/`HOT` elsewhere. Kernel never sees the advice body. |
| Lint rules (`90.tools/lint/_LintMain/lint_checks.spl:71,198,503,617,658`; `name_lints.spl`, `os_freestanding_lints.spl`, `wm_lane_boundary_lints.spl`, `traceability_and_assertions.spl`) | **P-static** | Monolithic class today; first migration target (plan Phase 4): pure, no hot path, deterministic per compiler build. |
| MCP tool table/dispatch (`src/app/mcp/tool_table.spl:16-22`; `main_dispatch.spl`; `main_lazy_*.spl` = per-group processes) | **P-static** (core tools) / **P-dyn** (tool packs) | Hand-built array; process-level laziness already exists. |
| SFFI providers used by the compiler (`scripts/check/no_direct_rt_allowlist.txt:5-11` dirs; `SIMPLE_LINK_OBJECTS` `70.backend/backend/llvm_native_link_stage4_projection.spl:40-123`) | **P-static** | Deliberate: `native_linking.spl:570-575` (incomplete `.so` export list; no rpath into build tree); Stage4 forbids aggregate archives (`stage4_symbol_closure.spl:782-785`). |
| SFFI providers used by applications: GPU (`rt_gpu_provider_abi_version()` `runtime.h:359`), DB, net, UI (`sffi/dynamic_versioned.spl:23-187`) | **P-dyn** | Already dlopen; filename-only version match and presence-only symbol probes (`:170-187,78,94`), all `@unsafe` (`:49,64,68,116,142`). Must adopt design §5 negotiation. |
| Aspect packs / facets (`aspect_pack.spl`, modes `APK_ACT_{OFF,STATIC,STARTUP,LAZY_FACET,MANUAL,LAZY_PATCHABLE,HOT}` `:65-119`) | **P-dyn** with **P-static** mode | The repo's real plugin format; activation mode *is* the static/dynamic switch. |
| Target descriptors (`70.backend/target/riscv32.spl:47-121`; `enum Arch` `70.backend/linker/smf_enums.spl:62`; no `src/lib/common/target/`, no `parse_target_triple`) | **P-static** (data) | Descriptor records, not code. |
| Package manager (`src/app/pkg/*`, unwired), lockfile (`nogc_sync_mut/package/lockfile.spl`), semver (`package/semver_old.spl:257-267`) | **P-static** tool | Not on any kernel path; becomes the consumer of `provides:/requires:` (design §6). |
| ECS business layer (`src/lib/gc_async_mut/ecs/`; `nogc_sync_mut/ecs/` only `change_detection.spl`) | **userland only** | `mdsoc_architecture_tobe.md:372-378`. Never K0/K1. |

### 3.1 What can NEVER leave the kernel
Value ABI; C runtime core; SFFI trampoline + dynamic loader; aspect-pack
loader/registry/gate/signature; module resolver; frontend..MIR; the weaver;
digest computation; driver identity/manifests/receipts; MDSOC checkers; the
`BackendPort` interface (not its implementations).

### 3.2 Why some pluggables stay statically linked
1. Bootstrap determinism: the receipt must reproduce the gate
   (`incremental.spl:250-252`); a P-dyn plugin in the bootstrap lane would make
   the receipt depend on a filesystem state at run time.
2. Existing, justified link policy (`native_linking.spl:570-575`).
3. Hot path: backends and optimizer passes see MIR per node.
4. Large unstable-ABI external deps (LLVM).
5. Platforms without dlopen (baremetal, SimpleOS early boot).

Static linking does not weaken the invariant: the P-static unit is compiled
against the same `(name, major, abi_digest)` and recorded in the same manifest;
only the check time differs (link-time receipt vs load-time negotiation).

## 4. Invariants that make the kernel rebuild-free

### 4.1 Interface identity
- Reuse the typed digest `compile_interface_digest`
  (`compile_interface.spl:131`, domain `simple/compile-interface/v1 :27`,
  encoders `:48-102`).
- Replace the placeholder `abi_interface_digest`
  (`module_identity.spl:9-31`, `simple/abi-interface/placeholder-v0`,
  "compute-and-log only" `:3`) with `simple/abi-interface/v1` folding field
  ordinals, field types, and param-object schema versions (design §3).
- Keep the textual `interface_digest_of` (`action_key.spl:250-255`) for cache
  keys only — it skips struct fields by its own admission. It IS wired
  (`driver_build/incremental.spl:14,388`; `watcher/smf_manifest.spl:18,358`;
  `sif/sif.spl:46,78,153,196`); the "zero callers" text in
  `.claude/rules/commands.md` and `src/lib/scv/build_invalidation.spl:12,38,172`
  is stale and should be corrected in the first landing.

### 4.2 Param objects
Design §2. Convention = the repo's own two: `ApkXxxV1/V2/V3` suffixed records
(`aspect_pack.spl:123-334`) and the frozen extension-identity tuple
(`extension_completeness.md:29-36`: `local_ordinal + payload_schema_hash +
module_abi_hash + schema_abi_version`). No third convention.

### 4.3 Recorded, then re-checked
- SMF manifest carries `iface_digest` (`smf_manifest.spl:41`) and `version`
  (`:43-46`, writer 3 `:54`) but never rejects (`:220,231-233`; verdict print-only
  `:163-188`). Improve: fail-closed; add `abi_digest`, `provides`, `requires`.
- Producer identity and scope key (`incremental.spl:250-252,292-301`) are the
  proof that a P-static relink leaves kernel object keys untouched: a plugin's
  source is not in the kernel object's key.
- APK gate: `APK_ABI_MISMATCH` enforced; core ABI/layout/variant gates opt-in
  and skipped when unset (`aspect_pack.spl:2196-2205`). Improve: mandatory.
- Bootstrap gate `bootstrap_wide_inputs_hash` (`bootstrap-from-scratch.sh:1018-1028`):
  narrow from `src/compiler/**` to the K0+K1 closure listed in a manifest
  (design §6.3) plus the `abi_digest` set of every P-static interface.

### 4.4 Compatibility rule (normative)

| Change | Effect | Compatible? |
|---|---|---|
| Add optional field to a param object (new ordinal, presence bit) | `schema_minor`+1; abi_digest changes; major unchanged | yes |
| Add a method to an interface (optional, negotiated) | interface minor+1 | yes |
| New interface version `X/v2` beside `X/v1` | new name | yes |
| Deprecate a field/method (slot kept) | minor+1 | yes |
| Remove / rename / retype / reorder a field or method | major+1 | **breaking** |
| Change value ABI or any K0 record | producer identity changes | **breaking for all**; full bootstrap |
| Change plugin implementation only | plugin digest changes; interface unchanged | yes; kernel untouched |

Fail-closed: `name` or `major` mismatch, or an `abi_digest` not in the host's
recorded-compatible set, is a refusal with a code. No fallback, no nil.

## 5. How the existing dyn/static switching plugs in

A unified link-mode switch **does not exist** (0 hits: `--link-mode`,
`link_mode`, `LinkMode`, `SIMPLE_LINK_MODE`). Three partial mechanisms do:

| Mechanism | Where | Role |
|---|---|---|
| `--emit-shared` -> `SIMPLE_NATIVE_BUILD_EMIT_OBJECT=shared` -> `emit_shared_requested` | `src/app/io/_CliCompile/compile_targets.spl:668,846,911-912`; `80.driver/driver_aot_native_output.spl:731-734,1078-1087`; `driver_public_shared.spl:35,93`; seed `native_binary_options.rs:95-96,122` | Builds a P-dyn artifact from a plugin source. |
| APK activation modes | `aspect_pack.spl:65-119`; gate `:2125-2205` | Per-plugin bind time: `STATIC` vs `STARTUP`/`LAZY_FACET`/`HOT`. Same catalog, same check. |
| Bootstrap `dynload` vs `one-binary` | `bootstrap_build_modes.md:11-15` | Whole-toolchain shape. |

Design §5 shows one interface, one implementation, bound in both modes.

## 6. Startup budget

Startup is ~50-60 ms end-to-end (`doc/10_metrics/startup/startup_perf_check_2026-08-17.md:22`).
Rules: P-static registration is a static table walk (no I/O); P-dyn discovery
reads one manifest (`simple.sdn` `provides:`) and defers pack I/O to first
facet use (`apk_try_facet` resident-only `module_loader_compat.spl:442` before
`_apk_load_facet_indexed_v1 :560`); negotiation compares digests, never
re-hashes source at startup. Plan Phase 7 pins this with a startup-time gate.
