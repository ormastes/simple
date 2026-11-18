<!-- codex-architecture -->
# Bootstrap Build Modes

## Purpose

Define the bootstrap and pure-Simple native-build mode boundary so compiler,
interpreter, and loader work does not drift back into Rust-seed tooling.

## Modes

| Mode | Default | Build shape | Owner |
|------|---------|-------------|-------|
| `dynload` | yes | Native executable plus SMF cache artifacts where the current driver supports `OutputFormat.Both` | `src/app/io/_CliCompile/compile_targets.spl`, `src/compiler/80.driver` |
| `one-binary` | no | Monolithic native executable path using `OutputFormat.Native` | `src/app/io/_CliCompile/compile_targets.spl`, `src/compiler/70.backend` |

`scripts/bootstrap/bootstrap-from-scratch.sh` defaults to `dynload`, reuses the
existing Rust seed/runtime, and stops after the pure-Simple staged build. It
must not run cargo unless `--full-bootstrap` is explicit. Stage 4 full-CLI
relinking requires `--full-cli`, `--deploy`, or `--mode=one-binary`.
`--full-bootstrap` controls only Rust seed/runtime freshness and still stops
after the dynload stages unless combined with a full-CLI option. The Rust seed
is a bootstrap input, not the production toolchain.

## Dependency Tracing

`--entry-closure` is a reducer, not an authority. It scans imports from the
entry to avoid loading broad source roots, but the real owner boundary is:

- module resolution: `src/compiler/99.loader/module_resolver/`
- source loading and entry closure env: `src/compiler/80.driver/driver.spl`
- AOP/MDSOC weaving: `src/compiler/85.mdsoc/` plus `driver_pipeline.spl`
- interpreter load/session cache: `src/compiler/10.frontend/core/interpreter/`
- SMF/native artifact output: `src/compiler/80.driver/driver_aot_output.spl`

Cache reuse is safe for unchanged leaf source artifacts. Changes that can alter
weaving, module resolution, interpreter adapters, loader ABI, or compiler ABI
must invalidate broadly. Script-level dependency tracing must never claim more
precision than the compiler resolver can prove.

## Refactor Invalidation Boundary

The broader refactor lane is
`doc/03_plan/agent_tasks/bootstrap_compiler_interpreter_loader_arch_refactor.md`.
Until resolver-backed cache keys include source hash, options hash, dependency
interface hashes, and AOP/MDSOC configuration hash, `dynload` cache reuse stays
conservative: bootstrap scripts clear cache on changes under `src/compiler`,
`src/app`, or `src/lib`, and any AOP/MDSOC/weaving environment change is treated
as a broad invalidation.

## Rust Seed Warning

Rust-built `src/compiler_rust/target/bootstrap/simple` prints `WARNING` when run
outside bootstrap. Bootstrap internals set `SIMPLE_BOOTSTRAP=1`; users should
build and use pure-Simple `bin/simple`.

## Cooperative Review

The current lane used read-only sidecars for bootstrap behavior, dynload/loader
surfaces, and dependency tracing/AOP risk. Integration owner is the main Codex
thread; future implementation of resolver-backed incremental rebuilds needs a
normal/high-capability review before claiming production precision.

## Orthogonal Axes: Phase, Profile, Composition, Host ABI, and Target (2026-11-18)

Artifact packaging mode (`dynload` SMF+native vs `one-binary` monolithic native) is independent of bootstrap stage, target profile, backend composition/linkage, and target architecture. Implementations and receipts must keep all five axes distinct:

| Axis | Values | Authority / Selector | Boundary Contract |
|------|--------|----------------------|-------------------|
| Bootstrap phase | `phase3`, `phase4` | `--managed-build-phase=phase3\|phase4` (`bootstrap_focused_native_build_args.spl`) | `phase3` builds the self-hosted `bootstrap_main.spl` recovery compiler (`--stop-after-stage3` stops here without implying Phase-4 completion or deployment); `phase4` builds the full CLI / product surface (`main.spl`). |
| Target profile | `dev`, `prod` | `--profile=dev\|prod`, `TargetBuildProfileV1` (`driver_compile_options.spl`) | `phase3` is strictly `dev`-only (`phase3` + `prod`/`--release` fails closed). `phase4` accepts both `dev` (unstripped Diagnosis variant) and `prod` (Release variant, default when `--profile` is omitted) with isolated cache, variant-key, and receipt namespaces (`focused_native_build_profile_cache_dir_v1`, `focused_native_build_profile_receipt_namespace_v1`, `ConfigVariantKeyV1`). |
| Backend composition & linkage | `host-only` (static K1), `full` (static 12-port), `dynlib` (`simple_backend_plugin_v1`) | `SIMPLE_BACKEND_COMPOSITION=host-only\|full`, `src/compositions/backends_host_only`, `src/compositions/kernel_llvm{,_cranelift}`, `--backend-plugin=PATH` | `host-only` (default under `SIMPLE_BOOTSTRAP_STAGE3=1` and K1/`backends_host_only` source overlays) excludes optional GPU/VHDL/Wasm static backend closures at the import boundary while routing host codegen through `BackendSession`. `--backend-plugin` loads an explicit `simple_backend_plugin_v1` shared library without silent static fallback. Passing `--mode=dynload` alone does **not** prove dynamic backend plugin execution. |
| Compiler host ABI | Resolved host triple + runtime/CRT ABI | Host build/runtime capsule (`dynamic_loader.spl`, provider manifest) | Determines the executable/shared-library ABI loaded into the compiler process (for example Linux ELF `.so`, macOS `.dylib`, Windows GNU/llvm-mingw UCRT vs MSVC `.dll`). |
| Emitted target | Target triple, CPU model, feature set | `--target`, `--cpu`, `MirTargetContext` (`target_context_v2.spl`) | Determines the object/code ABI emitted by the selected session. Cross-compilation loads a **host-ABI** provider library that emits **target-ABI** artifacts. |

See `doc/03_plan/compiler/phase3_first_dynlib_architecture_bootstrap_2026-11-18.md` (`C1`, `C7`; unit-verified slices in progress, native `G-P3-HOST`, `G-P4-DEBUG`, and `G-P4-RELEASE` gates pending execution).
