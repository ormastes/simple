# Bootstrap Build Modes TLDR

Purpose: keep bootstrap and native-build mode policy out of the Rust seed and
inside pure-Simple tooling.

- Default mode is `dynload`: reuse native cache when compiler/AOP/loader inputs
  are unchanged and emit native plus SMF cache artifacts where supported.
- `one-binary` is the conservative monolithic native executable path.
- Normal bootstrap never rebuilds Rust; `--full-bootstrap` is the only cargo
  rebuild path.
- `--entry-closure` is a reducer, not authoritative dependency tracing.
- AOP/MDSOC weaving, module resolver, interpreter cache, loader ABI, or compiler
  ABI changes invalidate broadly.
- Rust seed tools warn users to build/use pure-Simple `bin/simple`.

Next paths: `scripts/bootstrap/bootstrap-from-scratch.sh`,
`src/app/io/_CliCompile/native_build.spl`,
`src/compiler/80.driver/driver.spl`,
`src/compiler/99.loader/module_resolver/`,
`src/compiler/85.mdsoc/`.

## Phase-3-first orthogonal axes (2026-11-18)

- Packaging mode (`dynload` SMF+native vs `one-binary` monolithic native) is separate from dynamic codegen plugins (`--backend-plugin=PATH` / `simple_backend_plugin_v1`).
- Bootstrap phase (`--managed-build-phase=phase3|phase4`) and profile (`--profile=dev|prod`) are orthogonal for Phase 4: `phase3` is strictly `dev`-only; `phase4` defaults to `prod` when `--profile` is omitted and supports both `dev` (Diagnosis) and `prod` (Release) in isolated cache/receipt namespaces.
- Backend composition (`SIMPLE_BACKEND_COMPOSITION=host-only|full`, `src/compositions/backends_host_only`, K1 kernel roots) keeps Phase 3 bounded to the proven host K1 backend without importing optional GPU/VHDL/Wasm closures.
- Compiler host ABI (what `.dll`/`.so`/`.dylib` the compiler loads) is distinct from emitted target triple/CPU/features (what object code the backend emits).
- Plan & specs: `doc/03_plan/compiler/phase3_first_dynlib_architecture_bootstrap_2026-11-18.md`, `src/app/cli/bootstrap_focused_native_build_args.spl`, `src/compiler/70.backend/backend/static_backend_registry.spl`.
