# Phase-2 verification matrix: CLI/test-runner builds fail on HIR export-origin and @cfg duplicate-definition checks

Status: open, 2026-10-07. Lane: work/release-p2-cranelift-20261007
(release phase1+2 bootstrap; same failures reproduced on main — files
byte-identical between release/1.0 and main at the time of writing).

## Context

`bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2
--backend=cranelift --jobs=10 --no-mcp` on release `1e5509f6494`
(aarch64-apple-darwin, M4):

- Stage 2 itself ADMITS: seed rebuild, phase 1, stage-2 native build
  (compiler self-host), sanity, and struct-receiver/capability proofs all
  PASS (the 2026-10-06 `@when/@else` discovery fix holds).
- The compiler-tests phase verification matrix then fails its two product
  builds:
  - `compiler_cli_build` → **FAIL**
  - `test_runner_build` → **CRASH**
- The interpreter / loader / compiler-bootstrap suite rows that depend on
  those products therefore cannot run.

## Failure class A — invalid export origin (16 distinct errors)

Reported against importers in `src/compiler/99.loader/`:
`aspect_pack_io.spl`, `compiler_sffi.spl`, `jit_instantiator.spl`,
`metadata_symbols.spl`, `module_loader_compat.spl`. Names:

- `SweeperStats` — defined once at
  `src/compiler/99.loader/loader/generation_sweeper.spl:32`; the error
  claims origin `compiler.loader.runtime.generation_sweeper` (a module that
  does not exist — the `.loader` path segment is dropped), expected at
  `compiler.loader.runtime.__init__`.
- `SmfCache` — DUPLICATE definitions: `class SmfCache` at
  `src/compiler/99.loader/smf_cache.spl:17` AND `struct SmfCache` at
  `src/compiler/99.loader/loader/smf_cache.spl:254`.
- `SmfCacheManager` — same dual-module pattern.
- `native_mmap_file` — TWO definitions with DIFFERENT signatures:
  `loader/smf_mmap_native.spl:61` (returns tuple) vs
  `smf_mmap_native.spl:115` (returns `[i64]`).

Example error:
`invalid export origin 'compiler.loader.runtime.generation_sweeper::SweeperStats'
for 'compiler.loader.runtime.__init__::SweeperStats'`

`src/compiler/99.loader/runtime/__init__.spl` curates re-exports with
`export use compiler.loader.loader.<origin>.{...}` plus bare `export <name>`
lines; phase-2 HIR's strict export-origin validation (the item5 owner/
provenance hardening series) rejects the hops.

## Failure class B — @cfg duplicate definitions leave no export (4 errors)

`src/os/kernel/loader/elf_loader.spl` imports
`byte_at` (and siblings) from `os.kernel.loader.byte_utils`, and references
`_load_user_executable_arm64_unchecked`. Both fail:

- `byte_utils.spl` defines `byte_at` SIX times, once per
  `@cfg(arm64|arm32|riscv64|riscv32|x86_64|x86)` guard. Phase-2 HIR reports
  `module os.kernel.loader.byte_utils has no exported item byte_at` —
  the ambiguous same-name set exports under no name.
- `elf_loader.spl` itself defines `_load_user_executable_arm64_unchecked`
  four times (arch-guarded, lines 419/436/440/444) and the reference
  reports `unresolved name` (same mechanism inside the module).

## Working theory

The item5-era strictness fixes (`fix(mir): validate exact struct declaration
owners for provider methods`, export-origin/provenance validation) turned
previously tolerated duplicate-name registration (visible for months as
`field-index collision, 2026-08-07` mir-lower WARNINGS, still flooding the
test_runner_build log) into hard HIR errors for these modules. The seed and
the pre-strictness compilers keep running via last-write-wins fallback; the
phase-2 compiler fails closed.

## Update 1 (minimal repro, same day)

Class B root-caused with a 2-file repro against the admitted stage-2
compiler snapshot (`.simple/storage/build/bootstrap/stage2-compiler-tests/
<aarch64-apple-darwin>/verification/compiler.snapshot`):

```
# provider.spl
@cfg(arm64)
fn byte_at(data: [u8], off: i64) -> u8:
    data[off]

# user.spl
use .provider.{byte_at}
fn use_it(data: [u8]) -> u8:
    byte_at(data, 0)
```

`compiler.snapshot compile user.spl --format=smf --source . [--target
aarch64-apple-darwin]` fails with
`module .provider has no exported item byte_at` in ALL variants: two
guarded defs, a single guarded def, single guarded def WITH explicit
matching --target, and no --target. An UNGUARDED definition exports
fine (control). Conclusion: phase-2 HIR does not register
`@cfg`-guarded top-level definitions as module exports AT ALL — this is
a compiler registration bug, not a target-detection or
duplicate-definition issue. No source-level rearrangement of guarded
definitions can work around it; the fix belongs in the phase-2 HIR
export registration path (the seed's registration path handles guarded
declarations, which is why seed builds tolerate these files).

Implication: stage 2 self-build passes only because src/compiler,
src/app and src/lib do not rely on @cfg-guarded cross-module exports;
any build whose closure includes modules that do (os/kernel via
src/compositions/kernel_llvm_cranelift in the CLI/test-runner builds)
fails. Class A (export-origin validation) is likewise a phase-2 HIR
facade-hop bug: the recorded origin path drops a package segment
(`compiler.loader.runtime.<basename>` phantom for real origins under
`compiler.loader.loader.<basename>`).

## Update 2 — code-path analysis

- The diagnostic originates at
  `src/compiler/20.hir/hir_lowering/_Items/module_import_resolution.spl:610`
  (`surface_declares_item_indexed` probe against the frozen module surface).
- The surface is built in
  `src/compiler/20.hir/hir_lowering/module_surface_declarations.spl`
  (`module_surface_from_owner`): callables come from
  `owner.value.functions.keys()` — the PARSER module's function table. So a
  guarded declaration either never reaches the parser table in phase-2, or
  reaches it under a name/visibility the surface skips.
- Two preprocessing paths exist in
  `src/compiler/10.frontend/core/parser_preprocessor.spl`: the legacy
  `_pp_preprocess_conditionals` (host-detected) and
  `_pp_preprocess_conditionals_target_receipted_v1(os, arch)` which REQUIRES
  explicit non-empty target cfg (returns Err otherwise). The driver
  (`src/compiler/80.driver/driver_source_pipeline_parsing.spl:396+`) uses a
  "full inventory target cfg" authority (`runtime_std_cfg_source_identity_
  by_path`, receipted parse bound to `self.ctx.native_target`) only when the
  runtime publishes a std full-inventory selection; otherwise it falls back
  to the legacy path.
- Repro still fails WITH explicit `--target aarch64-apple-darwin`, so host
  arch detection / target naming is NOT the (only) cause: either the compile
  path does not thread `--target` into preprocessing, or the guarded
  declaration survives preprocessing but is dropped from the parser function
  table / surface in the phase-2 frontend.
- Next narrowing step (needs a fresh admitted snapshot): extend the 2-file
  repro with an UNGUARDED local caller inside provider.spl that calls the
  guarded fn. If the caller exports and the pair compiles, parsing keeps
  guarded defs and only surface export skips them (fix in
  module_surface_declarations.spl). If the caller also fails, the
  preprocessor strips active-guard declarations in phase-2 (fix in
  parser_preprocessor.spl / its driver plumbing).

- Update on the narrowing experiment (fresh snapshot, build-threads=8
  matrix in flight): an UNGUARDED same-module caller of a `@cfg(arm64)`
  function compiles with zero errors — so active guarded declarations
  PARSE and resolve locally; they are only missing from the frozen module
  SURFACE that cross-module import probes. Suspect: the full-inventory
  surface index path (the `runtime_std_full_inventory_selection` authority
  in driver_source_pipeline_parsing.spl) records guarded declarations
  under a variant tag the active-variant probe does not match. Fix belongs
  in the surface registration/index path, not the preprocessor.

- Update 2 (same day, deeper): the diagnostic prints
  `MISSING from parser functions table (functions=1 callables=1)` for the
  repro's provider module — so the drop is at PARSE-TO-MODULE-TABLE
  registration, before surface construction. Local resolution still works
  because it hits the compile-wide flat global registry (package-sibling
  semantics), which records declarations the module table misses.
- Discriminator experiments against the instrumented snapshot:
  `@when(os="macos")` (active) guard: compiles CLEAN, import works.
  `@cfg(arm64)` (active): fails. `@cfg(x86_64)` (inactive): declaration
  truly absent. So the bug is specific to ACTIVE `@cfg` per-declaration
  guards; `@when` blocks were fixed by 85c2bcc828c (2026-10-06) but the
  `@cfg` form was routed around (`@workaround` directives in
  path_identity_abi.spl) rather than fixed.
- ROOT CAUSE FOUND AND FIXED (2026-10-08): `cfg_detect_arch()` in
  `src/compiler/10.frontend/core/cfg_platform.spl` returned "unknown" on
  macOS — the env-var probes are unexported there and the /proc fallback
  is Linux-only. Every `@cfg(arch)` guard therefore evaluated FALSE in
  the ambient preprocessing path, so ACTIVE guarded declarations were
  stripped before parse (pp-diag: `arm64_eval=false` on an aarch64 host).
  The parser module table — and therefore the HIR module surface — lost
  those declarations, while the compile-wide flat global registry still
  resolved same-module uses (why local callers compiled clean). The seed's
  Rust arch detection is host-correct, which is why only the self-hosted
  compiler failed.
  Fix: host_arch() fallback (uname -m via the runtime, cached once per
  process) after the /proc probe. Verified with the instrumented rebuild:
  pp-diag now prints `arm64_eval=true` and the 2-file repro compiles clean
  (`succeeded=2`, no surface-diag, no "no exported item").
  Diagnostics (pp-diag / surface-diag) are still in the tree pending the
  matrix verification run; remove them before landing.
- Matrix verification (same day): the cfg fix took compiler_cli_build
  from 20 distinct HIR errors to ONE (`HIR aggregate failure; final worker
  and artifact publication blocked`) and test_runner_build now dies with
  a native-build worker SIGSEGV (exit -139). The remaining failure is the
  class-A export-origin family (reexport-chase-unresolved for text/i64/
  bool/Option at test_runner_types) plus a worker crash. NOTE: the
  segfault may be an artifact of the temporary diagnostics themselves —
  pp-diag prints from parallel HIR workers can corrupt the worker
  protocol stream. Next run: strip the diagnostics, rebuild, re-verify;
  then continue with the class-A export-origin bug.

## Suggested directions

1. De-duplicate the `99.loader` compat-vs-real surfaces: one definition per
   name (SmfCache, SmfCacheManager, native_mmap_file) with the compat module
   re-exporting instead of redefining (the compiler_sffi.spl header comment
   shows this was done for TypeInfo/CompilerContext in a prior fix — extend
   the same pattern).
2. For per-arch definition sets (byte_utils, elf_loader): split into
   per-arch modules selected into the build closure per target (the
   codebase's backend_vulkan/backend_metal idiom), or give each variant a
   distinct private name with a single active `@cfg` dispatcher whose export
   the registry can resolve.
3. Re-run the matrix after either fix; the suite rows
   (compiler_bootstrap/interpreter/loader) should then produce real counts.

## Evidence

- lane log: build/bootstrap-cran.log (worktree wt/render-harden-rel-20261005)
- matrix logs:
  .simple/storage/build/bootstrap/stage2-compiler-tests/aarch64-apple-darwin/verification/logs/{compiler_cli_build,test_runner_build}.log
- 20 distinct errors total (16 class A + 4 class B).
