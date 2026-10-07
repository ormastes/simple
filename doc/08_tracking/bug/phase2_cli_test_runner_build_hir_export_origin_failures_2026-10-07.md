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
