# cargo 1.100 nightly build-dir layout drift breaks the Rust authority publish path

Date: 2026-09-16
Branch: work/image-memory-budget-20260915 (merged origin/main @ e5ffe745ce9)
Host: Windows 11, Git Bash (MINGW64), x86_64-pc-windows-gnu

## Symptom

`--full-bootstrap` (the receipt-free Stage-2 trust-root lane) compiles all four
Rust lanes successfully and then aborts at the immutable-generation publish:

```
bootstrap_stage3_copy_seed_tuple: failed check 4
bootstrap_stage3_prepare_seed_generation: failed check 4
error: could not prepare immutable Rust authority generation
VERDICT — ABORTED: stage=rust-rust-compiler-backfill-build exit=1
```

## Root cause

cargo 1.100.0-nightly (7941be6fb 2026-09-11, rustc 215a8af4b 2026-09-15) ships
the new build-dir filesystem layout unconditionally: the per-profile `deps/`
directory is no longer created. Final crate artifacts are written directly into
the profile directory, and dependency rlibs are no longer materialized as
individual files.

Verified with a minimal two-crate path-dependency project on this host:

- `cargo build` (any profile) -> `target/<profile>/` contains only final
  artifacts (`ct.exe`, `ct.d`); NO `deps/` directory is created.
- `-Z build-dir-new-layout` and `[build] build-dir-new-layout = false` do not
  restore the old layout (tested both; flag description still says "Use the new
  build-dir filesystem layout").

The authority publisher `bootstrap_stage3_copy_seed_tuple`
(scripts/check/lib/bootstrap-stage3/authority.shs:2021) hard-requires the old
layout:

- check 4: `$source/deps` must be a real directory (absent under new cargo).
- runtime archive derived as `deps/libsimple_runtime.a` (now profile-root).
- hosted archive discovered as `deps/libspl_hosted_runtime-*.rlib` — this rlib
  is NOT materialized at all by new cargo (only final selected-package
  artifacts are), so there is no in-tree file to copy.

`deps/` layout assumptions are additionally baked into:

- scripts/bootstrap/phase2-runtime-capsule.shs:60,63,105
- scripts/bootstrap/bootstrap-phase-verification.shs:59,65
- scripts/check/lib/bootstrap-stage3/sanity.shs:556

The comment at src/compiler_rust/native_all/Cargo.toml:46-57 documents the
two-rlib-in-deps behavior this gate was written for.

## Why CI is green

The Windows/Linux Stage-2 CI lanes reuse a warm Rust-seed cache keyed by the
cargo-inputs fingerprint, so the rebuild + publish path never executes there.
The drift only surfaces on a machine with a stale/absent seed (fresh clone or,
as here, a tree whose src/compiler_rust or src/runtime content changed).

## Reproduce

1. Invalidate the seed (touch any file under src/compiler_rust or
   src/runtime), or use a fresh clone.
2. `sh scripts/bootstrap/bootstrap-windows.sh --full-bootstrap --stop-after-stage2 --backend=cranelift --jobs=min`
3. Wait through the four Rust lanes (~35 min at jobs=1); publish aborts.

## Impact

- No fresh machine can complete even the Stage-2 trust-root lane with current
  nightly cargo. The whole self-host chain (Stage 2 -> planner admission ->
  Stage 3/4) is closed to anyone without a warm seed cache.
- The check worker (`simple check`) and the native MCP servers cannot be
  produced, so `check src/app/mcp`, `check src/app/simple_lsp_mcp` and the
  MCP stdio integration spec stay red on affected machines.

## Evidence (this run)

- Fingerprint-keyed cargo target:
  build/c/a59b2e0e2e98d4b5199878c1fa66c9804260abc4673fa517a260d8649876f173/x86_64-pc-windows-gnu/bootstrap/
  contains 19 entries: simple.exe, simple-stub.exe, simple_runtime.dll,
  libsimple_driver.rlib, libsimple_native_all.a, libsimple_runtime.a/.rlib/
  .dll.a, libsimple_compiler_backfill.a, .d files. NO deps/ subdir.
- `find <target> -name 'libspl_hosted_runtime*'` -> no results.
- Bootstrap main log: /tmp/bootstrap_s2f.log (VERDICT ABORTED at stage=rust).

## Suggested direction

Teach the authority layer to accept the new layout: resolve the artifact dir as
`$source/deps` when present else `$source`, and source the hosted-runtime rlib
from wherever cargo materializes it — or emit it explicitly (e.g. build
spl_hosted_runtime with `--emit=link` crate-type rlib via a dedicated cargo
invocation) when cargo no longer leaves one in the target dir. All five
deps/-layout call sites listed above must change together; the tuple must stay
internally consistent because the phase-verification and sanity gates re-derive
the same paths.

## Update 2026-09-17 (LLVM prebuilt landed; admission decoupled)

The user directed downloading a prebuilt LLVM binary. Both clang+llvm-23.1.1
and clang+llvm-18.1.8 (x86_64-pc-windows-msvc) are installed under C:\llvm-23
and C:\llvm-18. LLVM 18 satisfies the llvm-sys 180 pin; 23.1 is kept as a
spare (the seed's llvm-sys cannot consume it, but the pure-Simple loader
tolerates any LLVM-C.dll).

The MSVC-LLVM-on-GNU static link was fought to a standstill over three
defects (rustc windows-gnu does not search <name>.lib for `static=` deps;
the tarball ships no libxml2s.lib; llvm-config --link-shared wants
LLVM-18.dll which this distribution lacks) plus cargo's treatment of
vendored sources as immutable (build-script edits need fingerprint
dirs cleared). inkwell no-llvm-linking leaves real LLVM symbols undefined.

Landed instead (commit 4537af34d90): the bootstrap lane never exercises
the seed's inkwell codegen -- the seed drives the pure-Simple compiler,
which loads LLVM-C.dll directly -- so the LLVM availability gate now
accepts a runtime-proven SIMPLE_LLVM_PATH, the seed builds feature-free
under SIMPLE_BOOTSTRAP_RUST_LLVM=0, and the lane runs
--backend=cranelift with LLVM discovered. The frontend sanity smoke
follows the seed's capability (cranelift), and the frontend cache is
disabled under low memory (the ~10GB growth term).

Validated end-to-end to the final two gates:
- the candidate's install_selected_k1_backend_table_v1 still answers
  false inside the smoke (the k1-table diagnostic pinpoints the failing
  sub-check; needs one focused look at the compiled candidate's table
  construction),
- the hello-world positional smoke exits 126 with its capture logs not
  materialising (infrastructure-failure path in
  scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs).


All of the above is now FIXED on branch work/image-memory-budget-20260915
(commits 8eddea9e1ed, 08d6fb9599e): the authority tuple resolves both cargo
layouts, `-p spl_hosted_runtime` is selected in the native-all lane, the
capsule/phase-verification/sanity globs accept the unsuffixed rlib spelling,
and the MSYS mode-bit exemptions are applied. The Stage-3 git-bind C# consumer
— which had never completed on ANY host — additionally needed: skipping
tree/gitlink ls-tree rows, accepting `[`/`]` in paths (14 Google-Fonts
variable-font files), recursive `ls-tree -r`, budget defaults corrected to the
measured 1M entries / 300 s (from 100k / 28 s), submodule-gitlink subtree
skips, and a stale-artifact clean of git-ignored build dirs with broken
reparse points.

With all of that, the chain now runs from scratch to the FINAL gate:

  PLUG-E-K1-POLICY: bootstrap backend composition admission failed
  (selected policy 'llvm-cranelift')

The committed K1 composition (src/compositions/kernel_llvm_cranelift) requires
an LLVM backend kernel-linked alongside cranelift and the interpreter
(static_backend_registry.spl validate_k1_static_backend_table_v1). This host
has no usable LLVM-C.dll: its LLVM 23.1.0 build omits the C API library, and
the Rust llvm-sys 180 pin requires LLVM 18 anyway. CI never sees this because
the same warm-seed cache skips the whole lane.

Remaining options (need a maintainer decision):
1. Install an LLVM 18.1.x Windows release with LLVM-C.dll; everything then
   works as committed. (SIMPLE_BOOTSTRAP_RUST_LLVM=0 now also lets a newer
   LLVM serve the pure-Simple backends alone when LLVM-C.dll is present.)
2. Land a committed cranelift-only K1 composition (new composition dir +
   registry policy + admission wiring) for low-dependency bootstrap hosts.
3. Keep the Rust seed for day-to-day test runs on this host.

