# seed_rust_build_not_reproducible_2026-11-02

**Severity:** P3 (perf and reproducibility. Blocks the fixpoint/reproducible-bootstrap story.)
**Status:** open

## Observation
I built `cargo build --profile bootstrap -p simple-driver --features llvm` twice from identical
`src/compiler_rust` trees (release 1.0.0, same worktree, same CARGO_TARGET_DIR, llvm-mingw, CC=clang-cl).
The two runs produced different `simple.exe` digests:
`36336a97feec…` and `34884dbd5a6c…`.

## Impact
The native-build object cache keys on the compiler binary. A rebuilt seed with
unchanged source therefore rebuilds all ~1540 stage2 objects (about 20 min) when it could reuse them.

## Next steps
- Diff the two binaries by section and find the source: embedded timestamps or paths, the build-script `env!`, LTO or CGU partition nondeterminism, or the `SOURCE_DATE_EPOCH` handling.
- Spec: `test/01_unit/compiler/bootstrap/seed_rust_build_reproducible_spec.spl` (pending until fixed).
