# seed_rust_build_not_reproducible_2026-11-02

**Severity:** P3 (perf and reproducibility. Blocks the fixpoint/reproducible-bootstrap story.)
**Status:** LIVE (triaged 2026-11-11, lane boot23) — cargo/seed build-reproducibility defect routed to the seed-fix lane (cargo fixes are outside P3 bug lanes); no in-lane reproduction (cargo is forbidden in-lane; two ~10-min builds of identical source to compare digests is not a cheap probe).

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

## Addendum 2026-11-11 (lane boot23) — LIVE; routed to seed-fix lane (header OPEN -> LIVE)

Triage (no reproduction attempted in-lane): this record's defect is in the
cargo/Rust seed build itself — `cargo build --profile bootstrap -p
simple-driver --features llvm` of identical source producing different
`simple.exe` digests (embedded timestamps/paths, build-script `env!`, LTO/CGU
partition nondeterminism, or `SOURCE_DATE_EPOCH` handling). Per campaign
routing, cargo fixes belong to the seed-fix lane, and the probe (two ~10-min
identical builds plus a section-level binary diff) is neither cheap nor
permitted here (no cargo/rustc in-lane).

Disposition: **LIVE**, owner seed-fix lane. Next steps per the record: diff
the two binaries by section to find the nondeterminism source; then land the
reproducibility fix (e.g. pinned `SOURCE_DATE_EPOCH`, deterministic
`env!`/paths, stable CGU partitioning) and only then promote the pending spec
`test/01_unit/compiler/bootstrap/seed_rust_build_reproducible_spec.spl` from
pending to green. Impact statement stands: the native-build object cache keys
on the compiler binary, so a rebuilt seed with unchanged source rebuilds all
~1540 stage2 objects (~20 min) when it could reuse them.
