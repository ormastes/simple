# Bootstrap is NON-DETERMINISTIC on a fresh `origin/main` tree with a fresh seed (2026-09-01)

Status: **OPEN**. Found while trying to produce an admissible pure-Simple
compiler for the arm64 WM+Vulkan pixel-evidence lane.

## Reproduce

Worktree: fresh `git worktree add --detach origin/main` (`5e09b3ef2fd`) plus the
three commits of PR #273 cherry-picked. Seed: fresh
`cargo build --release --bin simple` (rc 0), deployed only inside that worktree
at `bin/release/x86_64-unknown-linux-gnu/simple` — the shared deployed binaries
were NOT touched.

```
SIMPLE_TIMEOUT_SECONDS=0 SIMPLE_CACHE_SCOPE=goal2arm64 <fresh seed> build bootstrap
```

## Result

Every stage builds and links successfully, and all three outputs are
**byte-identical in length** — but all three sha256s differ:

```
Stage 3: OK (28480840 bytes, hash=9f81b567...)
Inputs stable: 16177 source file(s), tree=a38d7541672c5ea00e5f8235a83aa5f2bf32c74804f368b47e06d4c44c86dfe6

Bootstrap MISMATCH: outputs differ between stages
  Stage 1: 065addc8d0153735c61842659d99b2e300e3f148768e75fad8efca2ab7877221 (28480840 bytes)
  Stage 2: eb6af34dde8d2635608b88e730d9fd85fdabd4a3400e68901b8a13b97a37607f (28480840 bytes)
  Stage 3: 9f81b56783137edd71438672fea0ad65c9137edd3f80e985d6f940d6a1db8f6f (28480840 bytes)
```
rc 1.

The pipeline itself reports `Inputs stable` for the pinned snapshot, so the
input tree is identical across the three stages; the non-determinism is in the
compile/link, not in the sources. Equal sizes with unequal hashes points at
embedded non-reproducible content (ordering, timestamps, paths, or an unstable
symbol/section order), not at a semantic difference.

Note the stages are NOT all compiled by different compilers — the log shows all
three invoking the same `bin/release/x86_64-unknown-linux-gnu/simple
native-build ... --entry src/app/cli/bootstrap_main.spl`, i.e. the same seed
three times on the same snapshot. That makes this a plain reproducibility bug.

## Why it matters here

`bootstrap` exiting 1 means no stage is *admitted*, even though `stage3/.../simple`
(28480840 bytes) exists and runs. Every downstream provenance consumer —
`bootstrap-stage3-provenance.shs`, `stage4-candidate-provenance.shs`,
`scripts/check/admit-simpleos-arm64-server-compiler.shs`, and therefore
`SIMPLEOS_ARM64_ATTESTED_COMPILER` for
`scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs` — rests on a
verified stage chain. So this blocks the only supported route to the pure-Simple
Stage 4 full CLI the arm64 attested build requires (see
`arm64_attested_build_rejects_rust_seed_by_design_2026-09-01.md`).

## Not investigated here

Which bytes differ. `cmp -l` across the three artifacts, and a rebuild with
`SOURCE_DATE_EPOCH` pinned, are the obvious next steps.
