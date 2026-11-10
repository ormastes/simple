# Bootstrap is NON-DETERMINISTIC on a fresh `origin/main` tree with a fresh seed (2026-09-01)

Status: **SUPERSEDED as root-cause tracker 2026-11-11** — the live defect is
owned by `native_codegen_object_nondeterminism_2026-10-25.md`; stage-chain
re-verification remains BLOCKED-needs-grant (host-heavy). Original report
below retained for history.

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

## Triage 2026-11-10 (p3-boot3 lane, assignment row 23)

**Verdict: SUPERSEDED as root-cause tracker (newer open bug owns the defect);
stage-chain verification BLOCKED-needs-grant (heavy).**

The mismatch is compiler output nondeterminism, not the `build bootstrap`
determinism gate (the 2026-10-27 ledger triage agrees: the gate "is not the
defect"). The current root-cause tracker is
`native_codegen_object_nondeterminism_2026-10-25.md` — objects differ between
runs of ONE binary even in no-fork mode, with real code differences
(`Label.message` 284 vs 700 bytes, 2 vs 4 `rt_alloc` calls across runs) — the
exact "same size class, different bytes" signature this report recorded. A
partial emission-order root cause was already fixed per
`native_build_symbolid_dict_emission_nondeterminism_2026-10-19.md`
(2026-10-19, "fixed (compiler emission sites sort canonically)"), but the
2026-10-25 observation postdates that fix, so this row cannot be closed from
source review alone.

Verification needs a built compiler on a POSIX host (none exists on this
Windows lane host; building the seed is heavy and forbidden here). Exact
commands for the granted lane:

```sh
# Cheap probe first (from the 2026-10-25 bug): build a fixed closure twice,
# no fork workers, compare per-object digests.
SIMPLE_MIR_FORK_WORKERS=0 <compiler> native-build <fixed 142-module closure> -o /tmp/probe-a.bin
SIMPLE_MIR_FORK_WORKERS=0 <compiler> native-build <fixed 142-module closure> -o /tmp/probe-b.bin

# Then the stage chain, three runs from one seed on the pinned archive:
for i in 1 2 3; do
  build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple native-build \
    --source src/compiler --source src/app --source src/lib \
    --entry-closure --entry src/app/cli/bootstrap_main.spl \
    -o build/review/determinism-probe-$i.bin
done
sha256sum build/review/determinism-probe-*.bin   # all equal -> this row closes
```

`cmp -l` on a fresh mismatching pair (and a `SOURCE_DATE_EPOCH`-pinned
rebuild) remains the first byte-level step, per this doc's "Not investigated
here".

---

## Triage 2026-11-10 (P3 compiler-seed lane, work/p3-seed-20261110)

Verdict: **STALE-BLOCKED (host-limited — repro not completable in this lane)**.
Attempted a same-input double-build probe on the Windows lane with a fresh seed
built from this base (`cargo build --offline --profile bootstrap -p simple-driver`,
rc 0, 2m32s, CARGO_TARGET_DIR under the lane worktree; the binary reports
`build-commit: 1504212d788b`). Three probe attempts, none reached a pair of
output artifacts:

1. `native-build` of a trivial `fn main` probe refused by SCV stage-3 admission
   (`source-inventory-scope-unsupported`) until the entry was moved under
   `test/` — probe-layout constraint, not the bug.
2. Admitted full-closure dynload build ran >34 min of CPU (RSS pinned ~1.5 GB,
   no phase output after the semantic log) and was stood down per lane budget —
   the whole-compiler closure build dominates the probe cost on this host.
3. `--emit-entry-object` bounded retry refused twice by the seed's own memory
   reserve gate (`SIMPLE_BUILD_MEMORY_RESERVE_BYTES`, 24576 MiB reserve vs
   19-20 GiB free headroom) because the shared host was under load from other
   lanes; lowering the reserve was rejected as it would defeat a working guard
   under genuine memory pressure.

No output pair was produced, so the byte-difference question this record
defers ("Not investigated here: which bytes differ") remains open. Recommended
next step unchanged from the original record, on the Linux lane where the
mismatch was observed: run the three identical `native-build` invocations
there and `cmp -l` the outputs with `SOURCE_DATE_EPOCH` pinned. No seed change
made; the fresh-seed build artifacts remain under
`build/p3-seed-20261110/cargo-target/` in the lane worktree (git-ignored).

## Triage 2026-11-11 (P3 boot11 lane, work/p3-boot11-20261111)

**Verdict: SUPERSEDED as root-cause tracker; stage-chain verification
BLOCKED-needs-grant.** Corroborates the 2026-11-10 lanes: the current
root-cause tracker `native_codegen_object_nondeterminism_2026-10-25.md`
exists at this base (objects differ between runs of ONE binary even in
no-fork mode — the same "same size class, different bytes" signature this
report recorded); the 2026-10-19 emission-order fix
(`native_build_symbolid_dict_emission_nondeterminism_2026-10-19.md`)
predates the 2026-10-25 observation, so closure requires a rebuilt compiler
on a POSIX host. This Windows lane has a fresh seed
(46fe8f6b6def) but no POSIX compiler build and no cargo/rustc permission;
whole-compiler closure native builds are forbidden here (and the Windows
native-build hang is a known live defect).

Exact commands for the granted lane (unchanged from 2026-11-10):

```sh
# Cheap probe first (from the 2026-10-25 bug): build a fixed closure twice,
# no fork workers, compare per-object digests.
SIMPLE_MIR_FORK_WORKERS=0 <compiler> native-build <fixed 142-module closure> -o /tmp/probe-a.bin
SIMPLE_MIR_FORK_WORKERS=0 <compiler> native-build <fixed 142-module closure> -o /tmp/probe-b.bin

# Then the stage chain, three runs from one seed on the pinned archive:
for i in 1 2 3; do
  build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple native-build \
    --source src/compiler --source src/app --source src/lib \
    --entry-closure --entry src/app/cli/bootstrap_main.spl \
    -o build/review/determinism-probe-$i.bin
done
sha256sum build/review/determinism-probe-*.bin   # all equal -> this row closes
```
