# x86 bootstrap Rust authority tuple rebuild delays Stage 2

Status: OPEN (P2)

## Summary

A clean, current-source x86_64 Rust authority build spends more than twenty-three
minutes in four serial Cargo invocations before Stage 2 can start. The seed is
followed by three separately fingerprinted authority archive builds. Shared
compiler dependencies, including LTO-heavy `simple_compiler`, are compiled more
than once because the package feature/profile tuples differ.

The separation is currently correctness-sensitive: combining the packages in
one Cargo command unifies features and changes the admitted runtime tuple. The
performance bug is the repeated work, not the existence of distinct admitted
artifacts. A fix must preserve the exact seed, native-all, runtime symbol-table,
and compiler-backfill identities.

## Reproduction

Source revision: `e675a806153470478be0e1e36b1426b31c0a7bc2`

Host and toolchain:

- `x86_64-unknown-linux-gnu`
- Rust/Cargo 1.91.1
- LLVM 18.1.8

Command:

```sh
SIMPLE_NO_STUB_FALLBACK=1 \
SIMPLE_LLVM_DIAGNOSTIC_DIR=build/native_probe/x86_bootstrap_readiness/llvm-diag \
sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --stop-after-stage2 --backend=llvm --mode=dynload \
  --jobs=1 --output=build/native_probe/x86_bootstrap_readiness/bootstrap
```

The output and every Cargo target/cache are isolated below
`build/native_probe/x86_bootstrap_readiness/`. No pre-existing seed or runtime
archive is accepted as evidence.

## Measured evidence

The canonical Cargo logs report:

| Authority build | Cargo wall time | Maximum sampled process-tree RSS |
| --- | ---: | ---: |
| `simple-driver` seed, LLVM | 9m56s | 3,271,328 KiB |
| `simple-native-all`, LLVM | 10m00s | 2,165,916 KiB |
| `simple-runtime`, `runtime-symbol-table`, no LTO | 1m25s | 1,129,568 KiB |
| `simple-compiler-backfill` | 2m00s | 746,268 KiB |
| Total Cargo critical path | 23m21s | 3,271,328 KiB peak |

The wrapper reached the Stage-2 milestone after 26m21s and had retained about
2.6 GiB of isolated authority/cache material. The extra three minutes were
authority publication, hashing, copying, and provenance setup. These values
come from `rust-*-build.log` and `bootstrap-progress.log` in the reproduction
tree; they are not estimates from stale artifacts.

## Interrupted retained-cache follow-up

After rebasing the task branch onto `origin/main`, one cache-preserving rerun of
the exact Stage-2 native-build command was started with the preserved authority
binary (`sha256:25e1b2f2bacb97a08da2cef9f32ae0d47762d4eb05650e9fc5484dc40547b2b3`).
That authority was built at the earlier source revision above, so it was useful
for locating the next failure but was not current-source proof after the rebase.

A user sync/push override interrupted the rerun with SIGTERM at 2h05m55s. It
reached 1,373 cached objects and 51,389,973 cache bytes from a baseline of 741
objects and 26,693,309 bytes; maximum RSS was 1,061,272 KiB. The only emitted
diagnostic was the pre-existing unresolved `raise` warning in generated
`hir_walk_unhandled`; no terminal compiler error or LLVM diagnostic was emitted.

This interrupted run is explicitly **UNVERIFIED**. It does not establish a
Stage-2 artifact, identity, admission, sanity, Stage 3, or Stage 4 result.

## Likely ownership

`scripts/bootstrap/bootstrap-from-scratch.sh` deliberately runs the four Cargo
commands separately to avoid feature unification. The shared Cargo target
preserves dependency output where fingerprints agree, but the LLVM/native-all
and compiler-backfill graphs still rebuild expensive compiler units under
different feature or linker/LTO fingerprints.

Profile the complete authority graph before changing a leaf. Candidate fixes
include separating archive-only code from the compiler dependency graph,
sharing feature-invariant compiler artifacts across admitted tuples, or adding
an explicit multi-output build that does not unify runtime features. Do not
weaken provenance, silently reuse an unknown tuple, or replace current-source
build evidence with a cached stale binary.

## Acceptance criteria

1. Preserve byte- and provenance-correct seed, native-all, runtime symbol-table,
   and compiler-backfill artifacts for the same source/toolchain tuple.
2. Demonstrate which compiler units are rebuilt and why using Cargo timing or
   fingerprint evidence; optimize the dominant repeated work.
3. Reduce clean pre-Stage-2 authority wall time by at least 30% on the same
   x86_64 host without increasing peak RSS or isolated cache size by more than
   10%.
4. Demonstrate warm authority reuse with exact source/toolchain invalidation;
   `Unknown` must rebuild rather than reuse.
5. Complete admitted Stage 2 and Stage 3 with
   `SIMPLE_NO_STUB_FALLBACK=1`, then pass the Stage-3 provenance and sanity
   gates. Stage 4 remains a separate required production gate.
