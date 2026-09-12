# Resolution cache key stats `cpu_config.sdn` once per module resolution

- Status: OPEN (2026-09-12)
- Area: compiler / seed module resolution (interpreter lane)
- Found by: lane L3 (interpreter/compiler startup), while landing
  `stdlib_root_candidates_present`
- Binary: `bin/release/aarch64-unknown-linux-gnu/simple.l3`, sha256
  `a51e47d5c4df…`, built from `79a67e79135` + this session's two commits, aarch64

## What

`compute_cache_key` (`src/compiler_rust/compiler/src/interpreter_module/path_resolution.rs:69`)
hashes `active_simd_tier_name()` into the resolution cache key:

```rust
fn compute_cache_key(parts: &[String], base_dir: &Path) -> u64 {
    let mut hasher = ahash::AHasher::default();
    parts.hash(&mut hasher);
    base_dir.hash(&mut hasher);
    active_simd_tier_name().hash(&mut hasher);   // <- one fs::metadata per call
    hasher.finish()
}
```

`active_simd_tier_name()` -> `active_simd_tier()` -> `host_cpu_config()`
(`src/compiler_rust/simd/src/host_config.rs`) re-stats
`$HOME/.cache/simple/host/<triple>/cpu_config.sdn` on **every** call, by
design: the cache there keeps an on-disk fingerprint so a mid-process edit is
seen. The key is computed once per resolution, so the stat is paid once per
resolution.

## Repro

```sh
sh scripts/check/check-stdlib-variant-probe-waste.shs --lane interpreter
```

on this tree reports `cpu_config=132` for `simple check --help` — 132 stats of
one file that cannot have changed. Measured before this session's guard landed
the same command reported `cpu_config=353`; running one tiny spec
(`bin/simple test test/01_unit/app/examples_check_entry_args_spec.spl` under
`strace -f -e trace=openat,stat,newfstatat,statx`) reported 3,244 before and
1,203 after.

## Why it was not fixed here

Memoizing the tier for the key is a **behaviour change** and is pinned by two
cargo tests in the same file:

- `cache_key_changes_with_simd_tier` (`:1427`)
- `cache_key_changes_with_configured_active_tier_without_override` (`:1438`) —
  writes two different `cpu_config.sdn` documents and asserts the key differs,
  i.e. it asserts the per-call re-read.

So the fix is not "add a memo": it is a decision about whether the resolution
cache should track a mid-process tier flip at all, when every cache next to it
(`fs_probe::PATH_KIND_CACHE`, `DIR_LISTING_CACHE`, `IMPORTED_MODULE_AST`,
`MODULE_EXPORTS_CACHE`) is a plain per-process memo with no stamp. That
decision, and the two tests, belong to whoever owns the resolution cache.

## Suggested shape

Sample the tier once per resolution *batch* rather than per key — or make the
resolution cache honestly per-process like its neighbours and delete the tier
from the key, updating the two tests to assert the new contract explicitly
rather than by side effect. Either way it wants to be a deliberate, reviewed
change, not a silent optimisation.
