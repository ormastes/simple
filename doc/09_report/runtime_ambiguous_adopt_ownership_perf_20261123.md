# Indexed ownership for ambiguous transient heap adoption

The macOS bootstrap P2 warmup sampled on 2026-11-23 spent all248 samples in a three-second window in `TransientHeapScope::owns_heap_ptr`, reached through `rt_transient_heap_adopt` and the parse-closure chunk checkpoint. The sampled compiler was the frozen P2 at `/tmp/simple-rc-build-20261122/recovery-20261123/phase2-frozen`; the sample is retained in `recovery-20261123b/p2-warmup.sample.txt`. This is evidence for that window, not a whole-build profile.

`owns_heap_ptr` used a linear scan whenever duplicate tracked addresses made the scope index ambiguous. Adoption asks this question for each reachable heap node. The resulting cost was O(reachable nodes × tracked objects), even though an address index already existed. The owner was unchanged between the producer source dd52d605f41c and reviewed release source84ea108c7c9, so the newer Simple HIR/cache fixes did not remove this runtime hotspot.

Every heap address has one canonical `RuntimeValue` bit pattern: address plus `TAG_HEAP`. All duplicate entries for an address therefore have the same exact-bit promotion status. The repair uses the existing address index and promoted set for ownership even in ambiguous scopes, while preserving slot/pointer validation. Deferred duplicate compaction is unchanged. Explicit array frees still remove indexed ownership and every duplicate; already adopted roots still prune.

## Verification

Runtime-only tests used a private APFS-cloned Cargo target, two jobs, the bootstrap profile with LTO off, and target `aarch64-apple-darwin`. No seed compiler binary or live producer was rebuilt or modified.

- New real duplicate-graph adoption and existing session-pruning checks:2PASS.
- Existing ambiguous/indexed promotion and lifetime checks (`bsm_p0_`):5PASS.
- Existing free, duplicate-untracking and address-reuse checks (`array_free_`):13PASS.
- At20,000 real child arrays with duplicate tracking, the old owner took542,492µs for adoption and the repaired owner took5,797µs, approximately93.6× faster in this single before/after pair. Both runs verified graph contents, session ownership, idempotent adoption and reclamation. This is not a whole-bootstrap speed claim.

The performance fixture accepts `BSM_ADOPT_AMBIGUOUS_N`; default256 keeps ordinary tests small. Benchmark command:

```sh
BSM_ADOPT_AMBIGUOUS_N=20000 CARGO_BUILD_JOBS=2 \
CARGO_PROFILE_BOOTSTRAP_LTO=off CARGO_TARGET_DIR=<private-target> \
cargo test --locked --offline --profile bootstrap \
  --target aarch64-apple-darwin -p simple-runtime --lib \
  bsm_p1_adopt_ambiguous_index_preserves_ownership -- --nocapture
```

Local logs: `/tmp/simple-runtime-adopt-tests-20261123.log`, `/tmp/simple-runtime-adopt-baseline-20261123.log`, `/tmp/simple-runtime-adopt-fixed-bench-confirmed-20261123.log`, `/tmp/simple-runtime-adopt-ambiguous-promotion-20261123.log`, and `/tmp/simple-runtime-adopt-freed-address-20261123.log`. An intermediate misnamed fixed-bench log reran the baseline after a failed relative-path copy; it is excluded from the comparison.

## Artifact integration

A source-only merge does not repair an already linked compiler. Future P3/P4 artifacts must link refreshed runtime packages. The existing `libsimple_native_all.a` contains17 `simple_runtime` members, but replacing only those without matching Rust metadata/features can break private symbol references. Rebuild the normal `simple-native-all` and backfill runtime packages in an isolated source/cache owner, preserving the live producer and runtime directory. Build no Rust seed executable. A standalone C `libsimple_runtime.a` capsule cannot be substituted for native-all/backfill by renaming it. Any relinked P2 candidate must use recorded linker argv, a fresh output and exact Hello compile-and-run evidence before a dependent phase.
