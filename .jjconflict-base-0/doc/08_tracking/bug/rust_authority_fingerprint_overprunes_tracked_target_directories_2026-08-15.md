# Rust authority fingerprint over-prunes tracked `target` directories

**Status:** open follow-up; pre-existing provenance coverage gap, not the
current Stage-2 publication blocker.
**Observed:** 2026-08-15.

`bootstrap_stage3_seed_inputs_fingerprint` prunes every directory named
`target`. That excludes legitimate tracked source inputs such as
`src/compiler_rust/vendor/cc/src/target/*.rs` and driver target fixtures, not
only Cargo's generated `src/compiler_rust/target` tree.

The generated-output fix for `compiler/build` and `compiler/.simple` deliberately
does not expand into this distinct category after its focused test passed.
A separate bounded change should anchor target pruning to the canonical Cargo
output root and add a sentinel proving nested vendored `target` source changes
alter the authority fingerprint, while the top-level Cargo target output does
not.

Provider token usage and comparable completed-bug average: unavailable.
