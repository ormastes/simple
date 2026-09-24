# Shared Cargo target dir (`build/c/<config-key>` / `rust-cargo-target-<config-key>`) has no reaper

**Date:** 2026-09-24
**Severity:** low (disk growth, not correctness -- see the companion fix this
todo was filed alongside)
**Status:** open -- deliberately NOT fixed in this pass; filed instead of
attempting a risky same-pass cleanup
**Path:** `bug` / disk-hygiene track.

## Context

`scripts/bootstrap/bootstrap-authority-wiring.shs`
(`bootstrap_authority_rust_cargo_target`, called from
`scripts/bootstrap/bootstrap-from-scratch.sh`) selects a CARGO_TARGET_DIR
keyed by a 12-hex build-CONFIGURATION key
(`bootstrap_authority_rust_build_config_key`: rustc/cargo identity, target
platform, backend/features, LLVM version, CFLAGS/RUSTFLAGS, C toolchain,
`.cargo/config.toml` contents) -- `build/c/<12-hex>` on Windows,
`<sibling-of-authority-root>/rust-cargo-target-<12-hex>` elsewhere. This
directory is shared and reused across every seed-input CONTENT fingerprint
under the SAME configuration (that is the whole point: a test-only/comment-only
Rust source edit reuses cargo's own incremental cache instead of forcing a
cold rebuild), and is deliberately never removed by the ordinary build path
(`bootstrap_authority_rust_cargo_target`'s header comment: "This selector
never moves/removes data").

Switching build configuration (backend llvm <-> cranelift, an LLVM version
bump, a toolchain rollback, `SIMPLE_BOOTSTRAP_RUST_LLVM` toggling) selects a
DIFFERENT 12-hex key and therefore a brand-new, empty target dir. Each
configuration a host has ever built under leaves its own full Cargo target
dir (measured order of magnitude for a single crate's subgraph alone: several
hundred MB; a full `simple-driver` + `simple-native-all` + `simple-runtime`
+ LLVM-feature target dir is larger) sitting on disk indefinitely, with
nothing reaping old ones.

This is the SAME class of finding already on record for the OLD,
content-fingerprint-keyed scheme (`bootstrap-from-scratch.sh:920`'s
`build/w/rust-authority-*` mention, and
`bootstrap_authority_prune_generations`, which only reclaims
`bootstrap.generations/`, never `rust-authority-*` roots or their target
subtrees) -- moving from a content key to a configuration key SHRINKS the
practical blast radius (a host typically only ever builds a handful of
distinct configurations, vs. one new directory per source-content change),
but does not add a reaper.

## Why not fixed in the same pass

A correct reaper here needs to get several things right simultaneously, and a
mistake in ANY of them turns a disk-hygiene nice-to-have into a build
correctness incident (deleting a directory a concurrent or in-progress build
still needs):

1. **Never delete the directory currently in use.** The reaper must run
   strictly under the same Rust authority lock
   (`bootstrap_acquire_rust_authority`) that serializes cargo invocations,
   and must exclude the CURRENT `rust_authority_config_key`'s directory
   unconditionally -- not just "the most recent," since a retried build with
   an OLDER config key (e.g. a deliberate toolchain rollback mid-session)
   must not have its own in-progress directory reaped out from under it.
2. **Recognise orphaned LEGACY directories from the previous (content-keyed)
   scheme** -- `build/c/<64-hex>` and `rust-authority-*/target` -- without a
   false-positive match against the new `build/c/<12-hex>` /
   `rust-cargo-target-<12-hex>` naming (12 hex chars vs. 64 hex chars is an
   easy, safe discriminator, but this still needs its own test fixtures
   rather than being bolted on to the existing path-selection tests).
3. **Bound by "keep current + N most recent by mtime,"** which means walking
   `build/c/*` (Windows) or the authority-root's siblings (other platforms)
   and comparing directory mtimes -- straightforward on POSIX, but Windows
   directory mtime semantics under MSYS/cygpath have already caused at least
   one incident class in this area (the MAX_PATH work these two functions
   already carry scar tissue from), so this needs its own careful, tested
   implementation rather than a quick bolt-on.
4. Must run "only while holding the authority lock," per the review that
   requested this, which means the deletion path has to be threaded through
   `run_rust_authority_cargo` / `prepare_rust_authority_workspace` at exactly
   the right point (after a successful build, before lock release) rather
   than added as an unguarded top-level step.

Given the fix this todo accompanies was already a HIGH-severity trust-defect
repair under active review, adding an `rm -rf`-capable cleanup path in the
same change was judged higher-risk than the disk growth it would address.
Filing this instead, per the reviewing coordinator's explicit
"if you judge cleanup risky, instead file a concrete todo" instruction.

## Proposed fix (not yet implemented)

Add a `bootstrap_authority_prune_cargo_target_configs` alongside
`bootstrap_authority_prune_generations` in
`scripts/bootstrap/bootstrap-authority-wiring.shs`, following that function's
existing pattern exactly (require an owned lock, refuse to guess when state
is ambiguous, name-safety check every candidate before touching it):

- List sibling directories matching `build/c/[0-9a-f]{12}` (Windows) or
  `<base>/rust-cargo-target-[0-9a-f]{12}` (other platforms).
- Exclude the CURRENT `rust_authority_config_key`'s directory unconditionally.
- Sort the rest by mtime; keep the `N` most recent (default 2, matching the
  review's suggestion), `rm -rf` the remainder.
- Separately, and unconditionally (no "most recent" allowance -- these are
  dead regardless of how old the shared-config-key scheme is), remove any
  sibling matching the OLD naming: `build/c/[0-9a-f]{64}` or
  `rust-authority-*/target`.
- Call it from `run_rust_authority_cargo` (or immediately after a successful
  `bootstrap_stage3_publish_seed_generation`) while
  `bootstrap_acquire_rust_authority`'s lock is still held.
- Needs its own `--selftest`-style fixture coverage (fixture dirs, not real
  multi-GB Cargo output) mirroring `bootstrap_authority_prune_generations`'s
  test discipline before this is wired into the live path.

## References

- `scripts/bootstrap/bootstrap-authority-wiring.shs`:
  `bootstrap_authority_rust_cargo_target`,
  `bootstrap_authority_rust_build_config_key`,
  `bootstrap_authority_prune_generations` (existing analogous reaper for a
  different directory class).
- `scripts/bootstrap/bootstrap-from-scratch.sh:920` (prior disk-consumer
  callout for `build/w/rust-authority-*`).
- Companion fix commits: `42aca030c16` (share target dir across content
  fingerprints), `940a4b9921a` (key by build configuration instead of
  content, closing the cross-configuration stale-artifact hazard the sharing
  introduced).
