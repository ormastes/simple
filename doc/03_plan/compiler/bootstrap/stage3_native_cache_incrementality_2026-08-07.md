# Stage 2/3 bootstrap native-build cache incrementality

Status: partial fix landed 2026-08-07; residual scope below is NOT done.

## Root cause of the 0-byte stage3 cache (two layers)

**Layer 1 — unconditional wipe (fixed this pass).**
`scripts/bootstrap/bootstrap-from-scratch.sh` unconditionally `rm -rf`'d
`stage2_provenance_cache`/`stage3_provenance_cache` twice per run: once while
resetting provenance evidence (~line 1300, before Stage 2 even starts) and
again immediately before invoking Stage 3 (~line 1582). Every run therefore
started stage2 and stage3 from an empty cache dir regardless of whether any
source had changed since the previous run. `scripts/bootstrap/resume-stage3-from-admitted.sh`
had the same unconditional `rm -rf "$stage3_cache"` at line 89, even though
that script exists specifically to *resume* stage3 from an already-admitted
stage2 binary.

Fix landed: both scripts now only clear these cache dirs when a clean build
was explicitly requested (`--fresh-cache`/`--clean-release` in
bootstrap-from-scratch.sh; `RESUME_STAGE3_FRESH_CACHE=1` in
resume-stage3-from-admitted.sh). Otherwise the existing cache dir is kept and
just `mkdir -p`'d if missing. This mirrors the pattern
`bootstrap-from-scratch.sh` already used for the normal dynload
`native_cache_dir` (`prepare_native_cache`, ~line 675), which was never
applied to the stage2/stage3 provenance cache dirs.

Why this is safe (not a staleness risk): the pure-Simple driver's own cache
key is content-hash based, not mtime based (see Layer 2) — an unchanged
sources dir hits, any content change anywhere in the loaded closure produces
a different cache-scope directory and never reuses stale objects. There is no
code path that can serve a stale object for changed source under either the
old or new script behavior; the old behavior only made every run pay a full
rebuild even with zero source changes.

## Layer 2 — whole-closure fingerprint scoping (intentional, NOT changed this pass)

`src/compiler/80.driver/driver_aot_native_output.spl`:
- `driver_native_sources_fingerprint()` (line 101) hashes the content of
  **every loaded source file in the closure** into one combined manifest hash.
- That combined hash becomes part of `cache_scope_root` (line 266:
  `cache_scope_root = base_cache_scope_root/sources-{sources_fingerprint}`).
- Per-module object lookup (`driver_native_module_cache_source`, line 81) is
  keyed by module path only, but a hit additionally requires the cached
  object to live under the *current* run's `cache_scope_root`
  (`driver_native_build_filter_scoped_outputs`, checked at line 331).

Net effect: changing **one** file anywhere in the closure changes the combined
fingerprint, which changes `cache_scope_root`, which makes **every** module's
cache lookup miss — not just the changed module and its dependents. Two runs
over an *identical* source tree hit the cache almost entirely (Layer 1's fix
now lets that persist across process invocations); a run that touches even one
file still recompiles the whole closure.

This is a **documented, deliberate** design choice, not a bug:
`.claude/rules/bootstrap.md` -> "Dependency tracing intentionally
over-invalidates around AOP/MDSOC weaving, loader ABI, interpreter adapters,
execution mode, library path, and native-build environment knobs. Do not
narrow this to import edges until the AOP and loader contracts expose stable
cache keys." The same file separately tracks true per-module hardened-key
incremental reuse as a **follow-up not yet done** for the pure-Simple
self-hosted native-build path (it already exists in the Rust seed's
`native_project` pipeline via `SIMPLE_NATIVE_INCREMENTAL`).

**This plan intentionally does not attempt to narrow Layer 2.** Doing so
safely requires the AOP/loader ABI work called out in bootstrap.md; doing it
unilaterally here risks serving a cross-module-stale object under weaving/ABI
changes that the current coarse key protects against.

## What Layer 1's fix actually buys

- Repeated bootstrap runs on an unchanged tree (the common case for a
  shared/looping session) now reuse the stage2/stage3 cache instead of always
  starting cold — this is the majority of "incremental build" value for the
  stated directive ("bootstrap should be done with incremental build than
  full build").
- A single-file touch still triggers a full stage2/stage3 recompile of the
  loaded closure — expected under Layer 2, not a regression from this change.

## Verification performed / not performed

- `bash -n` on both edited scripts: pass.
- Code-level trace of the cache read/write/scoping path confirmed by reading
  `driver_aot_native_output.spl` (cache load, per-module hit/miss loop,
  existence-only integrity check at line 337, fingerprint construction).
- Full-scale A/B/C/D timing proof on the real stage3 closure (25min+ per run)
  was **not** performed in this pass: the pre-built `build/bootstrap/stage2`
  binary on disk (dated 2026-08-05) segfaults when driving native-build on a
  minimal out-of-tree entry file outside `bootstrap_main.spl`'s closure,
  consistent with the documented note that "the stage2 binary may lack
  features needed for pure in-process self-hosting" for non-bootstrap
  entries. Bare-positional dispatch to the in-process driver itself was
  confirmed working (a deliberately broken import produced the expected
  `unresolved import` error from the pure-Simple driver, not a seed
  delegation).
- This edit session hit repeated contested-working-copy reversion (another
  concurrent lane resetting these exact files mid-edit); the landed diff was
  built via git plumbing directly from `origin/main` blobs rather than the
  live working tree to avoid landing a partially-reverted patch.

## Residual / follow-up

1. Run the A/B/C/D measurement (cold, no-op rerun, one-file touch, sabotaged
   cache entry) as part of a normal scheduled bootstrap pass now that the
   cache dirs persist, using `SIMPLE_COMPILER_PHASE_PROFILE=1` to attribute
   wall time. Expect: A slow, B fast (cache hit), C slow (Layer 2, expected),
   D — construct by editing a cached `.o` file's bytes in place without
   changing its path or `build_cache.sdn` entry; current code only checks
   `rt_file_exists`, not content integrity, on hit (line 337) — verify this
   is/isn't an actual exploitable staleness gap in practice (it isn't for the
   normal case only because Layer 2's scope directory changes on any content
   change; it *would* be a gap if Layer 2 is ever narrowed without adding a
   per-object content check).
2. If/when the AOP/loader ABI stabilizes per bootstrap.md, revisit Layer 2 to
   scope cache entries per-module (or per strongly-connected dependency set)
   instead of by the whole closure, matching the Rust seed's
   `SIMPLE_NATIVE_INCREMENTAL` per-module reuse.
3. Consider adding a content check (not just existence) on cache-object reuse
   at `driver_aot_native_output.spl:337` as defense-in-depth before narrowing
   Layer 2, independent of the AOP work.
