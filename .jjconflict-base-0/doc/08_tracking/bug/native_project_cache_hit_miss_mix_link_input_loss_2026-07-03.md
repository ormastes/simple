---
id: native_project_cache_hit_miss_mix_link_input_loss_2026-07-03
status: NOT REPRODUCED
severity: unknown (reported as a latent correctness bug; could not confirm empirically)
discovered: 2026-07-03
discovered_by: seed task #64 (driver_aot_output cache hit/miss mix investigation)
related: src/compiler_rust/compiler/src/pipeline/native_project/mod.rs
related: src/compiler_rust/compiler/src/pipeline/native_project/linker.rs
related: src/compiler_rust/compiler/src/pipeline/native_project/tests.rs
---

# native-project incremental build: suspected link-input loss on cache hit/miss mix (NOT REPRODUCED)

**Status:** Investigated 2026-07-03. Full manual audit of the build/cache/link
pipeline plus two independent repro attempts (both automated as permanent
regression tests) found no evidence of the reported bug. Filing per the task
instruction to document an honest non-repro rather than claim a fix for a bug
that could not be shown to exist.

## Reported symptom

"When a native-project build has a mix of object-cache hits and misses, some
link inputs are dropped from the final link set" -- specifically raised in
the context of `object_cache_key`'s compiler-fingerprint addition in commit
`0887128f88f33e10390311bff8201eae24154cc6` ("fix(bootstrap): mix compiler
fingerprint into native-build object cache key").

## Investigation

### Code audit (mod.rs `NativeProjectBuilder::build`)

Traced every file discovered by `discover_files()` through to the final
`link_objects()` call:

1. Each discovered file gets one `usize` index `i` (0..files.len()).
2. For `use_incremental` builds, each index in `compile_indices` is looked up
   in `objects_dir` via `object_cache_key(...)`. On hit, `(i, obj_path)` is
   pushed to `cached_objects`; on miss (or when `is_entry` /
   `source_may_emit_inline_asm_sidecar` forces recompilation), `(i, path,
   source)` is pushed to `to_compile`. Every index lands in **exactly one**
   of the two buckets -- no index is skipped or double-counted.
3. `to_compile` is compiled (parallel or sequential); results merge into
   `object_paths_with_indices = cached_objects ++ freshly_compiled`, then
   sorted by index and flattened to `object_paths`.
4. `object_paths` (the full set, hits and misses together) is passed
   unconditionally to `link_objects(&final_object_paths, &imports)` /
   `archive_objects`. Neither function filters by hit/miss origin --
   `link_objects` (linker.rs:772) appends every path in `object_paths` to the
   link command (or a response file above 100 objects), with no drop path.
5. `compiler_fingerprint()` is a `OnceLock`, computed once per process and
   reused for every `object_cache_key` call within that process -- it cannot
   itself cause an index to be skipped; it can only change which `.o` file a
   given source hashes to (forcing a miss when the compiler binary changed
   between two separate process invocations), which is the intended
   invalidation behavior from commit `0887128f`.

No point in this path drops an object path based on cache-hit/miss origin.

### Empirical repro attempts (both added as permanent tests, both PASS)

Both live in `src/compiler_rust/compiler/src/pipeline/native_project/tests.rs`:

1. `test_incremental_cache_hit_miss_mix_preserves_all_link_inputs` -- 2-module
   project (`module_a.spl`, `module_b.spl`), `emit_archive: true`,
   `incremental: true`, shared `cache_dir`. Build 1 (both miss), then touch
   only `module_b.spl`, build 2 (module_a cache HIT, module_b cache MISS).
   Asserts both `cache_mix_probe_a`/`cache_mix_probe_b` symbols are present
   in the linked archive after build 2 via `nm -g --defined-only`.
2. `test_incremental_cache_hit_miss_mix_parallel_wide_matrix` -- 6-module
   project, `parallel: true` (exercises the rayon `compile_entries_parallel`
   path, not just the trivial single/dual-file case), alternating
   touched/untouched modules between build 1 and build 2 (3 hits + 3 misses
   on build 2). Asserts an exact count of 6 defined probe symbols present
   after build 2.

Matrix attempted: sequential-ish 2-module (default `parallel: true` but small
enough rayon may run it near-sequentially) x wide 6-module explicit
`parallel: true`; `emit_archive` output path (avoids full C-runtime link
variables to isolate the object-set question). Both pass cleanly with no
missing symbols on the first run, no flakiness observed across reruns.

### Not yet attempted

- `emit_archive: false` (real executable link via `link_objects`, not
  `archive_objects`) end-to-end with a runtime bundle -- the archive path
  was chosen to isolate the "which objects make it into the output" question
  from unrelated runtime/link-flag concerns, but a full `--backend
  cranelift` executable-link repro was not run for this specific mix
  scenario (the VERIFY step's trivial `/tmp` project build is a
  non-incremental single-shot build and does not exercise a hit/miss mix).
- Deliberately changing `compiler_fingerprint()` mid-matrix (i.e. swapping
  the running binary between build 1 and build 2 to simulate a seed rebuild)
  was not attempted -- `OnceLock` makes this impossible to trigger within a
  single test process; it would require two separate process invocations
  with two different compiler binaries, which is a heavier repro to stand up
  than the time budget allowed.
- Cross-invocation via the actual `native-build` CLI subcommand (spawning
  the built binary twice as a subprocess, rather than calling
  `NativeProjectBuilder` in-process) was not attempted; the in-process API
  is what `tests.rs` already uses throughout and should observably behave
  identically, but subprocess-level effects (e.g. tempdir cleanup timing,
  environment differences) are not fully ruled out.

## Conclusion

No drop of link inputs across a cache hit/miss mix was found by code audit or
by two independent empirical repros (small and wide, sequential-leaning and
explicitly parallel). If this bug is still observed in practice, the next
useful repro would be one of the two "not yet attempted" variants above,
particularly the real cross-process CLI invocation with a genuinely swapped
compiler binary between builds.
