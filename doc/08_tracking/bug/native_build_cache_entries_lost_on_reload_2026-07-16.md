# Bug: native-build BuildCache loses all entries on cross-process reload

**Status (2026-07-16):** Open. Found while regression-testing
`native_build_cache_omits_compiler_identity_2026-07-13.md`.

- **Severity:** P2 (perf, silent: the incremental native object cache NEVER
  hits across processes in the live-interpreted pipeline — every native-build
  recompiles every module; correctness is unaffected because misses only
  over-compile)
- **Area:** `src/compiler/80.driver/driver_build/incremental.spl`
  (`BuildCache.load`), `src/compiler/80.driver/driver/incremental.spl`
  (duplicate `BuildCache`), `std.common.sdn` parser.

## Symptom

`build/native_cache/build_cache.sdn` is written correctly (verified on disk:
`version: 9`, one entry with fingerprint + outputs), but the next
`native-build` run reports a miss for the identical source and compiler.
Instrumented `has_cached_object` shows `entries.len() == 0` after
`BuildCache.load`.

## Root causes (both proven by print-instrumentation, deployed seed
interpreter of 2026-07-11 interpreting the pipeline live at 6456be19e64)

1. **Duplicate-class dispatch collision:** `BuildCache` is defined in BOTH
   `driver/incremental.spl` and `driver_build/incremental.spl`.
   `driver_aot_output.spl` imports the `driver_build` one, but its
   `BuildCache.load(cache_path)` call executes the `driver/incremental.spl`
   implementation (print added to each version: only the `driver/` one fires),
   while instance methods (`get_cached_outputs`/`has_cached_object`) run the
   `driver_build` code. Known interpreter landmine: same type name in two
   modules collides in the global registry.
2. **SDN round-trip loss:** inside the (wrongly dispatched) load,
   `sdn_value.get("entries")` returns `SdnValue::Array([])` even though the
   file's `entries:` array contains one inline-brace object, and
   `as_array()` on it then yields `nil`. The persisted format
   `entries: [\n  { source: "...", fingerprint: { ... }, ... }\n]` does not
   survive parse under the interpreted `std.common.sdn` parser.

## Impact

- The compiler-identity cache-scope fix is correctness-complete (a changed
  compiler can never reuse another scope's objects), but its perf benefit
  ("same compiler retains hits") is dead until reload works.
- SimpleOS full-module builds keep paying the all-modules recompile cost that
  the identity bug report measured (345-634 s).

## Suggested fix

Deduplicate `BuildCache` (make `driver/incremental.spl` re-export the
`driver_build` implementation or rename one class), then fix or bypass the
SDN entry parse (e.g. one entry per line with a flat key=value encoding).
Regression gate: build twice with the same compiler binary and require
`[NATIVE] cache: 1 hits, 0 misses` on the second run.
