# Lifecycle teardown calls an absent cache-manager method

Bug: BUG-PHASE1-LIFECYCLE-CACHE-OWNER-20261011

Source baseline: `a4ca8226e21f8df3374c3eea1109e6365c4d7d79`.
`SmfCacheManager` declares `smfcachemanager_force_clear(self)` as a free function;
it does not declare a `force_clear` method. `lifecycle_destroy` nevertheless used
the method form, failing during loader teardown. The module-loader owner already
uses the free function. This repair imports and calls that same canonical owner.
Its cache-release, reference-reset, and sweeper behavior is otherwise unchanged.

The new executable regression creates an orphaned SMF reference without a
registered module, proves that reference accounting is nonempty, destroys the
lifecycle, and checks both the tracked count and dictionary are empty.
It does not allocate a file-backed mapping and does not prove native unmapping.

## Bounded diagnostic evidence

Evidence: `build/phase1-lifecycle-cache-teardown-20261011/`.
The cached producer SHA256 is
`15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb`.
It is the unadmitted Rust bootstrap producer, not an admitted pure runtime.

1. `baseline-result.json`: exact failing lazy-services scenario projected from
   the current spec, 0/1, exit 1, 13.04 seconds, missing `force_clear` method.
2. `fixed-result.json`: same projection after the source fix, 0/1, exit 1,
   13.19 seconds, identical missing-method error. The cached imported closure
   continues selecting the stale body; this is not a successful current-owner
   verification and is not claimed as a fixed lazy-services result.
3. `owner-inline-result.json`: exact changed `lifecycle_destroy` body extracted
   from source and renamed `diagnostic_current_lifecycle_destroy`, with real
   imported lifecycle, mapper, sweeper and cache-manager dependencies. The new
   orphaned-reference regression calls that body: 1/1, exit 0, 12.35 seconds.
   This proves the projected body delegates to the existing helper successfully
   under the producer. It does not qualify normal imported dispatch.

The normal projection SHA256 is
`cf19d68d2e7a1e4dde3412666a9f130962d47c11abf263399f2b7711dbac88fa`;
the changed-owner projection SHA256 is
`e2d033634add2f92d1bf351ecf51f4b80ebc43619200742649ce600f0984408b`.
Three attempts exhausted the bounded scope; no passing criterion was replayed.
The producer class-alias defect recorded in PR3034 remains separate and unfixed.

## Admission

STATUS: WARN — production verification pending. No rebuild was started.
Admitted pure compiler/lib/MCP/LSP checks, MCP interpreter integration, core and
MCP native smoke, normal imported regression, and native resource teardown
remain unrun. Preserve the draft until those gates are available and pass.
Historical global queue admission and Phase 1 completion are not claimed.
