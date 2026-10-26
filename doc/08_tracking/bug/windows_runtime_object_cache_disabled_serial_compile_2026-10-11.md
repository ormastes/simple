# Windows runtime object cache disabled and serial native compilation

Status: OPEN, source evidence confirmed; runtime timing and bug DB reconciliation pending.
Owner: src/compiler/70.backend/backend/runtime_compiler.spl.
Related: windows_core_c_value_accessors_missing_2026-09-29.md already notes the
cache-disabled behavior; this report tracks the separate performance issue.

## Actual source evidence

_runtime_object_cache_dir returns an empty string unconditionally on Windows,
regardless of SIMPLE_RT_OBJ_CACHE. compile_runtime_objects therefore constructs
an empty cache_obj, cannot hit the runtime-object cache, and invokes process_run
inside the selected-source loop. The core-c-bootstrap plan currently selects
37 base C translation units; include_dynload=true adds runtime_dynload for38.
This path is serial within one compiler request; higher
HIR workers do not parallelize these process_run invocations. This is evidence
of the source behavior, not a measured count for every native-link route.

The non-Windows key/publication path uses shell find/sort/sha256sum, ln, cp and
mv. Removing the Windows early return alone would not provide a native Windows
cache implementation or trustworthy cache admission. Artifact presence alone
must never admit reuse. Existing source changes or runtime archive routes may
avoid this owner; trace actual invocations before making whole-build claims.

## Required fix and acceptance evidence

Use the actual selected runtime composition and authenticated immutable source,
header, compiler/SDK, target/ABI, optimization and provider-policy identities.
Use native Windows filesystem/publication owners, exclusive staging, and
validated complete receipts; do not infer compatibility from mtime or size.
Propagate generation-bound capture authority to this owner before replacing
conservative source hashing. Unsupported capture must retain fail-closed
behavior or uncached correct compilation, with an explicit disposition.

1. Cold build records actual selected compiler invocations and positive-sized
objects, links a runnable program, and publishes only after complete success.
2. An unchanged warm build uses exactly those objects with zero C compiler
invocations; output behavior, object identities and link provenance match.
3. Source, nested header, compiler/SDK, target, ABI, flags and provider-policy
changes independently invalidate the affected authority; stale cache cannot hit.
4. Concurrent identical requests have one producer per key and authenticated
waiter results; crash/partial publication cannot become a hit. Ordinary syntax
failure remains distinct from infrastructure failure and does not poison other keys.
5. Measure cold/warm elapsed time and peak RSS for baseline and candidate on
the same fixtures; preserve ownership cleanup and compare the joint metrics.
6. Cache-hit validation avoids full-tree scans and process shell-outs. Maintain
bounded result/diagnostic retention and default standalone compilation support.

Do not replay exhausted bootstrap/loader cohorts to prove this fix. Qualification
requires an independently reviewed request against real producer/current owners.
No source workaround, guard bypass, benchmark or production application is made
by this report. Phase3/4, six test binaries and the 0.1-second target remain open.