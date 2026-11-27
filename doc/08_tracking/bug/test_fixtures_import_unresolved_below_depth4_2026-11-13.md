# `use test.fixtures.*` unresolved from specs deeper than `test/<a>/<b>/<c>/` (2026-11-13)

Status: open. Workaround in place.

## Symptom
A spec at `test/01_unit/lib/nogc_sync_mut/trace/zz_probe_spec.spl` containing
`use test.fixtures.xray.xray_backend_harness_v1.*` (or the long-standing
`use test.fixtures.scv.semantic_validation_bridge_v1_fixture.*`) fails to load:
`cannot resolve import ... module path segment `test` not found` (HIR lowering,
SIMPLE_JIT_STRICT), `executed=0`.
The SAME spec text at `test/01_unit/compiler/cache/zz_probe_spec.spl` passes.
Runner: Rust seed `src/compiler_rust/target/bootstrap/simple test <spec>`.

## Isolation
Only the spec's directory depth differs (5 vs 4 components under `test/`), so
the `test.` import root is derived from a fixed number of parent hops rather
than from the workspace root marker.

## Workaround
The XRay differential IN spec lives at `test/01_unit/lib/xray/` (depth 4)
instead of mirroring `src/lib/nogc_sync_mut/trace/`.

## Fix path
Resolve `test.` (and `app.`/`compiler.`) against the detected workspace root in
the module resolver, then move the spec next to its siblings.
