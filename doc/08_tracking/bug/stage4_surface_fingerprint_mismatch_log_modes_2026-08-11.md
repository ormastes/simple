# Stage4 full-CLI native-build fails deterministically: module surface/source fingerprint mismatch (log_modes.spl)

- **Date:** 2026-08-11
- **Severity:** high (blocks rebuilding the self-hosted full CLI on macOS arm64; combined with the bootstrap-only deployed binary, no `run`/`test`-capable pure-Simple CLI can be produced)
- **Area:** scripts/bootstrap/bootstrap-from-scratch.sh stage 4; src/compiler/80.driver/driver_hir_pipeline_lowering.spl (`module_surface_source_matches`)

## Repro
```
scripts/bootstrap/bootstrap-from-scratch.sh --mode=dynload --full-cli --no-mcp \
  [--fresh-cache] --output=build/gui-lane-bootstrap --jobs=3
```
Stage 2 and Stage 3 build and pass sanity + provenance (on a quiet tree).
Stage 4 (`main.spl` full CLI) fails identically on every attempt, fresh cache
or not:

```
[BOOTSTRAP-PHASE] +164783ms phase3:hir:file:done src/lib/nogc_async_mut/cli/log_modes.spl funcs=-1 heap_registry=7532717
[ERROR] phase 3 FAILED
error: focused native-build: Module surface/source fingerprint mismatch for src/lib/nogc_async_mut/cli/log_modes.spl
```

The file is untouched (mtime Aug 1) — not mid-build source churn. The check
(`module_surface_source_matches`, src/compiler/20.hir/hir_lowering/
module_surface.spl:305) compares source_index, canonical path, module name,
content length and `rt_hash_text(content)` between the phase-2 surface and the
phase-3 source. One of those diverges for this module — candidates:
`rt_hash_text` instability across phases, module-name aliasing between the
`std.cli.log_modes` shim path and `lib.nogc_async_mut.cli.log_modes`, or a
source-list ordering shift (`surface.source_index == index`).

## Secondary observation
phase3 HIR spent **164.8s on this single file** with thousands of
`[hir-lower] lower_expr:kind` debug lines and `heap_registry=7.5M` — a
compile-time perf pathology worth its own look once the mismatch is fixed
(cf. hir_lowering_quadratic_symbol_define_2026-07-28).

## Consequence
On this machine the last full CLI was overwritten by a bootstrap_main build
(see deployed_macos_cli_bootstrap_only_run_lost_2026-08-11.md), so every
`run`/`test`/`check`-dependent gate (GUI parity evidence, MCP smoke, …) is
blocked or forced onto the rust seed, which the honesty guards refuse.

## Fix direction
1. Dump both fingerprints (surface vs source) for the failing module in the
   error message — currently the mismatching field is invisible.
2. Check whether `rt_hash_text` is stable within a process run for identical
   content; if not, phase-2 must carry the source bytes forward instead.
3. Verify `index_by_name` aliasing for shim re-export modules
   (`std.cli.log_modes` → `nogc_async_mut.cli.log_modes`) does not shift
   `source_index` between phases.
