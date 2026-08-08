# Stage 4 wildcard re-export surface loss

Status: fixed (2026-08-03)
Severity: P1 bootstrap blocker
Owner: pure-Simple parser and HIR import surfaces
Fix owner: `/root` — CLAIMED

## Reproduction

The no-stub x86 Stage 4 full-CLI build parsed 2,116 sources and lowered 235
modules, then failed in `compiler.backend.backend.sdn` with `unresolved type:
Effect`. The consumer never names `Effect`; it imports `compiler.hir.hir.*`.

`HirTypeKind.Function` carries `[Effect]`. The facade explicitly exports
`HirTypeKind` and intends to re-export `hir_types.*`, but the parser discarded
the wildcard re-export from `Module.exports`. Materializing the enum through
the incomplete facade therefore lost its payload dependency. Globally unique
missing names were masked by full-universe fallback; the second HIR/MIR
`Effect` made this one visible.

## Fix

`_export_record_reexport_surface` now records an empty-item wildcard import as
`<source-module>.*`. Existing HIR facade expansion already consumes that form,
so all owner declarations and enum payload dependencies are registered through
the canonical module surface. Named and aliased re-exports are unchanged.

The regression parses an owner enum with a structured payload, a facade that
uses `export use owner.*`, and a consumer that imports the facade. It asserts
the wildcard survives parser assembly and that HIR resolves both the enum and
its payload with no lowering errors.

## Performance evidence

The failing retry took 7m38s at 99% aggregate CPU and 3.22 GB peak RSS. Parsing
the 2,116-source closure consumed about 346s (75% of wall time); HIR was also
serial. The delay is frontend serialization plus replay after each masked
root-cause failure, not swapping or native linking.
