# Phase 3 HIR import materialization time and RSS

## Status

Open bootstrap blocker. Pure-Simple Stage 3 remains both incorrect and too
expensive while lowering the 664-module CLI closure.

## Evidence

- Diagnostic build: HIR module 5 at `+240864 ms`, `776960 KiB` RSS.
- Trace-free final build: HIR module 6 at `+326955 ms`, `777240 KiB` RSS.
- The final build still recorded five unresolved `Span` errors before module 6.
- Stage 4 and deployment were not reached; no seed fallback was accepted.

Canonical owner imports and scalar, Dict-free route/origin validation remove
failed terminal searches for `Type`, `ProcessResult`, `OptimizationLevel`, and
several `Span` owners. They do not solve the remaining owner-qualified binding
loss, and did not materially reduce peak RSS.

## Required next investigation

Instrument the post-bind `lookup_qualified_type_raw(owner, "Span")` receipt and
the immediately following `imported_surface_projected_name_type` lookup in one
fresh scoped session. Once correctness is restored, profile allocations caused
by rebuilding the complete imported `CompilerDriver` method/type closure for
every driver extension module. Preserve module-local symbol identity while
caching only immutable terminal-route indexes; do not retain prior-module HIR
graphs or replace the Pure-Simple path with Rust/C.
