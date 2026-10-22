# Result unwrap rejects a declared Optional repository payload

Status: bounded source feature implemented; regression scenarios authored,
runtime **UNRUN**. Bug database registration awaits a qualified pure-Simple CLI.

## Current source witness

At base `23085fbde5b00c64024b059dc85bdaf673756e67`,
`mir_archive_try_production_repository_v1` declares
`Result<MonoArchiveFinalRepositoryV1?, text>` in
`src/compiler/80.driver/cache/hir_mir_archive_consumer_v1.spl`.
`driver_pipeline_lowering.spl` uses
`if val final_repository = production.unwrap()` before entering the archived
MIR route. The Result unwrap switch had no Optional arm.

This is an exact current-source missing route. The historical audit's group
116 had only a module-level diagnostic, so this witness does not prove that
all historical occurrences or any other receiver are resolved.

## ABI and selected scope

`ensure_option_handle` defines Optional as an enum-id-1 handle or bare nil
sentinel, never an untagged scalar payload. The pure provider's
`rt_enum_payload` returns the outer enum payload word verbatim.

REQ-ENUM-RESULT-OPTIONAL admits no-default unwrap/unwrap_err with Optional
inner i64, bool, f64, Text, or a currently declared Struct/Class/Enum owner.
It copies the existing word, remembers the exact Optional type and marks the
Optional/tagged provenance. Presence and inner decoding remain with the
existing Optional owner. No allocation, clone, traversal, reboxing, cache, or
runtime ABI change is introduced.

Any/inference/error, unknown or non-type nominal owners, nominal generic
arguments, nested containers and default-bearing Optional forms stay outside
this bounded route. Existing Result, Dict and scalar-default behavior remains.
Every mismatched Result tag still takes the existing panic-plus-Abort path.

The production change is confined to the Result method owner in
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`.
Initial MIR/runtime specs and the affected dictionary negative control were
authored before the production edit. Additional nominal-negative and native
mismatch controls were added during the same source preparation cycle.

## Evidence and remaining work

Five actual-MIR scenarios, four actual-value scenarios and two expected-failure
native fixtures are authored. The former dictionary spec's Optional<i64>
negative control is now Any; its stale truncated diagnostic expectations are
updated to the current exact formatter.

All scenarios, compiler/lib/MCP checks, docgen, native emission, runtime ABI,
formal and measured memory/performance qualification remain UNRUN.
Source-level call inspection is not execution evidence.
The existing runner and retry accounting are preserved.

Historical groups 108/111/117/120 remain unattributed; other landed PassScope,
collector, coherence and dictionary fixes were not reimplemented. Full robust
and enum completion remains open in
`doc/03_plan/sys_test/robust_any_enum_extension_2026-10-14.md`.
