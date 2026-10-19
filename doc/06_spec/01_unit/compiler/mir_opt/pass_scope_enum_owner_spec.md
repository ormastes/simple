# PassScope ownership and dispatch boundaries

Authored manual for
`test/01_unit/compiler/mir_opt/pass_scope_enum_owner_spec.spl`.
Requirement: REQ-ENUM-PASS-SCOPE. Runtime and generated documentation: UNRUN.

| Scenario | Real operation | Required observation |
|---|---|---|
| Registry ownership | Lookup DCE, write-coalesce, AutoVectorize, and vectorization | Function/FsDriver/Module owners; alias resolves to canonical AutoVectorize kind and name |
| Module request through function API | Run active vectorization on a valid leaf function | Skipped with `module_scope`, zero functions/transforms, unchanged MIR |
| Module dispatch | Run vectorization on a valid one-function module without loops | Valid module, same function count and serialized leaf |
| Inactive scopes | Run DCE and write-coalesce through both APIs | Skeleton/AnalysisOnly retained, explicit skip reasons, zero candidates/transforms, unchanged MIR |
| Unknown pass | Run a missing name through both APIs | Function result records Failed/`unknown_pass`; checked module remains unchanged |
| Malformed input | Run active, inactive, and missing names on a function without its entry block | Both APIs reject; module diagnostic contains MIRV011 |

The fixtures construct actual MIR; the assertions inspect production records,
structural receipts, and serialized functions. No source-text matching or fake
descriptor activation substitutes for dispatch.

No active Function/FsDriver pass currently exists in the registry. Their scope
branch execution remains unqualified. This no-loop module scenario also does
not prove a vectorization transformation. The tracking record
`doc/08_tracking/bug/pass_scope_enum_owner_projection_2026_10_19.md` names the
adjacent stale FsDriver transformation tests and the required follow-up.
