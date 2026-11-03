# Optional Try receiver declared-owner input workaround

## 2026-11-03 permanent owner-propagation source candidate

Status: **fix implemented, verification pending**. No admitted self-hosted
runtime is available in this recovery session; authored regressions are
**TEST_BLOCKED**, not PASS. The library annotation and its workaround tag remain
until the original unannotated native case passes.

Current source still had the actual root gap: `lower_try_expr` decoded Optional
payload bits but returned a nominal payload without its HIR declaration or
`struct_value_syms` owner. The already shipped Result `?` decoder restores both.
The candidate reuses that decoder for Optional Named payloads after the existing
physical decode. It adds no table copy, boxing, or getter reevaluation and does
not alter the Optional None branch. The base expression is lowered once; if its
Optional return becomes known only during imported-method lowering, that
remembered declaration is used as the fallback. Existing static Optional types
retain precedence.

Regressions authored in this candidate:

- `test/01_unit/compiler/mir/optional_try_nominal_owner_spec.spl` drives the real
  MIR Try lowering and checks retained class/struct declaration and owner.
- `test/fixtures/compiler/database_optional_receiver_unannotated_probe.spl`
  restores the original C2 unannotated real SdnDatabase/SdnTable receiver, with
  update/delete, missing table/key, class aliases and save/reload values/flags.
  Its temp parent uses the environment facade for Windows TEMP/TMP.
- `test/fixtures/compiler/native_optional_try_owner/main.spl` calls an effectful
  imported getter exactly once for Some and once for None, preserves an alias,
  and prevents a local same-name class from replacing the provider owner.

Required qualification: use a genuinely rebuilt pure-Simple producer containing
this compiler repair, private caches and outputs, and the actual linked runtime.
Run the MIR spec with the full self-hosted test CLI, then compile and execute
both native fixtures with LLVM and Cranelift. The database fixture must exit 0;
the imported fixture must exit 0 and print `OPTIONAL_TRY_OWNER_PASS`. The original
`src/lib/nogc_async_mut/database/bug.spl` input additionally requires the separate
native array.take/query-prefix prerequisite below. Preserve producer/source,
backend/provider and cache identities and actual object/executable/exit/output
receipts. An old producer, structural checks, or authored scenarios cannot
qualify this source candidate. The historical pinned producer below remains
failure/workaround evidence, not a repaired compiler.

Claims/provider usage: session `codex-optional-try-owner-20261103`; token usage,
comparable cohort average and ratio are unavailable, not zero. This recovery
does not resolve the bug, remove the library workaround, or claim native parity.

## Historical workaround evidence

Source-only companion for checkpoint74 database groupD. Runtime/compiler/native
qualification **UNRUN**. This does not report producer645 or the failed source
compiled successfully. No compiler operator or runtime carrier is changed.

The exact original `update_bug` binding now names its already imported
`SdnTable` owner. The getter remains the same once-evaluated `get_table_mut`
call followed by `?`; `update_row`, `mark_deleted`, and every existing
`set_table` writeback remain byte-identical. `SdnTable` is a class, not a new
raw typedef or an `Any` escape.

Pinned source path: `mir_lowering_stmts.spl` 1047-1061 chooses the declared
slot but `lower_expr_for_slot` 2349-2406 treats a Named class as ordinary
`lower_expr`, not scalar unboxing or optional boxing. The early Let metadata
path 1414-1465 copies an existing owner, otherwise remembers the explicit
declared type. The existing Try Optional arm ends at5194 with raw/decoded
payload, with no nominal HIR type registration. `enum_payload_value` 677-716
returns its Struct payload unchanged. Named table bindings are recovered by
`declared_record_receiver_owner` 1914-1928. `maybe_copy_struct_value`580-618
skips class references and this Try initializer is not a place read. No
annotation step adds a table copy, reevaluates the getter, changes class
aliasing, or removes explicit database writeback.

These are static source facts at commit8973828. The failed producer645 launch
pins a binary hash and input source; that alone does not prove its exact
source lineage or execution of this metadata path. The typed native fixture
uses the real core owners, updates/deletes, tests missing table/key, observes
class aliases before helper writeback, and saves/reloads exact values and
deleted flags. The unannotated C2 fixture remains required for the permanent
compiler repair; this companion cannot replace that acceptance test.

Operator qualification, not run here: use pinned producer
645e62a815d076d77a61b01daa6e86c1330632686c18ce4c56cccd860a4a714a, fresh
owned caches and output. Compile/execute the typed core-only fixture and
compile the actual changed database/bug.spl input. For the latter the reviewed
query-prefix patch is a separate prerequisite because native array.take
remains unsupported. No compiler Try edit may be assumed present in this old
producer. Record exact producer/input/dependency hashes, real diagnostics,
object/executable artifact and execution statuses; unrelated failures keep
this workaround UNQUALIFIED.

Remove the input annotation and this bug tag after a genuinely rebuilt
producer with the permanent Try type-recovery fix passes the unannotated
actual-owner fixture and actual database source, including mutation/aliasing
and persistence. Keep the regression. Native array.take parity is separately
OPEN under native_array_take_method_missing_2026_10_21; this annotation does
not implement it or change its removal conditions.

## Canonical database reconciliation — 2026-11-03

FIX IMPLEMENTED, VERIFICATION PENDING; source repair PR #6304 MERGED at efbd310e067829ba67386a5f246c400b08b744a8. Optional Try nominal-owner propagation received source safety review, but MIR regression, effectful single-evaluation/alias probes, both native backends, original unannotated database input and required core/MCP smokes are UNRUN. TEST_BLOCKED: qualified self-hosted runtime unavailable. Keep the historical library annotation until producer-qualified verification; no closure or Phase2/Phase3 qualification. Main status fix-implemented-verification-pending records the merged implementation, not a runtime PASS. Source owner session codex-optional-try-owner-20261103; original claim start is unknown in the current remote ledger.
