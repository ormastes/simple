# Optional Try receiver declared-owner input workaround

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
