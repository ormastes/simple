# Phase 2 imported indexed history-field workaround

Status: WORKAROUND VERIFIED for the shared record view; compiler defect OPEN.
No Phase2 compiler was rebuilt or replaced.

The existing pure-Simple Phase2 producer
`1ad6ea53c67f3e01efc5c1b0ac8aa4dcef184a0987b4d3c806c59e14e96be584`
misreads non-first fields after indexing an imported McpT32HistoryItem array.
The original state fixture fails the last request-ID check. Three bounded,
changed-input diagnostic builds localized and contrasted the operation:

- Core counts, history length and first command pass; assertion5 fails.
- Explicitly typed indexed local returns command `cmd-499` for result and
  request_id too. Decimal formatting correctly returns499.
- A directly constructed imported record reads distinct fields correctly.
  A view function in the record's declaring owner reads the indexed record as
  `(cmd-499,value-499,session,core,request-499)` correctly.

`t32_history_fields` transfers those five fields as a typed tuple. The actual
production-owner native fixture compiled/linked and ran all11 original semantic
checks, exit0: core counts,500-entry threshold,251-entry suffix, order, result,
session/core identity and final request ID. Evidence:
`build/tooling-phase2/workaround-state/owner-view-run/`, owner-view.spl,
owner-view-runtime.log. Earlier failed binaries/logs remain in the same parent.
This is focused native evidence, not a canonical SSpec or complete server PASS.

The real shared history serializer uses the owner view and retains appended
JSON entries. Legacy main declares a different four-field history record; its
two serializers use a separate locally typed four-field view. Representations
and wire keys/order/escaping/count limits are preserved, not unified by unsafe
casts. The legacy integration is source-reviewed, not independently executed.
New/updated SSpec expectations preserve the exact field values and remain UNRUN
while the general native test runner is blocked.

Remove the workaround only after the original indexed-field form preserves
every distinct field under a qualified compiler and the actual history callers
pass. Do not change expected values to the corrupted first field or reinterpret
the record layout. No compiler rebuild is authorized by this record.

## Other fixes considered

Astra reviewed landed PRs5014,4997,5006. Typed Result call boundaries, field-name
forwarding precedence and fresh-array ownership changes are reasonable in their
respective scopes, but do not establish this old producer's field-read behavior.
They remain upstream; no duplicate cherry-picks or global compiler flags were
used. Compiler-source changes do not alter this immutable Phase2 executable.

## 2026-11-09 — Fix (fix-implemented-verification-pending)

Root cause (located in current source, defect already repaired there): the MIR
array-index decode arm in
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` decoded the indexed
element as an untyped word and never propagated the array's element struct
identity onto the decoded local, so a following `.field` read fell through
`resolve_field_index`'s `struct_value_syms` fallback and silently used field
index 0 for EVERY field name — exactly the observed symptom (command text
returned for result and request_id on `items[499]`). The same-owner view read
correctly because same-module arrays register
`array_element_struct_syms[base]` at construction; arrays bound from an
IMPORTED call result (`val items = make_hist(500)`) carry only their Array HIR
type, so the imported/indexed view lost the layout.

Fix present on release/1.0.0 source: the indexed element is decoded as
`Opaque(esn)` and stamped `struct_value_syms[decoded_elem.id] = esn` (block
comment "Bug (array-of-structs field misread)"), and when
`array_element_struct_syms` has no row the element owner is recovered from the
base's `HirTypeKind.Array/Slice` element type through
`optional_payload_struct_name` — fail-closed via the `struct_field_order`
layout gate (recovery block landed 3b94b409c17, 2026-11-01; qualified
layout-key folding for imported declarations landed fc6440368f0,
2026-11-05). No new compiler edit was required and no compiler rebuild was
performed; the pinned Phase2 producer executable remains immutable as this
record always required.

Evidence:
- Tier T0 hosted (Rust seed `bin/simple`, provenance
  release100-7a0e6fe516f-20261031; warning noted): from a clean worktree of
  origin/release/1.0.0 @4648b81b549, `simple run
  test/fixtures/compiler/phase2_native_repro/imported_history_fields.spl`
  prints `cmd=cmd-499 result=value-499 session=session core=core
  req=request-499` + `PASS imported indexed fields`, exit 0; an explicitly
  typed-let variant (`val typed: [HistItem] = make_hist(500)`) prints
  `cmd=cmd-499 result=value-499 req=request-499` + `PASS typed-let imported
  indexed fields`, exit 0.
- Native: stage2_new4 self-hosted run 2026-11-09 (section above), rc=0,
  all five distinct fields.
- Regression spec added:
  `test/01_unit/compiler/mir/imported_indexed_record_fields_spec.spl`
  (3 examples, real assertions, reuses the hist_rec fixture module). Hosted
  spec execution is currently blocked for EVERY spec on this tree: the
  deployed seed predates `str.byte_len` (added to the Rust seed 2026-11-06)
  which the current test runner uses — `simple test` fails identically on a
  pre-existing spec (`module_qualified_type_registry_spec.spl`) and on a
  minimal smoke spec. Spec run is pending an updated seed/self-hosted runner.

Honest limits: no bootstrap/rebuild run (not authorized here); native
verification used the separately built stage2_new4 producer, not a rebuilt
pinned producer; the mcp_t32 owner-view workaround (`t32_history_fields`)
retirement is a separate change.

## 2026-11-09 — resolved-disappeared (native)
Native re-run 2026-11-09 with the current self-hosted stage2 `C:/dev/p3new/stage2new/stage2_new4.exe` (`native-build --entry-closure`, llvm, x86_64-pc-windows-gnu, core-c-bootstrap, SIMPLE_HIR_CACHE=0, clean sparse worktree of origin/release/1.0.0 @1cc167e37fd): two-module reproducer `test/fixtures/compiler/phase2_native_repro/imported_history_fields.spl` (5-text-field record declared in an imported module, 500-entry array built there, `items[499]` indexed in the importer) reads every distinct field: `RESULT rc=0 stdout=[cmd=cmd-499 result=value-499 session=session core=core req=request-499|PASS imported indexed fields]`. The owner-view workaround (`t32_history_fields`) may now be retired in a separate change.
