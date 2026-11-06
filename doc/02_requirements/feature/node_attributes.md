# Node attributes: selected requirements

Date: 2026-11-06. Status: selected full scope; implementation pending.

Selection basis: the user requested "full", "structural change to land first",
"applyit to simple", and "land arch/design change to land first to share".
This records that selection; no unchosen scope option is retained.
The [source plan](../../03_plan/compiler/data/data_attributes_layout_containers_xray_2026-11-06.md)
supplies the detailed invariants. This feature implements its node-attribute path
and connects existing data-policy owners; it does not claim all future container
algorithms or platform XRay providers are prerequisites or already available.

| ID | Required result | Source-plan acceptance inventory |
|---|---|---|
| REQ-001 | One canonical schema resolver merges equivalent SPL/SDN declarations, resolves exact nominal types and qualifiers, retains both provenances, and rejects unauthorized/conflicting introductions. | ATTR-01–06 |
| REQ-002 | Ordinary field syntax lowers to typed managed places, preserving visibility, effects, receiver/RHS/index order, nested writes, move/borrow/atomic semantics and exactly-once evaluation. Non-opted-in classes retain their semantics. | ATTR-13–18, AOP-07–09 |
| REQ-003 | Whole-node `NotInit<T>` requires finish or explicit discard. Missing/repeated initialization fails; defaults execute at most once; failed finish retains a sound obligation or explicitly rolls back. Optional absence and deferred analysis results stay distinct. | ATTR-07–15, ATTR-24, ATTR-27 |
| REQ-004 | Qualified node handles check schema, pool, region/store/node incarnation and authority. Removal/reset invalidates stale references without generation wrap. Typed views require no public tag and no implementation inheritance. | ATTR-19–21 |
| REQ-005 | Ordered-tree, DAG and explicit graph policies preserve edge order, parent/cycle rules and construction-group atomicity. Pending references cannot be dereferenced or escape as ready values. | ATTR-22–24 |
| REQ-006 | Direct/column/sparse implementations preserve the same typed property and presence semantics. Existing layout/collection owners select only admitted representations. No missing-field numeric-zero fallback. | ATTR-25–27, LAY-01–09, COL-07–09 |
| REQ-007 | Compiler and both interpreter contracts agree. Generated operations preserve origin and survive lowering; the active exported evaluator and duplicate access paths are covered. Rust remains bootstrap/reference scope, not the default runtime. | ATTR-16–18, LAY-07–09 |
| REQ-008 | Canonical `get`/`set` selectors work across declarations and engines. Initialization, failure, removal and migration are separate events; helper/backing-store advice is not double-counted. Annotation `attr(...)` keeps its distinct meaning. | AOP-01–09 |
| REQ-009 | Optional bounded observation uses the shared trace/capture/profile ownership. Unsupported XRay combinations fail explicitly; counters, native XRay and physical conversion evidence are not conflated. | XR-01–12 |
| REQ-010 | Resolve policy per compilation/run, freeze it before workers, preserve schema/physical/instrumentation/profile identities, and invalidate the correct cache/TLDR/reverse-reference artifacts. | RUN-01–03, CACHE-01–09 |
| REQ-011 | Apply managed attributes to real Simple AST construction/access/traversal, then relevant HIR analysis and BuildRunner task views. Owner-only task transitions and pointer-free transfer remain mandatory. | RUN-01–06, ATTR-19–27 |
| REQ-012 | Provide an explicit build-time off mode. Disabled ordinary programs keep baseline behavior without managed-schema generation or observation dependencies. Explicit managed declarations in off mode receive a diagnostic, never a silent legacy interpretation. | Additional NA-OFF-01–04 |
| REQ-013 | Land architecture/design first; land shared structural contracts before consumer rewrites; expand through qualified vertical slices without declaring a pilot to be full completion. | Delivery receipts and full matrix |
| REQ-014 | Expose one resolved explanation to compiler diagnostics and LSP: logical field, exact type, authority, declaration origin, generated target, selected physical policy and rejection reason. | Additional NA-TOOLS-01–03 |
| REQ-015 | Preserve lifetime/lease/move invariants across every admitted representation change. Default to next-build/instance/snapshot; reject unqualified shared migration and never migrate in observers. | MIG-01–09 |

Full completion requires executable, source-matched evidence for every applicable
row. Unsupported optional providers/representations must demonstrate the refusal
path; that does not excuse missing ordinary managed field access or Simple adoption.

See [NFRs](../nfr/node_attributes.md), [architecture](../../04_architecture/compiler/node_attributes.md),
[detail design](../../05_design/compiler/node_attributes.md), and
[test plan](../../03_plan/sys_test/node_attributes.md).
