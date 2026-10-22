# Native range indexing blocks deferred deserialization

Status: OPEN. Canonical bug ID: `native_deferred_range_index_2026_10_11`. GitHub: https://github.com/ormastes/simple/issues/3014

Original failure: C36 HIR7 PASS then unlocated MIR range-index failure; closure has one byte-array range and four text ranges. First thrown site remains unknown.

Workaround commits:

- `e7c59ad3010dc2f45f7ac13bfe55a839ee0fd07e`; recovery parent `aeb2517fac0a3f287aed4347d75235ac8976161d` (review only).

Current qualification: Changed C36 source HIR7/MIR7 PASS; both changed deferred modules have verified ARM objects among5/7 native units. Aggregate object still FAIL on lib.string_core/compiler.frontend.ast declaration-only dependencies. Native fixture execution pending.

Producer: `5315b60ff617fd4595390609e89bcd8530204c4595fc7b2f28b32e5b7a40f235`. Source integration before annotations: `f7fdafdea3b251b4fa6f84b7203bd319cce8bc6c`.

Evidence: `/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/manual-affected-source-objects-c36-consumer-fixes/deferred-deserialize/`.

Reproducing/prevention source: `test/fixtures/compiler/deferred_range_native/main.spl`.

Background fix owner and removal condition: Native Index/Range lowering owner. Retire byte-copy and four colon-slice workarounds only after original range forms preserve empty/negative/clamped/multibyte semantics through target objects and native fixture execution.

These are temporary source workarounds, not underlying fixes. Keep the DB and GitHub bug open. Apply and qualify a permanent owner repair and original-form tests before a separate narrow retirement commit. Root fixes for tracker APIs (#2998), missing imports (#3008/#3009), and the #3012 source group are not relabeled as workarounds here.

Provenance mapping and landing status: Workaround provenance: e7c59ad3010dc2f45f7ac13bfe55a839ee0fd07e -> 7c345672343dbb63345c2b5a5310f7d4167e3363 (stable patch-id equal; both UNLANDED on checked release). Release checked 95c12f073ffefa99ac774264beeedd68a47e7676. Add actual reachable landed commit/PR link after source landing; original branch SHA is not a release claim.

Exact qualified/failing source attribution: Changed-module ARM objects source f7fdafdea3b251b4fa6f84b7203bd319cce8bc6c includes 7c345672343dbb63345c2b5a5310f7d4167e3363; aggregate/fixture not passed.

Traceability annotation base: `64b8854eaa6eee9470470ddbcef5fa2165902d13`. No earlier source or retained build evidence was modified; native qualifications remain bound to their exact sources above.
