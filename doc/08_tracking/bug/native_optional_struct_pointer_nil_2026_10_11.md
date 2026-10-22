# Optional struct binding emits invalid pointer nil constant

Status: OPEN. Canonical bug ID: `native_optional_struct_pointer_nil_2026_10_11`. GitHub: https://github.com/ormastes/simple/issues/3016

Original failure: C36 tracker HIR11/MIR11 PASS; LLVM rejects add ptr3 in optional BuildMetadata if-val absent branch; retained LLVM points to tracker.spl:138.

Workaround commits:

- `dbe243b1075b1d130eca7ca377ff795e19da9159`; recovery parent `aeb2517fac0a3f287aed4347d75235ac8976161d` (review only).

Current qualification: Changed actual tracker ARM object PASS; snapshot behavioral fixture execution remains pending. Tracker API repair41096 is a separate root fix, not this workaround.

Producer: `5315b60ff617fd4595390609e89bcd8530204c4595fc7b2f28b32e5b7a40f235`. Source integration before annotations: `f7fdafdea3b251b4fa6f84b7203bd319cce8bc6c`.

Evidence: `/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/manual-affected-source-objects-c36-consumer-fixes/mono-tracker/`.

Reproducing/prevention source: `test/fixtures/compiler/tracker_finalize_snapshot/main.spl`.

Background fix owner and removal condition: MIR ExistsCheck nil-materialization and LLVM constant-type owners. Restore if-val only after pointer-optional absent/present cases generate valid LLVM and independent snapshot fixture executes.

These are temporary source workarounds, not underlying fixes. Keep the DB and GitHub bug open. Apply and qualify a permanent owner repair and original-form tests before a separate narrow retirement commit. Root fixes for tracker APIs (#2998), missing imports (#3008/#3009), and the #3012 source group are not relabeled as workarounds here.

Provenance mapping and landing status: Workaround provenance: dbe243b1075b1d130eca7ca377ff795e19da9159 -> f81ddc644cb9a49b84fe40fd6fdc1b287b830652 (stable patch-id equal; both UNLANDED on checked release). Release checked 95c12f073ffefa99ac774264beeedd68a47e7676. Add actual reachable landed commit/PR link after source landing; original branch SHA is not a release claim.

Exact qualified/failing source attribution: Affected tracker ARM object source f7fdafdea3b251b4fa6f84b7203bd319cce8bc6c includes f81ddc644cb9a49b84fe40fd6fdc1b287b830652; snapshot behavioral fixture pending.

Traceability annotation base: `64b8854eaa6eee9470470ddbcef5fa2165902d13`. No earlier source or retained build evidence was modified; native qualifications remain bound to their exact sources above.
