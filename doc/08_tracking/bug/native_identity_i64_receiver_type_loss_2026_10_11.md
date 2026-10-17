# Known i64 identity receivers lose MIR method provenance

Status: OPEN. Canonical bug ID: `native_identity_i64_receiver_type_loss_2026_10_11`. GitHub: https://github.com/ormastes/simple/issues/2983

Original failure: C35 real identity fixture emits three to_text placeholder warnings and times out; retained HIR has four known-i64 candidate bindings but no expression provenance. Exact warning-to-site mapping unproven.

Workaround commits:

- `89a0b39532981a7c15a234afedf966c5d20e0b25`; recovery parent `ea9224a83a64cd20e21d013cf1c2652f891999c4` (review only).

Current qualification: Typed-local source workaround reviewed; no claimed native correctness, lifetime or performance qualification. Memory before/after lane remains separate and not qualified.

Producer: `96d356291fb75d4d81ff72df901fe3328e9e4bbabd4f4e5317382766b7261c4c`. Source integration before annotations: `f7fdafdea3b251b4fa6f84b7203bd319cce8bc6c`.

Evidence: `/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/source-authority-memory-20261011/`.

Reproducing/prevention source: `test/fixture/transient_scope/native_capsule_mir_identity.spl`.

Background fix owner and removal condition: MIR optional/local integer receiver provenance owner. Remove four explicit aliases only after original-form native canonical identity, mutation rejection, lifetime and measured performance controls pass without placeholders.

These are temporary source workarounds, not underlying fixes. Keep the DB and GitHub bug open. Apply and qualify a permanent owner repair and original-form tests before a separate narrow retirement commit. Root fixes for tracker APIs (#2998), missing imports (#3008/#3009), and the #3012 source group are not relabeled as workarounds here.

Provenance mapping and landing status: Workaround provenance: 89a0b39532981a7c15a234afedf966c5d20e0b25 -> 2fd7b71911b86e5048c06e3685d2b23d0b2d17b7 (stable patch-id equal; both UNLANDED on checked release). Release checked 95c12f073ffefa99ac774264beeedd68a47e7676. Add actual reachable landed commit/PR link after source landing; original branch SHA is not a release claim.

Exact qualified/failing source attribution: Original C35 failing fixture source 0163d55daeae2e6e1cd65884c4d91299115d3281. Workaround integrated as 2fd7b71911b86e5048c06e3685d2b23d0b2d17b7; no qualified memory/lifetime/performance source claimed.

Traceability annotation base: `64b8854eaa6eee9470470ddbcef5fa2165902d13`. No earlier source or retained build evidence was modified; native qualifications remain bound to their exact sources above.
