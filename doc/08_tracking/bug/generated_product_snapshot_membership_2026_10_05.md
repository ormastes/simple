# Generated subsystem tests must enter the compiler snapshot

The canonical product builder renders authored tests into its private source
overlay after building the native parser and main-verdict helpers. A parent's
inherited warm SCV bindings name a different frozen tree. They cannot authorize
the overlay's newly generated test bodies.

The builder now clears all eight inherited SCV bindings before each native
overlay build and lets the canonical compiler cold inventory/event path admit
the overlay. After the aggregate product compiles, it requires the actual
compiler-published snapshot to contain every generated manifest member with
matching SHA-256 and byte count. The generated entry and authored test-owner
modules must all be present. A CURRENT pointer alone is insufficient.

The additional checker validates the exact six-field SCV provenance, derived
tree/commit/revision identity and exact completed receipt format from
`scv_compile_snapshot_receipt_v1`. It writes a hash-bound generated-membership
proof. The canonical product verifier requires that proof and replays the check
read-only, comparing its bounded output with the saved proof. These checks
supplement compiler admission; they do not grant source authority themselves.

Nine focused checks passed: complete membership, absent receipt, changed
snapshot payload, changed rendered bytes, omitted generated test owner,
provenance-only incomplete receipt, read-only replay, and the real builder's
post-compile publication hook accepting/rejecting the corresponding fixtures.
The two hook tests explicitly mock compilation and prove only caller wiring.
They do not represent built product binaries or executed test assertions.

Native generator/verdict compilation currently fails before linking. Full
compiler/interpreter/loader products for both backends remain unqualified until
those helpers succeed, canonical ledgers are produced, binaries enumerate their
authentic registries, first-case smoke runs and full execution receipts complete.
Original failures and inventories remain unchanged; no test exclusions or
fabricated manifests are introduced by this change.
