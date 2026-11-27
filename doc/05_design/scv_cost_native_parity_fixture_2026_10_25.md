# Native diagnostic parity fixture (small native run passed)

The retained plan below was implemented by
`test/fixtures/bootstrap/scv_cost_native/main.spl` and executed once after an
approved missing-platform-header harness repair. All four native rows passed;
actual summary and qualification limits are in
`C:/dev/simple-scv-native-parity-diagnostic2-storage-20261025/evidence/summary.sdn`
and `scv_cost_instrumentation_2026_10_25.md`. Static ABI review alone was not used
as native evidence. No production merge or full-fixture performance probe was
performed. Full negative-oracle integration remains pending, and the two-second
commit-base snapshot goal remains unmet. The steps below describe that bounded
fixture contract; they do not request another run of already-green checks.

## Build and ownership

After root review, build one tiny native diagnostic executable from the frozen
instrumentation source, using 24 workers and the canonical bounded Windows
JobObject owner, 5,859,375 KiB cap and 600-second build deadline. A pinned
immutable Rust seed may compile this bootstrap diagnostic; record its actual
path/hash and label it bootstrap-only, never ordinary self-hosted verification.
The fixture source imports the real scratch, snapshot and trace owners; it must
not replace them with local copies or mock transient/clock implementations.
Keep source, writable SCV, user/home/tmp, cache and outputs private to this
fixture. Record source patch hashes, seed and matching runtime hashes, full argv,
native DWORD, peak RSS, quiescence and cleanup. Build once; no green reruns.

## Small real-source scenarios

Prepare two clean tiny Git repositories at the same committed content: a real
entry source and two small valid source files (ASCII and UTF-8). Include one
committed delete in the current event stream. Keep their private cache roots
outside source discovery. Each scenario is a separate native process with a
60-second deadline and its own stdout/stderr receipt.

1. Allocate one carrier before the real file-event helper enters its transient
   scope. Call `compiler_inventory_file_event_cost_v1` successively for both
   physical files, retaining the first returned event across the second call.
   After both scopes end, compare event identities, byte counts and all facet
   digests to untimed old-arity events. Require two successful read/event
   counts, exact UTF-8 byte total, nonnegative durations, and nonzero aggregate
   hash-call count. Reduce retained events into a real inventory and compare
   encoded bytes with untimed reduction. This exercises allocation, promotion,
   scope teardown and later reuse of the actual carrier and first event.
2. Run the real source-authority admission route once on each twin repository:
   tracing disabled on one and enabled with a valid attempt token on the other.
   Capture real process stderr externally. Require identical inventory encoding
   and digest, snapshot source membership/content identities, validity/reason
   and emitted program bytes if the tiny entry is compiled. Compare semantic
   receipt fields, excluding root-bound paths, timestamps and diagnostics;
   root-specific snapshot IDs need not be equal. No final program is needed to
   establish this source-admission contract.
3. Capture owner-level calls to `inventory_trace_cost_emit_v1` in one bounded
   process. The lock-held call must emit nothing and leave `emitted=false`.
   After unlock, two calls with the same carrier must produce exactly one
   `phase=cost` line and set `emitted=true`. Invalid-token and nil-carrier calls
   must emit none. Require no per-file diagnostic lines and unchanged historical
   trace records. Also require exactly one aggregate in scenario 2 enabled and
   zero in disabled. Counters must remain readable after emission.

External assertions must inspect captured bytes, not merely the carrier flag.
Fail on a crash, timeout, missing receipt, wrong cardinality, mismatched source
authority, changed native arity/layout, residual child process or cleanup error.
Preserve the first failure and classify its actual boundary; no automatic retry.
Negative clock endpoints are source-reviewed to contribute zero; no clock
injection seam or duplicated pure elapsed helper is added solely for this test.

## Admission limits

PASS qualifies native diagnostic lifetime, trace cardinality and small-fixture
enabled/disabled parity only. It does not measure realistic SCV speed or prove
all unreadable/race/physical-alias/tamper negative oracles; those existing checks
remain required before production integration. The later reviewed producer
integration must carry this patch and retain its own normal qualification gates.
