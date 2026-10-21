# Remaining recovery acceptance evidence — 2026-10-21

Scope: the 35 non-OWN/non-BOR rows in the [authoritative plan](nogc_ownership_recovery_plan_2026-10-19.md) §12.1. The nine core rows are tracked separately. This is a bounded evidence audit, not a source implementation census or an executed verification pass.

**Result: 0 of these 35 criteria established closed by the inspected evidence.** `UNVERIFIED` means no sufficient terminal, route-specific receipt was found; it does not assert that implementation is absent. `FAIL-OBSERVED` identifies an actual counterexample to the required gate behavior. Test presence, old bug closure labels, build success, capsule receipts and success prints do not establish acceptance.

## Inspected authority and receipts

A single focused acceptance-ID search of `doc/03_plan`, `doc/08_tracking` and `.simple` found the non-core IDs only in the recovery plan; no separate bound traceability receipt was found. Inspected the maintained hardening progress record, top-level relevant diagnostic logs, verification cycle ledger and `build/nogc-hardening/parallel-feature-evidence.json`. No tests/builds were run, no in-flight outputs were classified terminal, and no other lane's source was edited.

The parallel-feature manifest records terminal build/run exit 0 for `unique_lifecycle`, `weak_owned_lease`, and `lease_view` under pure-Simple r17 producer SHA-256 `29dd8539f3fe8e01df9b227e0621b20953fd736e239dafef8bafae8918abb3c2`, with exact binary/fixture hashes and log paths. These are focused native LLVM library-component executions, not compiler-generated ownership lifecycle or backend/runtime-matrix qualification. The manifest itself states that no acceptance criterion is signed off. Parent admission log `stage2-r17-admission.log` binds runtime-authority snapshot SHA-256 `a4274058240cd344a5b388f34981699559b257f6c0303fd479df893e950e65f3`; this does not substitute for each criterion's runtime receipt.

The progress record's evidence correction withdraws earlier assertion-only native acceptance claims because false assertions could continue and exit 0. See `doc/08_tracking/bug/native_assert_no_failure_and_schema_empty_read_2026-10-21.md`. New explicit-failure-guard diagnostics must carry their negative control and scope; no component result is promoted to a whole row here.

## Matrix

| Acceptance ID | Status | Required behavior | Evidence limit / next proof gap |
|---|---|---|---|
| AC-DROP-01 | UNVERIFIED | Normal return, reassignment, scope end, error propagation, and cooperative cancellation clean each initialized owner exactly once | Unique library lifecycle probe is narrower than compiler-generated cleanup across return/reassignment/error/cancellation; no route-complete receipt. |
| AC-DROP-02 | UNVERIFIED | Partial construction failure destroys initialized members only, in the defined order | No terminal injected partial-construction cleanup/order receipt. |
| AC-DROP-03 | UNVERIFIED | Observable resource cleanup order is unchanged by last-use optimization | No terminal observable cleanup-order versus last-use-optimization comparison. |
| AC-FAIL-01 | UNVERIFIED | Inject failure at every relevant allocation/registration/publication step; no unchecked store or partial success | No terminal allocation/registration/publication fault-injection matrix. |
| AC-CONT-01 | UNVERIFIED | Fallible insertion and replacement preserve the documented owner on failure and commit it on success | No terminal fallible insertion/replacement owner rollback/commit receipt. |
| AC-CONT-02 | UNVERIFIED | Clear/remove/drain release owned elements without requiring capacity to shrink | No terminal clear/remove/drain live-element release receipt independent of capacity. |
| AC-REG-01 | UNVERIFIED | Inner scope cannot end an outer scope; failed begin does not confer scope ownership | No terminal nested scope-token/failed-begin ownership rejection receipt. |
| AC-REG-02 | UNVERIFIED | Frozen retained roots survive scratch release; intentionally retained scratch references are rejected/detected | No terminal frozen-root survival plus retained-scratch rejection receipt. |
| AC-REG-03 | UNVERIFIED | A resource-bearing arena runs required destructors; a dropless arena has no unnecessary per-node cleanup | No terminal destructor-bearing versus dropless arena cleanup receipt. |
| AC-HANDLE-01 | UNVERIFIED | Freed/reused/wrong-owner/out-of-range/wrapped-generation handles fail resolution | Weak-lease probe covers expiration/reset generations only; no bound receipt for wrong owner, out-of-range, wrap and all freed/reused handle cases. |
| AC-CYCLE-01 | UNVERIFIED | Region-owned cyclic graphs are valid and reclaimed with their owner | No terminal region-owned cyclic graph reclamation receipt. |
| AC-CYCLE-02 | UNVERIFIED | Obvious shared strong-cycle risk is diagnosed in basic mode; ordinary weak/handle backedges are not mislabeled | No terminal basic-mode strong-cycle negative and weak/handle positive diagnostic pair. |
| AC-CYCLE-03 | UNVERIFIED | Deep/runtime budget exhaustion reports incomplete; runtime detection does not collect or mutate objects | No terminal deep/runtime budget exhaustion with read-only incomplete outcome receipt. |
| AC-CYCLE-04 | UNVERIFIED | `cycle_check=off` does not disable mandatory move/drop/short-borrow checks | No terminal cycle_check=off mandatory move/drop/borrow enforcement comparison. |
| AC-PIPE-01 | UNVERIFIED | Fused and split produce equivalent semantics, errors, source locations, and required cleanup | No terminal fused/split semantic/error/location/cleanup equivalence receipt. |
| AC-PIPE-02 | UNVERIFIED | Cold default path parses each exact parser input once; decode/replay and legitimate recovery are separately counted | No terminal per-input cold parse counts separating legitimate decode/recovery. |
| AC-PIPE-03 | UNVERIFIED | Capture-off produces no debug checkpoint allocations/writes; targeted capture/replay remains functional | No terminal capture-off allocation/write counters paired with capture/replay execution. |
| AC-PIPE-04 | UNVERIFIED | Cyclic imports, trait/default bodies, generic instantiation, static conditions, and layout dependencies stay correct | No terminal cyclic imports/traits/generics/static/layout dependency matrix. |
| AC-PIPE-05 | UNVERIFIED | Failed or incomplete SCCs never become admitted executable/SMF success | No terminal failed/incomplete SCC executable/SMF publication rejection receipt. |
| AC-CACHE-01 | UNVERIFIED | Concurrent equal actions have one admitted producer; subscribers reuse the same immutable result | No terminal concurrent equal-action single-producer immutable reuse receipt. |
| AC-CACHE-02 | UNVERIFIED | New edits do not change an in-flight snapshot; expired generations cannot publish | Snapshot objects exist, but no terminal in-flight edit and expired-publisher rejection receipt bound to this criterion. |
| AC-CACHE-03 | UNVERIFIED | Eviction waits for actual reader quiescence; service crash cannot leave writable published artifacts | No terminal reader-quiescence eviction plus crash/writable-publication receipt. |
| AC-CACHE-04 | UNVERIFIED | Changed imports, negative resolution, target, runtime ABI, grammar, aspects, or entry role invalidate the affected stage | No terminal invalidation matrix covering every listed semantic dependency. |
| AC-HASH-01 | UNVERIFIED | Inject equal XXH3 digests for different bytes/actions; no false cache hit or overwrite occurs | No terminal injected equal-XXH3/different-content false-hit/overwrite rejection receipt. |
| AC-HASH-02 | UNVERIFIED | Private-to-untrusted export uses the boundary's strong identity; algorithm/schema confusion is rejected | No terminal boundary strong-identity and algorithm/schema confusion rejection receipt. |
| AC-HASH-03 | UNVERIFIED | Scalar/SIMD/pure/external hashing providers match canonical vectors and streaming/chunk boundary results | No terminal canonical vector/streaming/chunk-boundary comparison across providers. |
| AC-PROC-01 | UNVERIFIED | Timeout, cancellation, parent death, worker crash, and spawn failure leave no surviving managed descendants or leaked reservations | No terminal timeout/cancel/parent-death/crash/spawn-failure descendant and reservation teardown matrix. |
| AC-PROC-02 | UNVERIFIED | PID reuse and unrelated `simple` processes cannot be mistaken for managed children | No terminal PID-reuse/unrelated-process noninterference receipt. |
| AC-BUDGET-01 | UNVERIFIED | Parent/job limit reaches grandchildren; unknown measurements cannot enable unlimited worker fanout | No terminal child/grandchild limit inheritance plus unknown-measurement fail-closed receipt. |
| AC-BUDGET-02 | UNVERIFIED | Queue/fiber/output/device-pin budgets work independently of worker count | No terminal independent queue/fiber/output/device-pin budget matrix. |
| AC-METRIC-01 | UNVERIFIED | Known allocations and process fixtures calibrate bytes/KiB/pages; missing metrics are unavailable, never zero | Build time/RSS logs are observations, not known-allocation unit calibration or missing-metric unavailable controls. |
| AC-METRIC-02 | UNVERIFIED | Repeated equivalent units show bounded scratch after warmup; intentionally retained artifacts are separately attributed | Historical per-entry scratch evidence is acknowledged by plan §2.2; no current exact-owner repeated-unit and retained-artifact attribution receipt. |
| AC-DB-01 | UNVERIFIED | Group migration preserves every existing unrelated row/table and status; malformed/partial input causes no write | No terminal all-row/table-preserving group migration plus malformed/partial-input no-write receipt. |
| AC-GATE-01 | FAIL-OBSERVED | Zero executed tests, omitted mandatory backend, or missing proof root cannot report PASS | False assert/zero-result diagnostic is a documented counterexample; no ordinary gate receipt rejecting zero cases/omitted backend/missing proof root. |
| AC-GATE-02 | UNVERIFIED | Removing/bypassing a checker, cleanup operation, or required test is detected by an independent gate | No terminal independent sabotage/coverage-manifest invocation receipt detecting removed checker/cleanup/test. |

## Admission consequence

The focused runtime library work is useful partial evidence for DROP-01 and HANDLE-01, and lease-view work supports a separately tracked core borrow row. It closes none of the full non-core obligations. Plan §12.2 still requires actual applicable product routes, runtime providers and supported target/host qualification; §12.3 requires relevant mutation controls. Preserve historical repaired paths and narrow receipts without treating them as a fresh full-plan PASS. Phase 3 or landing admission cannot be inferred from this audit.
