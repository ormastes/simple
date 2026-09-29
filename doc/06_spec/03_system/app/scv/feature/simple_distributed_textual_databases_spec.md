# Simple distributed textual databases: SCV + jj + GitHub

**Status:** Design-only and intentionally fail-fast. No scenario is PASS evidence until its subsystem checker invokes the production owner and validates a durable receipt.

**Executable source:** `test/03_system/app/scv/feature/simple_distributed_textual_databases_spec.spl`

## Operator model

Each `@inline` checker owns its named setup contract: `setup_replica_fixture`, `setup_settlement_fixture`, `setup_test_evidence_fixture`, `setup_bridge_fixture`, or `setup_retention_fixture`. Its future production implementation must create an isolated fixture, drive the real owner, inject the stated boundary/fault, and inspect canonical state plus a durable receipt. Today the checker names that sequence and calls `fail(...)`; setup is not a silent test double.

The five visible flows are:

1. `step("Create offline semantic changes")`
2. `step("Settle compact identifiers")`
3. `step("Classify configuration-bound evidence")`
4. `step("Reconcile provider changes")`
5. `step("Retain exact or aggregated history")`

## Exact scenario catalog

| Contract | Fixture/checker | Happy-path scenario | Boundary scenario | Failure scenario |
|---|---|---|---|---|
| REQ-001 — Offline identity | `setup_replica_fixture` / `check_replica_contract` | Should prove that it creates distinct durable IDs on disconnected replicas | Should prove that it rotates incarnation after cloned counter rollback | Should prove that it rejects reused actor-counter identity with different bytes |
| REQ-002 — Compact alias | `setup_replica_fixture` / `check_replica_contract` | Should prove that it resolves a settled u64 under namespace epoch and kind | Should prove that it round-trips a context-elided integer through its versioned header | Should prove that it rejects a bare integer copied without identity context |
| REQ-003 — Canonical identity preservation | `setup_replica_fixture` / `check_replica_contract` | Should prove that it adds aliases without changing ChangeIdentity or RevisionIdentity | Should prove that it keeps canonical identities stable across compaction and replay | Should prove that it rejects alias-driven renumbering of canonical SCV identities |
| REQ-004 — Identity map | `setup_replica_fixture` / `check_replica_contract` | Should prove that it commits bidirectional aliases allocator receipt and tombstone atomically | Should prove that it leaves gaps while preserving high-water marks after deletion | Should prove that it rejects reuse or allocation derived from live row count |
| REQ-005 — Fixed authority | `setup_settlement_fixture` / `check_settlement_contract` | Should prove that it allocates only through the configured protected settled ref | Should prove that it allows a mirror to verify but not allocate identifiers | Should prove that it requires a new namespace when old-authority fencing is unproven |
| REQ-006 — Settlement admission | `setup_settlement_fixture` / `check_settlement_contract` | Should prove that it authorizes signature ACL versions dependencies and closure before allocation | Should prove that it admits an empty conflict-free batch without advancing unrelated allocators | Should prove that it rejects unauthorized or incompatible patches before candidate creation |
| REQ-007 — Atomic candidate | `setup_settlement_fixture` / `check_settlement_contract` | Should prove that it writes allocation aliases rewritten references and registry in one tree | Should prove that it builds a candidate with fetched head as its sole parent | Should prove that it rejects partially published identity state |
| REQ-008 — Publication and uncertainty | `setup_settlement_fixture` / `check_settlement_contract` | Should prove that it publishes by expected-old-head update then verifies accepted batch | Should prove that it replans a losing integrator from the newly fetched head | Should prove that it checks canonical history after lost acknowledgement before allocating again |
| REQ-009 — Rollback detection | `setup_settlement_fixture` / `check_settlement_contract` | Should prove that it verifies the signed chained receipt before next allocation | Should prove that it restores from a current receipt with unchanged high-water marks | Should prove that it blocks ancestry epoch or allocator regression |
| REQ-010 — Typed patches | `setup_settlement_fixture` / `check_settlement_contract` | Should prove that it round-trips every required patch identity dependency and operation field | Should prove that it preserves ordered operations and explicit preconditions | Should prove that it rejects a patch missing signature provenance or version identity |
| REQ-011 — Canonical encoding | `setup_settlement_fixture` / `check_settlement_contract` | Should prove that it produces identical domain-separated bytes for equivalent typed values | Should prove that it keeps delimiter-like Unicode data unambiguous through length framing | Should prove that it quarantines one batch ID reused with different canonical bytes |
| REQ-012 — Pure reducer | `setup_settlement_fixture` / `check_settlement_contract` | Should prove that it reduces an authorized patch without adapter or credential access | Should prove that it returns the same plan under provider-free fixture implementations | Should prove that it rejects merge planning attempted before authorization |
| REQ-013 — Merge semantics | `setup_settlement_fixture` / `check_settlement_contract` | Should prove that it merges concurrent edits to different schema-declared fields | Should prove that it retains delete-update and same-scalar races as explicit conflicts | Should prove that it rejects undeclared list or set merge guesses |
| REQ-014 — Causality | `setup_settlement_fixture` / `check_settlement_contract` | Should prove that it orders causal dependencies before deterministic batch-ID ties | Should prove that it preserves concurrency when remote settlement order differs | Should prove that it rejects missing causal bases instead of inventing order |
| REQ-015 — Replay and compatibility | `setup_settlement_fixture` / `check_settlement_contract` | Should prove that it replays an accepted batch as an idempotent no-op | Should prove that it matches full and incremental materialization during migration | Should prove that it rejects unknown versions and reducer downgrades |
| REQ-016 — Immutable evidence entities | `setup_test_evidence_fixture` / `check_test_evidence_contract` | Should prove that it persists all ten immutable evidence entity kinds with revision links | Should prove that it shares one run manifest across compact observation references | Should prove that it rejects mutation of an admitted evidence revision |
| REQ-017 — Observation identity | `setup_test_evidence_fixture` / `check_test_evidence_contract` | Should prove that it deduplicates identical provider identity and payload digest | Should prove that it retains a genuine rerun under a distinct attempt identity | Should prove that it quarantines identical observation identity with changed bytes |
| REQ-018 — Outcome separation | `setup_test_evidence_fixture` / `check_test_evidence_contract` | Should prove that it classifies immutable actual outcome against a pinned expectation | Should prove that it records XPASS signature mismatch infrastructure and incomplete distinctly | Should prove that it prevents observation ingestion from rewriting expectation policy |
| REQ-019 — Configuration and reproduction | `setup_test_evidence_fixture` / `check_test_evidence_contract` | Should prove that it binds a custom failure to exact config and reproduction revisions | Should prove that it records restricted expired and missing dependency availability honestly | Should prove that it rejects moving names private paths or mutable jj IDs as reproducibility |
| REQ-020 — Coverage finality | `setup_test_evidence_fixture` / `check_test_evidence_contract` | Should prove that it closes a run only after all declared chunks and digests reconcile | Should prove that it records skipped missing retried and superseded shards explicitly | Should prove that it keeps absent observations NOT_RUN or INCOMPLETE rather than PASS |
| REQ-021 — CI authority | `setup_test_evidence_fixture` / `check_test_evidence_contract` | Should prove that it accepts CI observations and evidence under append-only authority | Should prove that it records untrusted fork evidence without release qualification | Should prove that it rejects CI attempts to approve expectations close bugs or promote configs |
| REQ-022 — Git capability contract | `setup_bridge_fixture` / `check_bridge_contract` | Should prove that it settles through exact-head CAS protection and read-back capabilities | Should prove that it classifies a stale-head race separately from transport failure | Should prove that it disables allocator mode without admitted protection or read-back |
| REQ-023 — GitHub-first delivery | `setup_bridge_fixture` / `check_bridge_contract` | Should prove that it round-trips GitHub settlement and Actions ingestion | Should prove that it passes equivalent non-GitHub Git GitLab-CI and Jenkins-class fixtures | Should prove that it rejects provider-specific semantics leaking into the common contract |
| REQ-024 — Provider-neutral CI | `setup_bridge_fixture` / `check_bridge_contract` | Should prove that it normalizes declared run attempt artifact and attestation identity | Should prove that it handles event poll bundle and paginated sources without double count | Should prove that it rejects sources whose uniqueness dimensions cannot be proven |
| REQ-025 — Durable discovery | `setup_bridge_fixture` / `check_bridge_contract` | Should prove that it persists a discoverable manifest before acknowledging a producer | Should prove that it reconciles missed events with overlapping persisted polling windows | Should prove that it does not advance a cursor before durable canonical acceptance |
| REQ-026 — Bounded ingestion | `setup_bridge_fixture` / `check_bridge_contract` | Should prove that it streams a valid quarantined bundle within every declared quota | Should prove that it handles boundary-sized paths nesting and decompression safely | Should prove that it rejects traversal links devices Unicode ambiguity bombs and executable content |
| REQ-027 — Bridge delivery | `setup_bridge_fixture` / `check_bridge_contract` | Should prove that it moves committed intent from pending through acknowledged with read-back | Should prove that it recovers sent-unconfirmed delivery without duplicating remote effects | Should prove that it quarantines mismatched replay and preserves uncertain effects |
| REQ-028 — Provider conflict semantics | `setup_bridge_fixture` / `check_bridge_contract` | Should prove that it three-way merges one-sided provider changes from last-common state | Should prove that it distinguishes inaccessible remote state from confirmed deletion | Should prove that it surfaces concurrent scalar conflict and prevents causation loops |
| REQ-029 — Writer ownership | `setup_bridge_fixture` / `check_bridge_contract` | Should prove that it commits every mutation through the SJ lease capsule | Should prove that it persists intent and releases the lease during provider waits | Should prove that it rejects independent Git jj or adapter mutation of one checkout |
| REQ-030 — Semantic and evidence placement | `setup_retention_fixture` / `check_retention_contract` | Should prove that it stores durable semantics in Git and raw evidence in controlled CAS | Should prove that it hydrates raw bytes through a digest-verified manifest | Should prove that it rejects high-volume raw evidence from canonical Git ancestry |
| REQ-031 — Retention classes | `setup_retention_fixture` / `check_retention_contract` | Should prove that it keeps 28-day exact telemetry and versioned daily rollups afterward | Should prove that it pins complete unresolved release pending and reproduction closure | Should prove that it refuses age-based pruning of unsynchronized work |
| REQ-032 — Honest resolution | `setup_retention_fixture` / `check_retention_contract` | Should prove that it returns exact aggregated restricted or unavailable explicitly | Should prove that it reports a day-end aggregate without claiming an exact revision | Should prove that it rejects a manifest-only claim that missing bytes remain available |
| REQ-033 — Rollup correctness | `setup_retention_fixture` / `check_retention_contract` | Should prove that it deduplicates counts and merges declared timing sketches | Should prove that it revises provenance when late input changes a daily rollup | Should prove that it rejects averaging daily percentiles as a global percentile |
| REQ-034 — Resnapshot | `setup_retention_fixture` / `check_retention_contract` | Should prove that it rebases pending semantic work onto a complete resnapshot | Should prove that it retains alias allocator tombstone merge batch and history knowledge | Should prove that it returns ResnapshotRequired rather than resurrecting stale entities |
| REQ-035 — Confidentiality and deletion | `setup_retention_fixture` / `check_retention_contract` | Should prove that it filters secrets and unnecessary PII before Git ingestion | Should prove that it erases restricted CAS keys while reporting immutable-copy limits | Should prove that it rejects secret-bearing metadata under default-deny policy |
| REQ-036 — One app path | `setup_retention_fixture` / `check_retention_contract` | Should prove that it runs the same orchestration through capability-selected adapters | Should prove that it uses platform differences only behind existing HAL interfaces | Should prove that it rejects per-OS sibling or raw-runtime fallback implementations |
| NFR-001 — Fixture receipt | `setup_settlement_fixture` / `check_settlement_contract` | Should prove that it records a complete reproducible performance receipt | Should prove that it distinguishes cold warm percentile and timeout methods | Should prove that it rejects a threshold claim with missing fixture or raw evidence fields |
| NFR-002 — Scale | `setup_settlement_fixture` / `check_settlement_contract` | Should prove that it builds the one-million-alias and observation Operating-B corpus | Should prove that it imports exactly ten thousand representative observations | Should prove that it rejects a reduced corpus presented as Operating-B evidence |
| NFR-003 — Query latency | `setup_settlement_fixture` / `check_settlement_contract` | Should prove that it measures warm alias and current-status p95 within 100 ms | Should prove that it reports p50 p95 p99 and dedup p95 within 250 ms | Should prove that it fails admission when any measured percentile exceeds its limit |
| NFR-004 — Import resources | `setup_settlement_fixture` / `check_settlement_contract` | Should prove that it validates ten thousand observations within 5 s and 256 MiB | Should prove that it includes decode auth closure dedup and patch construction costs | Should prove that it fails admission when elapsed time or max RSS exceeds budget |
| NFR-005 — Maintenance resources | `setup_settlement_fixture` / `check_settlement_contract` | Should prove that it compacts one million rows within 10 s and 512 MiB | Should prove that it rebases ten thousand operations within 60 s | Should prove that it fails admission when either maintenance threshold is exceeded |
| NFR-006 — Recovery | `setup_settlement_fixture` / `check_settlement_contract` | Should prove that it recovers settlement within ten minutes after dependencies return | Should prove that it applies bounded backpressure while preserving oldest pending work | Should prove that it rejects overflow behavior that discards pending semantic work |
| NFR-007 — Exact window | `setup_retention_fixture` / `check_retention_contract` | Should prove that it retrieves routine raw observations exactly through day 28 | Should prove that it labels older daily summaries with reducer version and provenance | Should prove that it rejects early loss or an unversioned aggregate |
| NFR-008 — Archive closure | `setup_retention_fixture` / `check_retention_contract` | Should prove that it verifies complete pinned evidence closure before provider expiry | Should prove that it hydrates a retained 100 MiB local bundle within 5 s | Should prove that it fails a pin with missing digest closure or expired-only location |
| NFR-009 — Semantic repository growth | `setup_retention_fixture` / `check_retention_contract` | Should prove that it measures ten-year packed objects and clone transfer within 2 GiB | Should prove that it reports external CAS bytes separately from semantic Git | Should prove that it fails admission when either canonical Git measure exceeds 2 GiB |
| NFR-010 — Integrity | `setup_retention_fixture` / `check_retention_contract` | Should prove that it proves zero reuse resurrection inflation loss escalation and secret fields | Should prove that it verifies every accepted reference receipt and archive digest | Should prove that it fails on the first integrity violation or incomplete closure |
| NFR-011 — Cryptography agility | `setup_bridge_fixture` / `check_bridge_contract` | Should prove that it verifies algorithm-tagged domain-separated signatures and digests | Should prove that it rotates and revokes keys without changing schema identity | Should prove that it rejects cross-repository namespace epoch or provider replay |
| NFR-012 — Least privilege | `setup_bridge_fixture` / `check_bridge_contract` | Should prove that it settles and publishes with scoped credentials outside untrusted steps | Should prove that it separates authenticated transport identity from operation authority | Should prove that it rejects credential access or privilege escalation from test payloads |
| NFR-013 — Fail closed | `setup_bridge_fixture` / `check_bridge_contract` | Should prove that it returns typed errors for unsupported unsafe or ambiguous state | Should prove that it leaves settled identity unpublished after every rejection | Should prove that it rejects fallback publication on malformed encoding quota or regression |
| NFR-014 — Determinism | `setup_replica_fixture` / `check_replica_contract` | Should prove that it matches canonical full and incremental tree digests across hosts | Should prove that it repeats equivalent accepted logs with stable ordering | Should prove that it fails when host order or execution path changes canonical output |
| NFR-015 — Portability | `setup_replica_fixture` / `check_replica_contract` | Should prove that it runs one pure semantic core through all capability fixtures | Should prove that it keeps subprocess network OS and runtime code in adapters | Should prove that it rejects forbidden provider SDK or raw runtime dependency in the core |

## Execution and evidence

Run only after production helpers exist. Compiled-mode execution must validate production behavior; interpreter loading is not evidence. Store protocol transcripts, signed settlement receipts, normalized CI envelopes, provider read-back, CAS manifests, crash logs, and benchmark records under `build/test-artifacts/03_system/app/scv/feature/simple_distributed_textual_databases/`. Missing helpers, receipts, dependencies, or capabilities are failures.

## Folded executable SSpec

<details>
<summary>Show exact executable design</summary>

```simple
# codex-system-test
# @evidence-display: links
# Design-first acceptance specification. Every checker fails explicitly until it
# is replaced by a production-owner fixture and durable receipt validation.

use std.spec.*

# @inline
fn check_replica_contract(requirement: String, oracle: String, failure_sequence: String):
    fail("UNIMPLEMENTED {requirement}: setup_replica_fixture -> {oracle}; failure sequence: {failure_sequence}")

# @inline
fn check_settlement_contract(requirement: String, oracle: String, failure_sequence: String):
    fail("UNIMPLEMENTED {requirement}: setup_settlement_fixture -> {oracle}; failure sequence: {failure_sequence}")

# @inline
fn check_test_evidence_contract(requirement: String, oracle: String, failure_sequence: String):
    fail("UNIMPLEMENTED {requirement}: setup_test_evidence_fixture -> {oracle}; failure sequence: {failure_sequence}")

# @inline
fn check_bridge_contract(requirement: String, oracle: String, failure_sequence: String):
    fail("UNIMPLEMENTED {requirement}: setup_bridge_fixture -> {oracle}; failure sequence: {failure_sequence}")

# @inline
fn check_retention_contract(requirement: String, oracle: String, failure_sequence: String):
    fail("UNIMPLEMENTED {requirement}: setup_retention_fixture -> {oracle}; failure sequence: {failure_sequence}")

describe "Simple distributed textual databases: SCV + jj + GitHub":
    describe "REQ-001: Offline identity":
        it "should prove that it creates distinct durable IDs on disconnected replicas":
            step("Create offline semantic changes")
            step("Drive accepted state and inspect its receipt")
            check_replica_contract("REQ-001", "drive accepted offline identity state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it rotates incarnation after cloned counter rollback":
            step("Create offline semantic changes")
            step("Drive the boundary state and inspect preserved invariants")
            check_replica_contract("REQ-001", "drive boundary offline identity state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects reused actor-counter identity with different bytes":
            step("Create offline semantic changes")
            step("Inject the failure and inspect fail-closed state")
            check_replica_contract("REQ-001", "inject unsafe offline identity state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-002: Compact alias":
        it "should prove that it resolves a settled u64 under namespace epoch and kind":
            step("Create offline semantic changes")
            step("Drive accepted state and inspect its receipt")
            check_replica_contract("REQ-002", "drive accepted compact alias state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it round-trips a context-elided integer through its versioned header":
            step("Create offline semantic changes")
            step("Drive the boundary state and inspect preserved invariants")
            check_replica_contract("REQ-002", "drive boundary compact alias state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects a bare integer copied without identity context":
            step("Create offline semantic changes")
            step("Inject the failure and inspect fail-closed state")
            check_replica_contract("REQ-002", "inject unsafe compact alias state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-003: Canonical identity preservation":
        it "should prove that it adds aliases without changing ChangeIdentity or RevisionIdentity":
            step("Create offline semantic changes")
            step("Drive accepted state and inspect its receipt")
            check_replica_contract("REQ-003", "drive accepted canonical identity preservation state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it keeps canonical identities stable across compaction and replay":
            step("Create offline semantic changes")
            step("Drive the boundary state and inspect preserved invariants")
            check_replica_contract("REQ-003", "drive boundary canonical identity preservation state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects alias-driven renumbering of canonical SCV identities":
            step("Create offline semantic changes")
            step("Inject the failure and inspect fail-closed state")
            check_replica_contract("REQ-003", "inject unsafe canonical identity preservation state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-004: Identity map":
        it "should prove that it commits bidirectional aliases allocator receipt and tombstone atomically":
            step("Create offline semantic changes")
            step("Drive accepted state and inspect its receipt")
            check_replica_contract("REQ-004", "drive accepted identity map state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it leaves gaps while preserving high-water marks after deletion":
            step("Create offline semantic changes")
            step("Drive the boundary state and inspect preserved invariants")
            check_replica_contract("REQ-004", "drive boundary identity map state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects reuse or allocation derived from live row count":
            step("Create offline semantic changes")
            step("Inject the failure and inspect fail-closed state")
            check_replica_contract("REQ-004", "inject unsafe identity map state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-005: Fixed authority":
        it "should prove that it allocates only through the configured protected settled ref":
            step("Settle compact identifiers")
            step("Drive accepted state and inspect its receipt")
            check_settlement_contract("REQ-005", "drive accepted fixed authority state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it allows a mirror to verify but not allocate identifiers":
            step("Settle compact identifiers")
            step("Drive the boundary state and inspect preserved invariants")
            check_settlement_contract("REQ-005", "drive boundary fixed authority state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it requires a new namespace when old-authority fencing is unproven":
            step("Settle compact identifiers")
            step("Inject the failure and inspect fail-closed state")
            check_settlement_contract("REQ-005", "inject unsafe fixed authority state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-006: Settlement admission":
        it "should prove that it authorizes signature ACL versions dependencies and closure before allocation":
            step("Settle compact identifiers")
            step("Drive accepted state and inspect its receipt")
            check_settlement_contract("REQ-006", "drive accepted settlement admission state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it admits an empty conflict-free batch without advancing unrelated allocators":
            step("Settle compact identifiers")
            step("Drive the boundary state and inspect preserved invariants")
            check_settlement_contract("REQ-006", "drive boundary settlement admission state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects unauthorized or incompatible patches before candidate creation":
            step("Settle compact identifiers")
            step("Inject the failure and inspect fail-closed state")
            check_settlement_contract("REQ-006", "inject unsafe settlement admission state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-007: Atomic candidate":
        it "should prove that it writes allocation aliases rewritten references and registry in one tree":
            step("Settle compact identifiers")
            step("Drive accepted state and inspect its receipt")
            check_settlement_contract("REQ-007", "drive accepted atomic candidate state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it builds a candidate with fetched head as its sole parent":
            step("Settle compact identifiers")
            step("Drive the boundary state and inspect preserved invariants")
            check_settlement_contract("REQ-007", "drive boundary atomic candidate state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects partially published identity state":
            step("Settle compact identifiers")
            step("Inject the failure and inspect fail-closed state")
            check_settlement_contract("REQ-007", "inject unsafe atomic candidate state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-008: Publication and uncertainty":
        it "should prove that it publishes by expected-old-head update then verifies accepted batch":
            step("Settle compact identifiers")
            step("Drive accepted state and inspect its receipt")
            check_settlement_contract("REQ-008", "drive accepted publication and uncertainty state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it replans a losing integrator from the newly fetched head":
            step("Settle compact identifiers")
            step("Drive the boundary state and inspect preserved invariants")
            check_settlement_contract("REQ-008", "drive boundary publication and uncertainty state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it checks canonical history after lost acknowledgement before allocating again":
            step("Settle compact identifiers")
            step("Inject the failure and inspect fail-closed state")
            check_settlement_contract("REQ-008", "inject unsafe publication and uncertainty state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-009: Rollback detection":
        it "should prove that it verifies the signed chained receipt before next allocation":
            step("Settle compact identifiers")
            step("Drive accepted state and inspect its receipt")
            check_settlement_contract("REQ-009", "drive accepted rollback detection state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it restores from a current receipt with unchanged high-water marks":
            step("Settle compact identifiers")
            step("Drive the boundary state and inspect preserved invariants")
            check_settlement_contract("REQ-009", "drive boundary rollback detection state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it blocks ancestry epoch or allocator regression":
            step("Settle compact identifiers")
            step("Inject the failure and inspect fail-closed state")
            check_settlement_contract("REQ-009", "inject unsafe rollback detection state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-010: Typed patches":
        it "should prove that it round-trips every required patch identity dependency and operation field":
            step("Settle compact identifiers")
            step("Drive accepted state and inspect its receipt")
            check_settlement_contract("REQ-010", "drive accepted typed patches state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it preserves ordered operations and explicit preconditions":
            step("Settle compact identifiers")
            step("Drive the boundary state and inspect preserved invariants")
            check_settlement_contract("REQ-010", "drive boundary typed patches state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects a patch missing signature provenance or version identity":
            step("Settle compact identifiers")
            step("Inject the failure and inspect fail-closed state")
            check_settlement_contract("REQ-010", "inject unsafe typed patches state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-011: Canonical encoding":
        it "should prove that it produces identical domain-separated bytes for equivalent typed values":
            step("Settle compact identifiers")
            step("Drive accepted state and inspect its receipt")
            check_settlement_contract("REQ-011", "drive accepted canonical encoding state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it keeps delimiter-like Unicode data unambiguous through length framing":
            step("Settle compact identifiers")
            step("Drive the boundary state and inspect preserved invariants")
            check_settlement_contract("REQ-011", "drive boundary canonical encoding state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it quarantines one batch ID reused with different canonical bytes":
            step("Settle compact identifiers")
            step("Inject the failure and inspect fail-closed state")
            check_settlement_contract("REQ-011", "inject unsafe canonical encoding state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-012: Pure reducer":
        it "should prove that it reduces an authorized patch without adapter or credential access":
            step("Settle compact identifiers")
            step("Drive accepted state and inspect its receipt")
            check_settlement_contract("REQ-012", "drive accepted pure reducer state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it returns the same plan under provider-free fixture implementations":
            step("Settle compact identifiers")
            step("Drive the boundary state and inspect preserved invariants")
            check_settlement_contract("REQ-012", "drive boundary pure reducer state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects merge planning attempted before authorization":
            step("Settle compact identifiers")
            step("Inject the failure and inspect fail-closed state")
            check_settlement_contract("REQ-012", "inject unsafe pure reducer state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-013: Merge semantics":
        it "should prove that it merges concurrent edits to different schema-declared fields":
            step("Settle compact identifiers")
            step("Drive accepted state and inspect its receipt")
            check_settlement_contract("REQ-013", "drive accepted merge semantics state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it retains delete-update and same-scalar races as explicit conflicts":
            step("Settle compact identifiers")
            step("Drive the boundary state and inspect preserved invariants")
            check_settlement_contract("REQ-013", "drive boundary merge semantics state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects undeclared list or set merge guesses":
            step("Settle compact identifiers")
            step("Inject the failure and inspect fail-closed state")
            check_settlement_contract("REQ-013", "inject unsafe merge semantics state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-014: Causality":
        it "should prove that it orders causal dependencies before deterministic batch-ID ties":
            step("Settle compact identifiers")
            step("Drive accepted state and inspect its receipt")
            check_settlement_contract("REQ-014", "drive accepted causality state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it preserves concurrency when remote settlement order differs":
            step("Settle compact identifiers")
            step("Drive the boundary state and inspect preserved invariants")
            check_settlement_contract("REQ-014", "drive boundary causality state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects missing causal bases instead of inventing order":
            step("Settle compact identifiers")
            step("Inject the failure and inspect fail-closed state")
            check_settlement_contract("REQ-014", "inject unsafe causality state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-015: Replay and compatibility":
        it "should prove that it replays an accepted batch as an idempotent no-op":
            step("Settle compact identifiers")
            step("Drive accepted state and inspect its receipt")
            check_settlement_contract("REQ-015", "drive accepted replay and compatibility state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it matches full and incremental materialization during migration":
            step("Settle compact identifiers")
            step("Drive the boundary state and inspect preserved invariants")
            check_settlement_contract("REQ-015", "drive boundary replay and compatibility state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects unknown versions and reducer downgrades":
            step("Settle compact identifiers")
            step("Inject the failure and inspect fail-closed state")
            check_settlement_contract("REQ-015", "inject unsafe replay and compatibility state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-016: Immutable evidence entities":
        it "should prove that it persists all ten immutable evidence entity kinds with revision links":
            step("Classify configuration-bound evidence")
            step("Drive accepted state and inspect its receipt")
            check_test_evidence_contract("REQ-016", "drive accepted immutable evidence entities state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it shares one run manifest across compact observation references":
            step("Classify configuration-bound evidence")
            step("Drive the boundary state and inspect preserved invariants")
            check_test_evidence_contract("REQ-016", "drive boundary immutable evidence entities state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects mutation of an admitted evidence revision":
            step("Classify configuration-bound evidence")
            step("Inject the failure and inspect fail-closed state")
            check_test_evidence_contract("REQ-016", "inject unsafe immutable evidence entities state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-017: Observation identity":
        it "should prove that it deduplicates identical provider identity and payload digest":
            step("Classify configuration-bound evidence")
            step("Drive accepted state and inspect its receipt")
            check_test_evidence_contract("REQ-017", "drive accepted observation identity state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it retains a genuine rerun under a distinct attempt identity":
            step("Classify configuration-bound evidence")
            step("Drive the boundary state and inspect preserved invariants")
            check_test_evidence_contract("REQ-017", "drive boundary observation identity state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it quarantines identical observation identity with changed bytes":
            step("Classify configuration-bound evidence")
            step("Inject the failure and inspect fail-closed state")
            check_test_evidence_contract("REQ-017", "inject unsafe observation identity state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-018: Outcome separation":
        it "should prove that it classifies immutable actual outcome against a pinned expectation":
            step("Classify configuration-bound evidence")
            step("Drive accepted state and inspect its receipt")
            check_test_evidence_contract("REQ-018", "drive accepted outcome separation state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it records XPASS signature mismatch infrastructure and incomplete distinctly":
            step("Classify configuration-bound evidence")
            step("Drive the boundary state and inspect preserved invariants")
            check_test_evidence_contract("REQ-018", "drive boundary outcome separation state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it prevents observation ingestion from rewriting expectation policy":
            step("Classify configuration-bound evidence")
            step("Inject the failure and inspect fail-closed state")
            check_test_evidence_contract("REQ-018", "inject unsafe outcome separation state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-019: Configuration and reproduction":
        it "should prove that it binds a custom failure to exact config and reproduction revisions":
            step("Classify configuration-bound evidence")
            step("Drive accepted state and inspect its receipt")
            check_test_evidence_contract("REQ-019", "drive accepted configuration and reproduction state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it records restricted expired and missing dependency availability honestly":
            step("Classify configuration-bound evidence")
            step("Drive the boundary state and inspect preserved invariants")
            check_test_evidence_contract("REQ-019", "drive boundary configuration and reproduction state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects moving names private paths or mutable jj IDs as reproducibility":
            step("Classify configuration-bound evidence")
            step("Inject the failure and inspect fail-closed state")
            check_test_evidence_contract("REQ-019", "inject unsafe configuration and reproduction state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-020: Coverage finality":
        it "should prove that it closes a run only after all declared chunks and digests reconcile":
            step("Classify configuration-bound evidence")
            step("Drive accepted state and inspect its receipt")
            check_test_evidence_contract("REQ-020", "drive accepted coverage finality state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it records skipped missing retried and superseded shards explicitly":
            step("Classify configuration-bound evidence")
            step("Drive the boundary state and inspect preserved invariants")
            check_test_evidence_contract("REQ-020", "drive boundary coverage finality state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it keeps absent observations NOT_RUN or INCOMPLETE rather than PASS":
            step("Classify configuration-bound evidence")
            step("Inject the failure and inspect fail-closed state")
            check_test_evidence_contract("REQ-020", "inject unsafe coverage finality state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-021: CI authority":
        it "should prove that it accepts CI observations and evidence under append-only authority":
            step("Classify configuration-bound evidence")
            step("Drive accepted state and inspect its receipt")
            check_test_evidence_contract("REQ-021", "drive accepted ci authority state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it records untrusted fork evidence without release qualification":
            step("Classify configuration-bound evidence")
            step("Drive the boundary state and inspect preserved invariants")
            check_test_evidence_contract("REQ-021", "drive boundary ci authority state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects CI attempts to approve expectations close bugs or promote configs":
            step("Classify configuration-bound evidence")
            step("Inject the failure and inspect fail-closed state")
            check_test_evidence_contract("REQ-021", "inject unsafe ci authority state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-022: Git capability contract":
        it "should prove that it settles through exact-head CAS protection and read-back capabilities":
            step("Reconcile provider changes")
            step("Drive accepted state and inspect its receipt")
            check_bridge_contract("REQ-022", "drive accepted git capability contract state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it classifies a stale-head race separately from transport failure":
            step("Reconcile provider changes")
            step("Drive the boundary state and inspect preserved invariants")
            check_bridge_contract("REQ-022", "drive boundary git capability contract state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it disables allocator mode without admitted protection or read-back":
            step("Reconcile provider changes")
            step("Inject the failure and inspect fail-closed state")
            check_bridge_contract("REQ-022", "inject unsafe git capability contract state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-023: GitHub-first delivery":
        it "should prove that it round-trips GitHub settlement and Actions ingestion":
            step("Reconcile provider changes")
            step("Drive accepted state and inspect its receipt")
            check_bridge_contract("REQ-023", "drive accepted github-first delivery state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it passes equivalent non-GitHub Git GitLab-CI and Jenkins-class fixtures":
            step("Reconcile provider changes")
            step("Drive the boundary state and inspect preserved invariants")
            check_bridge_contract("REQ-023", "drive boundary github-first delivery state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects provider-specific semantics leaking into the common contract":
            step("Reconcile provider changes")
            step("Inject the failure and inspect fail-closed state")
            check_bridge_contract("REQ-023", "inject unsafe github-first delivery state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-024: Provider-neutral CI":
        it "should prove that it normalizes declared run attempt artifact and attestation identity":
            step("Reconcile provider changes")
            step("Drive accepted state and inspect its receipt")
            check_bridge_contract("REQ-024", "drive accepted provider-neutral ci state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it handles event poll bundle and paginated sources without double count":
            step("Reconcile provider changes")
            step("Drive the boundary state and inspect preserved invariants")
            check_bridge_contract("REQ-024", "drive boundary provider-neutral ci state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects sources whose uniqueness dimensions cannot be proven":
            step("Reconcile provider changes")
            step("Inject the failure and inspect fail-closed state")
            check_bridge_contract("REQ-024", "inject unsafe provider-neutral ci state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-025: Durable discovery":
        it "should prove that it persists a discoverable manifest before acknowledging a producer":
            step("Reconcile provider changes")
            step("Drive accepted state and inspect its receipt")
            check_bridge_contract("REQ-025", "drive accepted durable discovery state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it reconciles missed events with overlapping persisted polling windows":
            step("Reconcile provider changes")
            step("Drive the boundary state and inspect preserved invariants")
            check_bridge_contract("REQ-025", "drive boundary durable discovery state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it does not advance a cursor before durable canonical acceptance":
            step("Reconcile provider changes")
            step("Inject the failure and inspect fail-closed state")
            check_bridge_contract("REQ-025", "inject unsafe durable discovery state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-026: Bounded ingestion":
        it "should prove that it streams a valid quarantined bundle within every declared quota":
            step("Reconcile provider changes")
            step("Drive accepted state and inspect its receipt")
            check_bridge_contract("REQ-026", "drive accepted bounded ingestion state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it handles boundary-sized paths nesting and decompression safely":
            step("Reconcile provider changes")
            step("Drive the boundary state and inspect preserved invariants")
            check_bridge_contract("REQ-026", "drive boundary bounded ingestion state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects traversal links devices Unicode ambiguity bombs and executable content":
            step("Reconcile provider changes")
            step("Inject the failure and inspect fail-closed state")
            check_bridge_contract("REQ-026", "inject unsafe bounded ingestion state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-027: Bridge delivery":
        it "should prove that it moves committed intent from pending through acknowledged with read-back":
            step("Reconcile provider changes")
            step("Drive accepted state and inspect its receipt")
            check_bridge_contract("REQ-027", "drive accepted bridge delivery state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it recovers sent-unconfirmed delivery without duplicating remote effects":
            step("Reconcile provider changes")
            step("Drive the boundary state and inspect preserved invariants")
            check_bridge_contract("REQ-027", "drive boundary bridge delivery state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it quarantines mismatched replay and preserves uncertain effects":
            step("Reconcile provider changes")
            step("Inject the failure and inspect fail-closed state")
            check_bridge_contract("REQ-027", "inject unsafe bridge delivery state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-028: Provider conflict semantics":
        it "should prove that it three-way merges one-sided provider changes from last-common state":
            step("Reconcile provider changes")
            step("Drive accepted state and inspect its receipt")
            check_bridge_contract("REQ-028", "drive accepted provider conflict semantics state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it distinguishes inaccessible remote state from confirmed deletion":
            step("Reconcile provider changes")
            step("Drive the boundary state and inspect preserved invariants")
            check_bridge_contract("REQ-028", "drive boundary provider conflict semantics state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it surfaces concurrent scalar conflict and prevents causation loops":
            step("Reconcile provider changes")
            step("Inject the failure and inspect fail-closed state")
            check_bridge_contract("REQ-028", "inject unsafe provider conflict semantics state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-029: Writer ownership":
        it "should prove that it commits every mutation through the SJ lease capsule":
            step("Reconcile provider changes")
            step("Drive accepted state and inspect its receipt")
            check_bridge_contract("REQ-029", "drive accepted writer ownership state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it persists intent and releases the lease during provider waits":
            step("Reconcile provider changes")
            step("Drive the boundary state and inspect preserved invariants")
            check_bridge_contract("REQ-029", "drive boundary writer ownership state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects independent Git jj or adapter mutation of one checkout":
            step("Reconcile provider changes")
            step("Inject the failure and inspect fail-closed state")
            check_bridge_contract("REQ-029", "inject unsafe writer ownership state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-030: Semantic and evidence placement":
        it "should prove that it stores durable semantics in Git and raw evidence in controlled CAS":
            step("Retain exact or aggregated history")
            step("Drive accepted state and inspect its receipt")
            check_retention_contract("REQ-030", "drive accepted semantic and evidence placement state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it hydrates raw bytes through a digest-verified manifest":
            step("Retain exact or aggregated history")
            step("Drive the boundary state and inspect preserved invariants")
            check_retention_contract("REQ-030", "drive boundary semantic and evidence placement state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects high-volume raw evidence from canonical Git ancestry":
            step("Retain exact or aggregated history")
            step("Inject the failure and inspect fail-closed state")
            check_retention_contract("REQ-030", "inject unsafe semantic and evidence placement state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-031: Retention classes":
        it "should prove that it keeps 28-day exact telemetry and versioned daily rollups afterward":
            step("Retain exact or aggregated history")
            step("Drive accepted state and inspect its receipt")
            check_retention_contract("REQ-031", "drive accepted retention classes state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it pins complete unresolved release pending and reproduction closure":
            step("Retain exact or aggregated history")
            step("Drive the boundary state and inspect preserved invariants")
            check_retention_contract("REQ-031", "drive boundary retention classes state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it refuses age-based pruning of unsynchronized work":
            step("Retain exact or aggregated history")
            step("Inject the failure and inspect fail-closed state")
            check_retention_contract("REQ-031", "inject unsafe retention classes state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-032: Honest resolution":
        it "should prove that it returns exact aggregated restricted or unavailable explicitly":
            step("Retain exact or aggregated history")
            step("Drive accepted state and inspect its receipt")
            check_retention_contract("REQ-032", "drive accepted honest resolution state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it reports a day-end aggregate without claiming an exact revision":
            step("Retain exact or aggregated history")
            step("Drive the boundary state and inspect preserved invariants")
            check_retention_contract("REQ-032", "drive boundary honest resolution state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects a manifest-only claim that missing bytes remain available":
            step("Retain exact or aggregated history")
            step("Inject the failure and inspect fail-closed state")
            check_retention_contract("REQ-032", "inject unsafe honest resolution state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-033: Rollup correctness":
        it "should prove that it deduplicates counts and merges declared timing sketches":
            step("Retain exact or aggregated history")
            step("Drive accepted state and inspect its receipt")
            check_retention_contract("REQ-033", "drive accepted rollup correctness state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it revises provenance when late input changes a daily rollup":
            step("Retain exact or aggregated history")
            step("Drive the boundary state and inspect preserved invariants")
            check_retention_contract("REQ-033", "drive boundary rollup correctness state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects averaging daily percentiles as a global percentile":
            step("Retain exact or aggregated history")
            step("Inject the failure and inspect fail-closed state")
            check_retention_contract("REQ-033", "inject unsafe rollup correctness state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-034: Resnapshot":
        it "should prove that it rebases pending semantic work onto a complete resnapshot":
            step("Retain exact or aggregated history")
            step("Drive accepted state and inspect its receipt")
            check_retention_contract("REQ-034", "drive accepted resnapshot state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it retains alias allocator tombstone merge batch and history knowledge":
            step("Retain exact or aggregated history")
            step("Drive the boundary state and inspect preserved invariants")
            check_retention_contract("REQ-034", "drive boundary resnapshot state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it returns ResnapshotRequired rather than resurrecting stale entities":
            step("Retain exact or aggregated history")
            step("Inject the failure and inspect fail-closed state")
            check_retention_contract("REQ-034", "inject unsafe resnapshot state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-035: Confidentiality and deletion":
        it "should prove that it filters secrets and unnecessary PII before Git ingestion":
            step("Retain exact or aggregated history")
            step("Drive accepted state and inspect its receipt")
            check_retention_contract("REQ-035", "drive accepted confidentiality and deletion state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it erases restricted CAS keys while reporting immutable-copy limits":
            step("Retain exact or aggregated history")
            step("Drive the boundary state and inspect preserved invariants")
            check_retention_contract("REQ-035", "drive boundary confidentiality and deletion state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects secret-bearing metadata under default-deny policy":
            step("Retain exact or aggregated history")
            step("Inject the failure and inspect fail-closed state")
            check_retention_contract("REQ-035", "inject unsafe confidentiality and deletion state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "REQ-036: One app path":
        it "should prove that it runs the same orchestration through capability-selected adapters":
            step("Retain exact or aggregated history")
            step("Drive accepted state and inspect its receipt")
            check_retention_contract("REQ-036", "drive accepted one app path state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it uses platform differences only behind existing HAL interfaces":
            step("Retain exact or aggregated history")
            step("Drive the boundary state and inspect preserved invariants")
            check_retention_contract("REQ-036", "drive boundary one app path state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects per-OS sibling or raw-runtime fallback implementations":
            step("Retain exact or aggregated history")
            step("Inject the failure and inspect fail-closed state")
            check_retention_contract("REQ-036", "inject unsafe one app path state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "NFR-001: Fixture receipt":
        it "should prove that it records a complete reproducible performance receipt":
            step("Settle compact identifiers")
            step("Drive accepted state and inspect its receipt")
            check_settlement_contract("NFR-001", "drive accepted fixture receipt state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it distinguishes cold warm percentile and timeout methods":
            step("Settle compact identifiers")
            step("Drive the boundary state and inspect preserved invariants")
            check_settlement_contract("NFR-001", "drive boundary fixture receipt state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects a threshold claim with missing fixture or raw evidence fields":
            step("Settle compact identifiers")
            step("Inject the failure and inspect fail-closed state")
            check_settlement_contract("NFR-001", "inject unsafe fixture receipt state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "NFR-002: Scale":
        it "should prove that it builds the one-million-alias and observation Operating-B corpus":
            step("Settle compact identifiers")
            step("Drive accepted state and inspect its receipt")
            check_settlement_contract("NFR-002", "drive accepted scale state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it imports exactly ten thousand representative observations":
            step("Settle compact identifiers")
            step("Drive the boundary state and inspect preserved invariants")
            check_settlement_contract("NFR-002", "drive boundary scale state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects a reduced corpus presented as Operating-B evidence":
            step("Settle compact identifiers")
            step("Inject the failure and inspect fail-closed state")
            check_settlement_contract("NFR-002", "inject unsafe scale state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "NFR-003: Query latency":
        it "should prove that it measures warm alias and current-status p95 within 100 ms":
            step("Settle compact identifiers")
            step("Drive accepted state and inspect its receipt")
            check_settlement_contract("NFR-003", "drive accepted query latency state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it reports p50 p95 p99 and dedup p95 within 250 ms":
            step("Settle compact identifiers")
            step("Drive the boundary state and inspect preserved invariants")
            check_settlement_contract("NFR-003", "drive boundary query latency state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it fails admission when any measured percentile exceeds its limit":
            step("Settle compact identifiers")
            step("Inject the failure and inspect fail-closed state")
            check_settlement_contract("NFR-003", "inject unsafe query latency state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "NFR-004: Import resources":
        it "should prove that it validates ten thousand observations within 5 s and 256 MiB":
            step("Settle compact identifiers")
            step("Drive accepted state and inspect its receipt")
            check_settlement_contract("NFR-004", "drive accepted import resources state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it includes decode auth closure dedup and patch construction costs":
            step("Settle compact identifiers")
            step("Drive the boundary state and inspect preserved invariants")
            check_settlement_contract("NFR-004", "drive boundary import resources state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it fails admission when elapsed time or max RSS exceeds budget":
            step("Settle compact identifiers")
            step("Inject the failure and inspect fail-closed state")
            check_settlement_contract("NFR-004", "inject unsafe import resources state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "NFR-005: Maintenance resources":
        it "should prove that it compacts one million rows within 10 s and 512 MiB":
            step("Settle compact identifiers")
            step("Drive accepted state and inspect its receipt")
            check_settlement_contract("NFR-005", "drive accepted maintenance resources state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it rebases ten thousand operations within 60 s":
            step("Settle compact identifiers")
            step("Drive the boundary state and inspect preserved invariants")
            check_settlement_contract("NFR-005", "drive boundary maintenance resources state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it fails admission when either maintenance threshold is exceeded":
            step("Settle compact identifiers")
            step("Inject the failure and inspect fail-closed state")
            check_settlement_contract("NFR-005", "inject unsafe maintenance resources state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "NFR-006: Recovery":
        it "should prove that it recovers settlement within ten minutes after dependencies return":
            step("Settle compact identifiers")
            step("Drive accepted state and inspect its receipt")
            check_settlement_contract("NFR-006", "drive accepted recovery state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it applies bounded backpressure while preserving oldest pending work":
            step("Settle compact identifiers")
            step("Drive the boundary state and inspect preserved invariants")
            check_settlement_contract("NFR-006", "drive boundary recovery state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects overflow behavior that discards pending semantic work":
            step("Settle compact identifiers")
            step("Inject the failure and inspect fail-closed state")
            check_settlement_contract("NFR-006", "inject unsafe recovery state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "NFR-007: Exact window":
        it "should prove that it retrieves routine raw observations exactly through day 28":
            step("Retain exact or aggregated history")
            step("Drive accepted state and inspect its receipt")
            check_retention_contract("NFR-007", "drive accepted exact window state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it labels older daily summaries with reducer version and provenance":
            step("Retain exact or aggregated history")
            step("Drive the boundary state and inspect preserved invariants")
            check_retention_contract("NFR-007", "drive boundary exact window state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects early loss or an unversioned aggregate":
            step("Retain exact or aggregated history")
            step("Inject the failure and inspect fail-closed state")
            check_retention_contract("NFR-007", "inject unsafe exact window state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "NFR-008: Archive closure":
        it "should prove that it verifies complete pinned evidence closure before provider expiry":
            step("Retain exact or aggregated history")
            step("Drive accepted state and inspect its receipt")
            check_retention_contract("NFR-008", "drive accepted archive closure state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it hydrates a retained 100 MiB local bundle within 5 s":
            step("Retain exact or aggregated history")
            step("Drive the boundary state and inspect preserved invariants")
            check_retention_contract("NFR-008", "drive boundary archive closure state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it fails a pin with missing digest closure or expired-only location":
            step("Retain exact or aggregated history")
            step("Inject the failure and inspect fail-closed state")
            check_retention_contract("NFR-008", "inject unsafe archive closure state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "NFR-009: Semantic repository growth":
        it "should prove that it measures ten-year packed objects and clone transfer within 2 GiB":
            step("Retain exact or aggregated history")
            step("Drive accepted state and inspect its receipt")
            check_retention_contract("NFR-009", "drive accepted semantic repository growth state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it reports external CAS bytes separately from semantic Git":
            step("Retain exact or aggregated history")
            step("Drive the boundary state and inspect preserved invariants")
            check_retention_contract("NFR-009", "drive boundary semantic repository growth state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it fails admission when either canonical Git measure exceeds 2 GiB":
            step("Retain exact or aggregated history")
            step("Inject the failure and inspect fail-closed state")
            check_retention_contract("NFR-009", "inject unsafe semantic repository growth state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "NFR-010: Integrity":
        it "should prove that it proves zero reuse resurrection inflation loss escalation and secret fields":
            step("Retain exact or aggregated history")
            step("Drive accepted state and inspect its receipt")
            check_retention_contract("NFR-010", "drive accepted integrity state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it verifies every accepted reference receipt and archive digest":
            step("Retain exact or aggregated history")
            step("Drive the boundary state and inspect preserved invariants")
            check_retention_contract("NFR-010", "drive boundary integrity state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it fails on the first integrity violation or incomplete closure":
            step("Retain exact or aggregated history")
            step("Inject the failure and inspect fail-closed state")
            check_retention_contract("NFR-010", "inject unsafe integrity state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "NFR-011: Cryptography agility":
        it "should prove that it verifies algorithm-tagged domain-separated signatures and digests":
            step("Reconcile provider changes")
            step("Drive accepted state and inspect its receipt")
            check_bridge_contract("NFR-011", "drive accepted cryptography agility state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it rotates and revokes keys without changing schema identity":
            step("Reconcile provider changes")
            step("Drive the boundary state and inspect preserved invariants")
            check_bridge_contract("NFR-011", "drive boundary cryptography agility state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects cross-repository namespace epoch or provider replay":
            step("Reconcile provider changes")
            step("Inject the failure and inspect fail-closed state")
            check_bridge_contract("NFR-011", "inject unsafe cryptography agility state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "NFR-012: Least privilege":
        it "should prove that it settles and publishes with scoped credentials outside untrusted steps":
            step("Reconcile provider changes")
            step("Drive accepted state and inspect its receipt")
            check_bridge_contract("NFR-012", "drive accepted least privilege state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it separates authenticated transport identity from operation authority":
            step("Reconcile provider changes")
            step("Drive the boundary state and inspect preserved invariants")
            check_bridge_contract("NFR-012", "drive boundary least privilege state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects credential access or privilege escalation from test payloads":
            step("Reconcile provider changes")
            step("Inject the failure and inspect fail-closed state")
            check_bridge_contract("NFR-012", "inject unsafe least privilege state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "NFR-013: Fail closed":
        it "should prove that it returns typed errors for unsupported unsafe or ambiguous state":
            step("Reconcile provider changes")
            step("Drive accepted state and inspect its receipt")
            check_bridge_contract("NFR-013", "drive accepted fail closed state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it leaves settled identity unpublished after every rejection":
            step("Reconcile provider changes")
            step("Drive the boundary state and inspect preserved invariants")
            check_bridge_contract("NFR-013", "drive boundary fail closed state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects fallback publication on malformed encoding quota or regression":
            step("Reconcile provider changes")
            step("Inject the failure and inspect fail-closed state")
            check_bridge_contract("NFR-013", "inject unsafe fail closed state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "NFR-014: Determinism":
        it "should prove that it matches canonical full and incremental tree digests across hosts":
            step("Create offline semantic changes")
            step("Drive accepted state and inspect its receipt")
            check_replica_contract("NFR-014", "drive accepted determinism state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it repeats equivalent accepted logs with stable ordering":
            step("Create offline semantic changes")
            step("Drive the boundary state and inspect preserved invariants")
            check_replica_contract("NFR-014", "drive boundary determinism state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it fails when host order or execution path changes canonical output":
            step("Create offline semantic changes")
            step("Inject the failure and inspect fail-closed state")
            check_replica_contract("NFR-014", "inject unsafe determinism state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")

    describe "NFR-015: Portability":
        it "should prove that it runs one pure semantic core through all capability fixtures":
            step("Create offline semantic changes")
            step("Drive accepted state and inspect its receipt")
            check_replica_contract("NFR-015", "drive accepted portability state; inspect canonical state and durable receipt", "fixture -> production owner -> committed/read-back receipt -> oracle")

        it "should prove that it keeps subprocess network OS and runtime code in adapters":
            step("Create offline semantic changes")
            step("Drive the boundary state and inspect preserved invariants")
            check_replica_contract("NFR-015", "drive boundary portability state; inspect identity, provenance, and unchanged invariants", "fixture -> boundary transition -> durable receipt -> boundary oracle")

        it "should prove that it rejects forbidden provider SDK or raw runtime dependency in the core":
            step("Create offline semantic changes")
            step("Inject the failure and inspect fail-closed state")
            check_replica_contract("NFR-015", "inject unsafe portability state; prove typed rejection and no forbidden mutation", "fixture -> fault injection -> typed error -> unchanged canonical state")
```

</details>
