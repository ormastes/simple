# Provider Generation Quarantine Specification

> Tests covering SPipe provider generation quarantine.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Provider Generation Quarantine Specification

## Scenarios

### SPipe provider generation quarantine

#### precommits restart denial before another lifecycle quarantine CAS

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- precommits restart denial before another lifecycle quarantine CAS


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("precommits restart denial before another lifecycle quarantine CAS")
val generation = 1
val marker = "/tmp/simple-spipe-provider-precommit-order.marker"
val inner = fresh_store("/tmp/simple-spipe-provider-precommit-order",
    marker)
val store = TombstonePrecommitOrderLifecycleV1(inner: inner,
    violation_marker: marker, provider_generation: generation)
var service = SpipeProviderServiceV1.configured(
    PureEd25519ReceiptAuthorityV1.test_only(quarantine_seed(),
        "AUTH-PRECOMMIT", generation).unwrap(), store).unwrap()
service = dispatch(service, initialized_frame("init-precommit"),
    generation).service
val applied = apply_empty(service, "apply-precommit", generation)
service = applied.service
val candidate_uid = result_text(response_payload(applied),
    "candidate_uid")
val candidate_root = result_text(response_payload(applied),
    "candidate_logical_root")
val payload = publish_payload("publish-precommit", candidate_uid,
    candidate_root)
val published = dispatch(service, bound_frame(
    "request-publish-precommit", "index_publish", payload,
    generation), generation)
val first = response_payload(published)
expect(first).to_contain("\"code\":\"fatal_provider_error\"")
expect(file_exists(marker)).to_be(false)
expect(inner.load_generation_quarantine(generation).unwrap()).to_contain(
    "\"schema\":\"spipe-provider-generation-quarantine-v1\"")
expect(inner.load().unwrap()).to_contain("\"state\":\"staged\"")
var restarted = SpipeProviderServiceV1.configured(
    PureEd25519ReceiptAuthorityV1.test_only(quarantine_seed(),
        "AUTH-PRECOMMIT", generation).unwrap(), inner).unwrap()
restarted = dispatch(restarted, initialized_frame("init-precommit-restart"),
    generation).service
expect(response_payload(dispatch(restarted, bound_frame(
    "request-publish-precommit", "index_publish", payload,
    generation), generation))).to_equal(first)
```

</details>

#### returns the exact lifecycle winner that linearized before generation close

- returns the exact lifecycle winner that linearized before generation close
   - Expected: response_payload(replayed) equals `first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the exact lifecycle winner that linearized before generation close")
val generation = 17
val staged_etag = "/tmp/simple-spipe-provider-close-race.etag"
val staged_state = "/tmp/simple-spipe-provider-close-race.state"
file_delete(staged_etag)
file_delete(staged_state)
val inner = fresh_store("/tmp/simple-spipe-provider-close-race",
    "/tmp/simple-spipe-provider-close-race.marker")
val store = LifecycleWinnerBeforeCloseV1(inner: inner,
    staged_etag_path: staged_etag, staged_state_path: staged_state)
var service = SpipeProviderServiceV1.configured(
    PureEd25519ReceiptAuthorityV1.test_only(quarantine_seed(),
        "AUTH-CLOSE-RACE", generation).unwrap(), store).unwrap()
service = dispatch(service, initialized_frame("init-close-race"),
    generation).service
val applied = apply_empty(service, "apply-close-race", generation)
service = applied.service
val candidate_uid = result_text(response_payload(applied),
    "candidate_uid")
val candidate_root = result_text(response_payload(applied),
    "candidate_logical_root")
val payload = publish_payload("publish-close-race", candidate_uid,
    candidate_root)
val published = dispatch(service, bound_frame(
    "request-publish-close-race", "index_publish", payload,
    generation), generation)
val first = response_payload(published)
expect(first).to_contain("\"status\":\"published\"")
expect(inner.load().unwrap()).to_contain("\"state\":\"published\"")
expect(inner.load_generation_quarantine(generation).unwrap()).to_contain(
    "\"schema\":\"spipe-provider-generation-quarantine-v1\"")
var restarted = SpipeProviderServiceV1.configured(
    PureEd25519ReceiptAuthorityV1.test_only(quarantine_seed(),
        "AUTH-CLOSE-RACE", generation).unwrap(), inner).unwrap()
restarted = dispatch(restarted,
    initialized_frame("init-close-race-restart"), generation).service
val replayed = dispatch(restarted, bound_frame(
    "request-publish-close-race", "index_publish", payload,
    generation), generation)
expect(response_payload(replayed)).to_equal(first)
```

</details>

#### persists generation closure through lifecycle contention and restart

- persists generation closure through lifecycle contention and restart
   - Expected: service.state.provider_generation equals `generation`
   - Expected: response_payload(replayed) equals `first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 61 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("persists generation closure through lifecycle contention and restart")
val generation = 9
val marker = "/tmp/simple-spipe-provider-generation-quarantine.marker"
val inner = fresh_store("/tmp/simple-spipe-provider-generation-quarantine",
    marker)
val store = QuarantineConflictLifecycleV1(inner: inner,
    marker_path: marker)
var service = SpipeProviderServiceV1.configured(
    PureEd25519ReceiptAuthorityV1.test_only(quarantine_seed(),
        "AUTH-QUARANTINE", generation).unwrap(), store).unwrap()
service = dispatch(service, initialized_frame("init-quarantine"),
    generation).service
expect(service.state.provider_generation).to_equal(generation)
val applied = apply_empty(service, "apply-quarantine", generation)
service = applied.service
val apply_response = response_payload(applied)
val candidate_uid = result_text(apply_response, "candidate_uid")
val candidate_root = result_text(apply_response,
    "candidate_logical_root")
# This process loaded the still-open generation before another
# process wins the generation-close tombstone.
var stale_writer = SpipeProviderServiceV1.configured(
    PureEd25519ReceiptAuthorityV1.test_only(quarantine_seed(),
        "AUTH-QUARANTINE", generation).unwrap(), inner).unwrap()
stale_writer = dispatch(stale_writer,
    initialized_frame("init-stale-writer"), generation).service
val payload = publish_payload("publish-quarantine", candidate_uid,
    candidate_root)
val published = dispatch(service, bound_frame("request-publish-quarantine",
    "index_publish", payload, generation), generation)
service = published.service
val first = response_payload(published)
expect(first).to_contain("\"code\":\"fatal_provider_error\"")
expect(first).to_contain("provider generation closed")
expect(service.state.generation_quarantined).to_be(true)
expect(service.state.request_allowed()).to_be(false)
expect(inner.load().unwrap()).to_contain("\"state\":\"staged\"")
val denied = apply_empty(service, "apply-after-quarantine", generation)
expect(response_payload(denied)).to_contain(
    "\"code\":\"fatal_provider_error\"")
var restarted = SpipeProviderServiceV1.configured(
    PureEd25519ReceiptAuthorityV1.test_only(quarantine_seed(),
        "AUTH-QUARANTINE", generation).unwrap(), inner).unwrap()
restarted = dispatch(restarted, initialized_frame("init-restart"),
    generation).service
expect(restarted.state.generation_quarantined).to_be(true)
val replayed = dispatch(restarted,
    bound_frame("request-publish-quarantine", "index_publish", payload,
        generation), generation)
expect(response_payload(replayed)).to_equal(first)
val stale_payload = publish_payload("publish-stale-writer",
    candidate_uid, candidate_root)
val stale_result = dispatch(stale_writer, bound_frame(
    "request-publish-stale-writer", "index_publish", stale_payload,
    generation), generation)
val stale_response = response_payload(stale_result)
expect(stale_response).to_contain("\"code\":\"fatal_provider_error\"")
expect(response_payload(dispatch(restarted, bound_frame(
    "request-publish-stale-writer", "index_publish", stale_payload,
    generation), generation))).to_equal(stale_response)
```

</details>

#### retries terminal loser journaling until the exact response is durable

- retries terminal loser journaling until the exact response is durable
   - Expected: response_payload(replayed) equals `loser_response`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retries terminal loser journaling until the exact response is durable")
val generation = 13
val marker = "/tmp/simple-spipe-provider-terminal-journal.marker"
val inner = fresh_store("/tmp/simple-spipe-provider-terminal-journal",
    marker)
var service = SpipeProviderServiceV1.configured(
    PureEd25519ReceiptAuthorityV1.test_only(quarantine_seed(),
        "AUTH-JOURNAL", generation).unwrap(), inner).unwrap()
service = dispatch(service, initialized_frame("init-journal"),
    generation).service
val applied = apply_empty(service, "apply-journal", generation)
service = applied.service
val candidate_uid = result_text(response_payload(applied),
    "candidate_uid")
val candidate_root = result_text(response_payload(applied),
    "candidate_logical_root")
val winner_payload = publish_payload("publish-winner", candidate_uid,
    candidate_root)
service = dispatch(service, bound_frame("request-publish-winner",
    "index_publish", winner_payload, generation), generation).service
var contender = SpipeProviderServiceV1.configured(
    PureEd25519ReceiptAuthorityV1.test_only(quarantine_seed(),
        "AUTH-JOURNAL", generation).unwrap(),
    TerminalJournalConflictLifecycleV1(inner: inner,
        marker_path: marker)).unwrap()
contender = dispatch(contender, initialized_frame("init-contender"),
    generation).service
val loser_payload = publish_payload("publish-loser", candidate_uid,
    candidate_root)
val loser = dispatch(contender, bound_frame("request-publish-loser",
    "index_publish", loser_payload, generation), generation)
val loser_response = response_payload(loser)
expect(loser_response).to_contain("\"code\":\"stale_base\"")
expect(inner.load().unwrap()).to_contain("publish-loser")
val replayed = dispatch(loser.service,
    bound_frame("request-publish-loser", "index_publish", loser_payload,
        generation), generation)
expect(response_payload(replayed)).to_equal(loser_response)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/spipe_knowledge_provider/provider_generation_quarantine_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SPipe provider generation quarantine.
- SPipe provider generation quarantine

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8d9a5f5809ae2eb84a4cd0dd7bac53e2ec8822906376d08d73d9a0d7c1a3a32e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8d9a5f5809ae2eb84a4cd0dd7bac53e2ec8822906376d08d73d9a0d7c1a3a32e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8d9a5f5809ae2eb84a4cd0dd7bac53e2ec8822906376d08d73d9a0d7c1a3a32e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/spipe_knowledge_provider/provider_generation_quarantine_spec.spl
mirror: doc/06_spec/01_unit/app/spipe_knowledge_provider/provider_generation_quarantine_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/spipe_knowledge_provider/provider_generation_quarantine_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/spipe_knowledge_provider/provider_generation_quarantine_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/spipe_knowledge_provider/provider_generation_quarantine_spec.spl:175:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'precommits restart denial before another lifecycle quarantine CAS' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spipe_knowledge_provider/provider_generation_quarantine_spec.spl:215:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the exact lifecycle winner that linearized before generation close' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spipe_knowledge_provider/provider_generation_quarantine_spec.spl:258:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'persists generation closure through lifecycle contention and restart' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
