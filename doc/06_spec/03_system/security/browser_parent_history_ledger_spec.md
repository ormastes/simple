# Capability-bound parent browser history

> Proves the real SBR2/nested-SBRF9 decode and parent frame-accept boundary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Capability-bound parent browser history

Proves the real SBR2/nested-SBRF9 decode and parent frame-accept boundary.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Security |
| Status | Active |
| Source | `test/03_system/security/browser_parent_history_ledger_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves the real SBR2/nested-SBRF9 decode and parent frame-accept boundary.
The renderer can propose a complete bounded ledger, but only the parent can
validate and atomically publish it. Static source evidence is not an executed
browser claim until the admitted pure-Simple runner executes this scenario.

## Scenarios

### Capability-bound parent browser history

#### should publish only one complete parent-authorized ledger

- should publish only one complete parent-authorized ledger
   - Protocol capture: after_step
- Stage parent history authority
   - Protocol capture: after_step
   - Evidence: protocol response verified by 3 expected checks
   - Expected: empty_decoded.url_kind equals `V`
   - Expected: empty_decoded.raw_url equals ``
   - Expected: decoded_navigation.status equals `message`
- Accept one capability-bound history proposal
   - Protocol capture: after_step
- Reject hostile or stale history proposals
   - Protocol capture: after_step
- Preserve chrome across renderer failure
   - Protocol capture: after_step
   - Evidence: protocol response verified by 3 expected checks
   - Expected: hostile.state equals `failed`
   - Expected: hostile.home_url equals `https://history.test/home`
   - Expected: hostile.document_title equals `History application`


<details>
<summary>Executable SSpec</summary>

Runnable source: 140 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should publish only one complete parent-authorized ledger")
step("Stage parent history authority")
var staged = make_history_process_fixture()
val capability = _history_capability()
val current = staged.document_url
val explicit_empty = browser_renderer_history_proposal_encode(
    "P", "V", "", current, capability, 2,
    [staged.history_urls[0], current, current]
)
expect(explicit_empty.is_ok()).to_be(true)
val empty_decoded = browser_renderer_history_proposal_decode(
    explicit_empty.unwrap()
)
expect(empty_decoded.url_kind).to_equal("V")
expect(empty_decoded.raw_url).to_equal("")
expect(empty_decoded.resolved_url).to_equal(
    "https://history.test/app?q=1#kept"
)
val snapshot_wire = staged._history_snapshot_for_command(capability)
expect(snapshot_wire.is_ok()).to_be(true)
val navigation = browser_renderer_navigation_encode_with_history(
    7, 41, "back", staged.history_back_url,
    "GET", "", "", "", snapshot_wire.unwrap()
)
val outer_navigation = browser_renderer_capability_bind_encoded(
    navigation, 7, 41, 41, capability
)
expect(outer_navigation.ok).to_be(true)
val decoded_navigation = browser_renderer_capability_decoder_feed(
    browser_renderer_capability_decoder_new(7),
    outer_navigation.wire
)
expect(decoded_navigation.status).to_equal("message")
val joined = browser_renderer_navigation_decode(
    browser_renderer_capability_payload_message(
        decoded_navigation.message
    )
)
expect(joined.ok).to_be(true)
expect(browser_renderer_history_proposal_decode(
    joined.history_snapshot
).authority_capability).to_equal(capability)

step("Accept one capability-bound history proposal")
var accepted = make_history_process_fixture()
val next_url = "https://history.test/next#view"
val proposal = browser_renderer_history_proposal_encode(
    "P", "V", "/next#view", next_url, capability, 2,
    [accepted.history_urls[0], accepted.history_urls[1], next_url]
)
expect(proposal.is_ok()).to_be(true)
val accepted_frame = _history_frame(
    accepted, proposal.unwrap(), next_url
)
_admit_history_frame(accepted, accepted_frame)
val accepted_result = accepted._accept_decoded_frame(
    accepted_frame.frame, accepted_frame.envelope.generation
)
expect(accepted_result.ok).to_be(true)
expect_history_public_state(
    accepted, next_url,
    "https://history.test/app?q=1#kept", "", 3, 2
)

step("Reject hostile or stale history proposals")
var hostile = make_history_process_fixture()
val hostile_proposal = browser_renderer_history_proposal_encode(
    "P", "V", "/next#view", next_url,
    "22222222222222222222222222222222", 2,
    [hostile.history_urls[0], hostile.history_urls[1], next_url]
)
expect(hostile_proposal.is_ok()).to_be(true)
val hostile_frame = _history_frame(
    hostile, hostile_proposal.unwrap(), next_url
)
_admit_history_frame(hostile, hostile_frame)
val hostile_result = hostile._accept_decoded_frame(
    hostile_frame.frame, hostile_frame.envelope.generation
)
expect(hostile_result.ok).to_be(false)
expect_history_public_state(
    hostile, "https://history.test/app?q=1#kept",
    "https://history.test/start", "", 2, 1
)

var stale = make_history_process_fixture()
stale.expected_reply_to_request_id = 40
val stale_frame = _history_frame(
    stale, proposal.unwrap(), next_url
)
_admit_history_frame(stale, stale_frame)
expect(stale._accept_decoded_frame(
    stale_frame.frame, stale_frame.envelope.generation
).ok).to_be(false)

var denied = make_history_process_fixture()
denied.document_csp_policy = "sandbox"
denied.history_csp_policies[1] = "sandbox"
val denied_proposal = browser_renderer_history_proposal_encode(
    "P", "V", "/next#view", next_url, capability, 2,
    [denied.history_urls[0], denied.history_urls[1], next_url]
)
val denied_frame = _history_frame(
    denied, denied_proposal.unwrap(), next_url
)
_admit_history_frame(denied, denied_frame)
expect(denied._accept_decoded_frame(
    denied_frame.frame, denied_frame.envelope.generation
).ok).to_be(false)

var wrong_url = make_history_process_fixture()
val wrong_frame = _history_frame(
    wrong_url, proposal.unwrap(),
    "https://history.test/wrong"
)
_admit_history_frame(wrong_url, wrong_frame)
expect(wrong_url._accept_decoded_frame(
    wrong_frame.frame, wrong_frame.envelope.generation
).ok).to_be(false)

var overflow = make_history_process_fixture()
val overflow_frame = _history_frame(
    overflow,
    "SBRHJ1\tP\tV\t0\t65\t-\t-\t-",
    overflow.document_url
)
_admit_history_frame(overflow, overflow_frame)
expect(overflow._accept_decoded_frame(
    overflow_frame.frame, overflow_frame.envelope.generation
).ok).to_be(false)

step("Preserve chrome across renderer failure")
expect(hostile.state).to_equal("failed")
expect(hostile.home_url).to_equal("https://history.test/home")
expect(hostile.document_title).to_equal("History application")
expect_history_public_state(
    hostile, "https://history.test/app?q=1#kept",
    "https://history.test/start", "", 2, 1
)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-BROWSER-009`
- `REQ-WEB-BROWSER-012`
- `REQ-WEB-BROWSER-014`
- `REQ-WEB-BROWSER-017`
- `REQ-WEB-BROWSER-021`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7ad229b88148eaf755408532259263378f6d809b2a1b722f31a146c7c473c33d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7ad229b88148eaf755408532259263378f6d809b2a1b722f31a146c7c473c33d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7ad229b88148eaf755408532259263378f6d809b2a1b722f31a146c7c473c33d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/security/browser_parent_history_ledger_spec.spl
mirror: doc/06_spec/03_system/security/browser_parent_history_ledger_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=95 oracle=100
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/03_system/security/browser_parent_history_ledger_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/security/browser_parent_history_ledger_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/security/browser_parent_history_ledger_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 5 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/security/browser_parent_history_ledger_spec.spl:139:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should publish only one complete parent-authorized ledger' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/security/browser_parent_history_ledger_spec.spl:139:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should publish only one complete parent-authorized ledger' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
