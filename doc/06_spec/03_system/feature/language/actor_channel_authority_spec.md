# Scheduler-owned actor channel authority

> This system specification exercises the public scalar-text actor compatibility

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scheduler-owned actor channel authority

This system specification exercises the public scalar-text actor compatibility

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/language/actor_channel_authority_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This system specification exercises the public scalar-text actor compatibility
surface through one explicit scheduler owner. It proves finite mailbox and
reply admission, admission-time argument copying, copied-reference routing,
and one terminal scheduler removal. It does not claim cross-thread ActorRef
safety, typed heap payload transport, or C/interpreter provider parity.

Run only with an admitted pure-Simple Stage-4 test surface:

    SIMPLE_LIB=src bin/release/simple test test/03_system/feature/language/actor_channel_authority_spec.spl --mode=native

The Rust bootstrap seed is not acceptance evidence.

## Scenarios

### scheduler-owned actor channel authority

#### should preserve bounded copied-reference authority through terminal stop

- should preserve bounded copied-reference authority through terminal stop
- Create one scheduler-owned bounded actor channel
   - Expected: scheduler.reply_capacity() equals `1`
- Admit copied arguments through one actor reference
   - Expected: copied.has_messages() is true
- Observe finite mailbox and reply backpressure
   - Expected: copied.send("echo", ["mailbox-full"]) is false
   - Expected: copied.ask("echo", ["reply-full"]) equals `-1`
   - Expected: scheduler.outstanding_reply_count() equals `1`
   - Expected: mailbox.pending_high_water_count() equals `1`
- Dispatch and consume the isolated result
   - Expected: reply equals `before`
   - Expected: scheduler.outstanding_reply_count() equals `0`
   - Expected: copied.has_messages() is false
- Stop once through the owning scheduler
   - Expected: first_stop is true
   - Expected: second_stop is false
   - Expected: late_send is false
   - Expected: late_ask equals `-1`
   - Expected: original.has_messages() is false
   - Expected: comparison.status equals `EvidenceStatus.passed`
   - Expected: comparison.summary equals `8 check(s) passed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 75 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve bounded copied-reference authority through terminal stop")
step("Create one scheduler-owned bounded actor channel")
val scheduler = ActorScheduler.with_reply_capacity(1)
val mailbox = ActorMailbox.new(1)
val original = actor_ref_with_authority(scheduler, mailbox)
val copied = original
expect(original.get_id()).to_be_greater_than(0)
expect(scheduler.reply_capacity()).to_equal(1)

step("Admit copied arguments through one actor reference")
var args = ["before"]
val reply_id = original.ask("echo", args)
expect(reply_id).to_be_greater_than(0)
args[0] = "after"
expect(copied.has_messages()).to_equal(true)

step("Observe finite mailbox and reply backpressure")
expect(copied.send("echo", ["mailbox-full"])).to_equal(false)
expect(copied.ask("echo", ["reply-full"])).to_equal(-1)
expect(scheduler.outstanding_reply_count()).to_equal(1)
expect(mailbox.pending_high_water_count()).to_equal(1)

step("Dispatch and consume the isolated result")
scheduler.run_until_idle()
var observed_reply = "missing"
if val reply = scheduler.consume_reply(reply_id):
    observed_reply = reply
    expect(reply).to_equal("before")
else:
    fail("the admitted actor reply must remain available")
expect(scheduler.outstanding_reply_count()).to_equal(0)
expect(copied.has_messages()).to_equal(false)

step("Stop once through the owning scheduler")
val first_stop = copied.stop()
val second_stop = original.stop()
val late_send = original.send("echo", ["late"])
val late_ask = copied.ask("echo", ["late"])
expect(first_stop).to_equal(true)
expect(second_stop).to_equal(false)
expect(late_send).to_equal(false)
expect(late_ask).to_equal(-1)
expect(original.has_messages()).to_equal(false)

val evidence = canonical_evidence(
    "protocol",
    "actor-channel-authority/v1",
    [
        evidence_node("mailbox.high_water", "{mailbox.pending_high_water_count()}"),
        evidence_node("reply.capacity", "{scheduler.reply_capacity()}"),
        evidence_node("reply.value", observed_reply),
        evidence_node("reply.outstanding_after_consume", "{scheduler.outstanding_reply_count()}"),
        evidence_node("lifecycle.first_stop", "{first_stop}"),
        evidence_node("lifecycle.second_stop", "{second_stop}"),
        evidence_node("lifecycle.late_send", "{late_send}"),
        evidence_node("lifecycle.late_ask", "{late_ask}")
    ]
)
val oracle = oracle_spec(
    "actor-channel-authority/v1",
    [
        check_exact("mailbox.high_water", "1"),
        check_exact("reply.capacity", "1"),
        check_exact("reply.value", "before"),
        check_exact("reply.outstanding_after_consume", "0"),
        check_exact("lifecycle.first_stop", "true"),
        check_exact("lifecycle.second_stop", "false"),
        check_exact("lifecycle.late_send", "false"),
        check_exact("lifecycle.late_ask", "-1")
    ]
)
val comparison = compare_evidence(evidence, oracle)
expect(comparison.status).to_equal(EvidenceStatus.passed)
expect(comparison.summary).to_equal("8 check(s) passed")
```

</details>

<details>
<summary>Advanced: should reject an unknown actor without publishing work or reply credit</summary>

#### should reject an unknown actor without publishing work or reply credit

- should reject an unknown actor without publishing work or reply credit
- Create an actor reference whose ID is absent from the scheduler
- Reject every operation at the scheduler-owned registry boundary
   - Expected: unknown.send("echo", ["unknown"]) is false
   - Expected: unknown.ask("echo", ["unknown"]) equals `-1`
   - Expected: unknown.has_messages() is false
   - Expected: unknown.stop() is false
   - Expected: scheduler.outstanding_reply_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject an unknown actor without publishing work or reply credit")
step("Create an actor reference whose ID is absent from the scheduler")
val scheduler = ActorScheduler.with_reply_capacity(1)
val unknown = ActorRef(actor_id: 999999, _scheduler: scheduler)

step("Reject every operation at the scheduler-owned registry boundary")
expect(unknown.send("echo", ["unknown"])).to_equal(false)
expect(unknown.ask("echo", ["unknown"])).to_equal(-1)
expect(unknown.has_messages()).to_equal(false)
expect(unknown.stop()).to_equal(false)
expect(scheduler.outstanding_reply_count()).to_equal(0)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-PAR-002`
- `REQ-PAR-006`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e230be279fe9a8eab0271fc8cd7104ce51a207f77c26359a19e30eafd4a6adc7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e230be279fe9a8eab0271fc8cd7104ce51a207f77c26359a19e30eafd4a6adc7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e230be279fe9a8eab0271fc8cd7104ce51a207f77c26359a19e30eafd4a6adc7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/feature/language/actor_channel_authority_spec.spl
mirror: doc/06_spec/03_system/feature/language/actor_channel_authority_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=90 oracle=70
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/feature/language/actor_channel_authority_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/language/actor_channel_authority_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/language/actor_channel_authority_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/language/actor_channel_authority_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/feature/language/actor_channel_authority_spec.spl:54:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve bounded copied-reference authority through terminal stop' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/language/actor_channel_authority_spec.spl:132:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject an unknown actor without publishing work or reply credit' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/language/actor_channel_authority_spec.spl:132:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject an unknown actor without publishing work or reply credit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
