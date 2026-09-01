# log_text_dispatch_spec

> log-lib-drivers Phase 5 regression spec — log_dispatch_text() text correlation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# log_text_dispatch_spec

log-lib-drivers Phase 5 regression spec — log_dispatch_text() text correlation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/log_text_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

log-lib-drivers Phase 5 regression spec — log_dispatch_text() text correlation.

Bug (Batch D, lane DS4): log_dispatch_text() — used by log_trace_subsys/debug/info/
warn/error/fatal — called `_dispatch_to_backends(level, subsys, 0)` with a
dummy p0=0. The actual message text never reached ring backends; only
log_dispatch_record() (the structured/numeric p0-p1 path) carried a real
payload. This spec proves the dispatched backend record now correlates back
to the real message via the text-intern handle carried in p0.

## Scenarios

### log facade — log_dispatch_text() text correlation (bug fix)

#### log_info_subsys's message is retrievable from the dispatched ring record

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- log_info_subsys's message is retrievable from the dispatched ring record
   - Expected: ring_backend_count(sink) equals `1`
   - Expected: recovered equals `hello-from-log-info`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("log_info_subsys's message is retrievable from the dispatched ring record")
log_set_level(LOG_INFO)
val sink = ring_backend_new(64)
val id = log_register_backend(sink.ops)
ring_backend_clear(sink)
log_info_subsys(SUBSYS_KERN, "hello-from-log-info")
expect(ring_backend_count(sink)).to_equal(1)
val handle = ring_backend_seq_at(sink, 0)
val recovered = log_text_from_handle(handle)
expect(recovered).to_equal("hello-from-log-info")
log_remove_backend(id)
```

</details>

#### two distinct messages correlate to two distinct, correctly-ordered handles

- two distinct messages correlate to two distinct, correctly-ordered handles
   - Expected: ring_backend_count(sink) equals `2`
   - Expected: log_text_from_handle(h0) equals `first-message`
   - Expected: log_text_from_handle(h1) equals `second-message`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("two distinct messages correlate to two distinct, correctly-ordered handles")
log_set_level(LOG_INFO)
val sink = ring_backend_new(64)
val id = log_register_backend(sink.ops)
ring_backend_clear(sink)
log_info_subsys(SUBSYS_KERN, "first-message")
log_info_subsys(SUBSYS_KERN, "second-message")
expect(ring_backend_count(sink)).to_equal(2)
val h0 = ring_backend_seq_at(sink, 0)
val h1 = ring_backend_seq_at(sink, 1)
expect(log_text_from_handle(h0)).to_equal("first-message")
expect(log_text_from_handle(h1)).to_equal("second-message")
log_remove_backend(id)
```

</details>

#### an out-of-range or never-issued handle resolves to empty, not garbage

- an out-of-range or never-issued handle resolves to empty, not garbage
   - Expected: log_text_from_handle(0) equals ``
   - Expected: log_text_from_handle(-1) equals ``
   - Expected: log_text_from_handle(999999999) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("an out-of-range or never-issued handle resolves to empty, not garbage")
expect(log_text_from_handle(0)).to_equal("")
expect(log_text_from_handle(-1)).to_equal("")
expect(log_text_from_handle(999999999)).to_equal("")
```

</details>

#### the text table wraps instead of going permanently text-blind

- the text table wraps instead of going permanently text-blind
   - Expected: log_text_from_handle(handle) equals `after-wrap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("the text table wraps instead of going permanently text-blind")
# The pre-review implementation stopped storing after
# LOG_TEXT_INTERN_CAP messages, so every later log line lost its text
# forever. Logging past the cap must still resolve the newest message.
log_set_level(LOG_INFO)
val sink = ring_backend_new(4)
val id = log_register_backend(sink.ops)
var i = 0
while i < LOG_TEXT_INTERN_CAP + 8:
    log_info_subsys(SUBSYS_KERN, "filler")
    i = i + 1
ring_backend_clear(sink)
log_info_subsys(SUBSYS_KERN, "after-wrap")
val handle = ring_backend_seq_at(sink, 0)
expect(log_text_from_handle(handle)).to_equal("after-wrap")
assert_true(log_text_intern_overwritten() > 0)
log_remove_backend(id)
```

</details>

#### a handle whose slot was overwritten resolves to empty, not a later message

- a handle whose slot was overwritten resolves to empty, not a later message
   - Expected: log_text_from_handle(stale) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a handle whose slot was overwritten resolves to empty, not a later message")
log_set_level(LOG_INFO)
val sink = ring_backend_new(4)
val id = log_register_backend(sink.ops)
ring_backend_clear(sink)
log_info_subsys(SUBSYS_KERN, "doomed-message")
val stale = ring_backend_seq_at(sink, 0)
var i = 0
while i < LOG_TEXT_INTERN_CAP + 1:
    log_info_subsys(SUBSYS_KERN, "overwriter")
    i = i + 1
expect(log_text_from_handle(stale)).to_equal("")
log_remove_backend(id)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ac6f9bdfe225af91d83c88595aa5f91dc5fc56359963071c93654629f41e900c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ac6f9bdfe225af91d83c88595aa5f91dc5fc56359963071c93654629f41e900c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ac6f9bdfe225af91d83c88595aa5f91dc5fc56359963071c93654629f41e900c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/log_text_dispatch_spec.spl
mirror: doc/06_spec/01_unit/lib/log_text_dispatch_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/log_text_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/log_text_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/log_text_dispatch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/log_text_dispatch_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'log_info_subsys's message is retrievable from the dispatched ring record' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/log_text_dispatch_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'two distinct messages correlate to two distinct, correctly-ordered handles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/log_text_dispatch_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an out-of-range or never-issued handle resolves to empty, not garbage' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
