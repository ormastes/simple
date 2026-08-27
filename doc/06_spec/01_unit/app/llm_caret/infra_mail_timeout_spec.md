# infra_mail_timeout_spec

> Bounded mail server reads for the LLM Caret mail tools.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# infra_mail_timeout_spec

Bounded mail server reads for the LLM Caret mail tools.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/infra_mail_timeout_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Bounded mail server reads for the LLM Caret mail tools.

Who: the caret user whose `mail_list` / `mail_read` / `mail_send` call hits
a server that accepts the TCP connection and then never speaks. Why: before
this change the read loop had no deadline, so one stalled server hung the
whole tool call (and the caret turn) forever. Every tool must now fail with
"mail server timed out after N ms" inside the configured budget.

Fixture: an in-process listener bound to 127.0.0.1:0 that is never accepted
from. The kernel completes the handshake from the backlog, so the client
connects successfully and then waits for a greeting that never comes.

## Scenarios

### mail tools against a server that accepts and never replies

#### mail_list fails with the timeout error inside the budget instead of hanging

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- mail_list fails with the timeout error inside the budget instead of hanging
- Start a listener that never answers and point [mail] at it with a 2 s budget
   - Expected: mail_read_timeout_ms() equals `BUDGET_MS`
- mail_list connects, waits for the IMAP greeting, and gives up
   - Expected: ok is false
   - Expected: err equals `mail server timed out after 2000 ms`
- Wall time stays under 5 s (budget 2 s plus connect/setup)


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("mail_list fails with the timeout error inside the budget instead of hanging")
step("Start a listener that never answers and point [mail] at it with a 2 s budget")
val addr = silent_server_addr()
configure(addr)
expect(mail_read_timeout_ms()).to_equal(BUDGET_MS)
step("mail_list connects, waits for the IMAP greeting, and gives up")
val t0 = current_time_ms()
val (ok, err) = mail_list("INBOX", 5)
val elapsed = current_time_ms() - t0
expect(ok).to_equal(false)
expect(err).to_equal("mail server timed out after 2000 ms")
step("Wall time stays under 5 s (budget 2 s plus connect/setup)")
expect(elapsed).to_be_less_than(WALL_LIMIT_MS)
expect(elapsed).to_be_greater_than(BUDGET_MS - 200)
reset_config()
```

</details>

#### mail_read reports the same timeout (sibling path: UID FETCH session)

- mail_read reports the same timeout (sibling path: UID FETCH session)
   - Expected: ok is false
   - Expected: err equals `mail server timed out after 2000 ms`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("mail_read reports the same timeout (sibling path: UID FETCH session)")
val addr = silent_server_addr()
configure(addr)
val t0 = current_time_ms()
val (ok, err) = mail_read("42")
val elapsed = current_time_ms() - t0
expect(ok).to_equal(false)
expect(err).to_equal("mail server timed out after 2000 ms")
expect(elapsed).to_be_less_than(WALL_LIMIT_MS)
reset_config()
```

</details>

#### mail_send reports the timeout while waiting for the SMTP greeting

- mail_send reports the timeout while waiting for the SMTP greeting
   - Expected: ok is false
   - Expected: err equals `mail server timed out after 2000 ms`
- Resetting to 0 restores the production default
   - Expected: mail_read_timeout_ms() equals `15000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("mail_send reports the timeout while waiting for the SMTP greeting")
val addr = silent_server_addr()
configure(addr)
val t0 = current_time_ms()
val (ok, err) = mail_send("to@example.test", "subject", "body")
val elapsed = current_time_ms() - t0
expect(ok).to_equal(false)
expect(err).to_equal("mail server timed out after 2000 ms")
expect(elapsed).to_be_less_than(WALL_LIMIT_MS)
reset_config()
mail_set_read_timeout_ms(0)
step("Resetting to 0 restores the production default")
expect(mail_read_timeout_ms()).to_equal(15000)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LLM-CARET-MAIL-TIMEOUT`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b54f43ad343f9fa2245787fae4337cb4cd6af048cf644e888c7782c1556d6916`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b54f43ad343f9fa2245787fae4337cb4cd6af048cf644e888c7782c1556d6916`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b54f43ad343f9fa2245787fae4337cb4cd6af048cf644e888c7782c1556d6916`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/infra_mail_timeout_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/infra_mail_timeout_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/infra_mail_timeout_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/infra_mail_timeout_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/infra_mail_timeout_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/infra_mail_timeout_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/infra_mail_timeout_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mail_list fails with the timeout error inside the budget instead of hanging' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/infra_mail_timeout_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mail_read reports the same timeout (sibling path: UID FETCH session)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/infra_mail_timeout_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mail_send reports the timeout while waiting for the SMTP greeting' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
