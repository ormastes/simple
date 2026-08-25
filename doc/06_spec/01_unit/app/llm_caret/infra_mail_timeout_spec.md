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
| Updated | 2026-08-25 |
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

- Start a listener that never answers and point [mail] at it with a 2 s budget
   - Expected: mail_read_timeout_ms() equals `BUDGET_MS`
- mail_list connects, waits for the IMAP greeting, and gives up
   - Expected: ok is false
   - Expected: err equals `mail server timed out after 2000 ms`
- Wall time stays under 5 s (budget 2 s plus connect/setup)


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Resetting to 0 restores the production default
   - Expected: mail_read_timeout_ms() equals `15000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
