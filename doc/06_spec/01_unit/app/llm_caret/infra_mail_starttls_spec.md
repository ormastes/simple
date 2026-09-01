# infra_mail_starttls_spec

> STARTTLS negotiation for the LLM Caret mail tools, proven against scripted

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# infra_mail_starttls_spec

STARTTLS negotiation for the LLM Caret mail tools, proven against scripted

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/infra_mail_starttls_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

STARTTLS negotiation for the LLM Caret mail tools, proven against scripted
server transcripts (no TLS server, no network).

Who: an operator pointing `[mail]` at SMTP submission (587) or IMAP with
STARTTLS (143). Why: the client must send the right command sequence, must
parse the capability advertisement before asking to upgrade, and must refuse
to continue in cleartext when the server never offered STARTTLS. The socket
upgrade itself is not possible on this runtime (no `rt_tls_client_from_fd`),
so `mail_send` refuses 587 before connecting and names the missing symbol.

## Scenarios

### SMTP STARTTLS negotiation (RFC 3207)

#### sends EHLO, reads STARTTLS from the 250 block, sends STARTTLS and stops at 220 ready to upgrade

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- sends EHLO, reads STARTTLS from the 250 block, sends STARTTLS and stops at 220 ready to upgrade
- Client opens with EHLO
   - Expected: st0.next_command equals `EHLO localhost\r\n`
   - Expected: st0.ready is false
- Server advertises STARTTLS in the multiline 250 reply
   - Expected: st1.error equals ``
   - Expected: st1.advertised is true
   - Expected: st1.next_command equals `STARTTLS\r\n`
- Server answers 220 Ready to start TLS: the socket must now be wrapped
   - Expected: st2.error equals ``
   - Expected: st2.ready is true
   - Expected: st2.next_command equals ``
   - Expected: st2.sent equals `["EHLO localhost\r\n", "STARTTLS\r\n"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("sends EHLO, reads STARTTLS from the 250 block, sends STARTTLS and stops at 220 ready to upgrade")
step("Client opens with EHLO")
val st0 = starttls_begin(STARTTLS_SMTP, "localhost")
expect(st0.next_command).to_equal("EHLO localhost\r\n")
expect(st0.ready).to_equal(false)
step("Server advertises STARTTLS in the multiline 250 reply")
val st1 = starttls_feed(st0, smtp_ehlo_with_starttls())
expect(st1.error).to_equal("")
expect(st1.advertised).to_equal(true)
expect(st1.next_command).to_equal("STARTTLS\r\n")
step("Server answers 220 Ready to start TLS: the socket must now be wrapped")
val st2 = starttls_feed(st1, ["220 Ready to start TLS"])
expect(st2.error).to_equal("")
expect(st2.ready).to_equal(true)
expect(st2.next_command).to_equal("")
expect(st2.sent).to_equal(["EHLO localhost\r\n", "STARTTLS\r\n"])
```

</details>

#### refuses to continue when the server does not advertise STARTTLS

- refuses to continue when the server does not advertise STARTTLS
   - Expected: st.ready is false
   - Expected: st.advertised is false
- Only EHLO was ever sent; STARTTLS and credentials never left the client
   - Expected: st.sent equals `["EHLO localhost\r\n"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("refuses to continue when the server does not advertise STARTTLS")
val st = starttls_run_script(STARTTLS_SMTP, "localhost", [smtp_ehlo_without_starttls()])
expect(st.ready).to_equal(false)
expect(st.advertised).to_equal(false)
expect(st.error).to_contain("does not advertise STARTTLS")
step("Only EHLO was ever sent; STARTTLS and credentials never left the client")
expect(st.sent).to_equal(["EHLO localhost\r\n"])
```

</details>

#### treats a non-220 answer to STARTTLS as a refusal, and a bad EHLO as fatal

- treats a non-220 answer to STARTTLS as a refusal, and a bad EHLO as fatal
   - Expected: refused.ready is false
   - Expected: bad_ehlo.sent.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("treats a non-220 answer to STARTTLS as a refusal, and a bad EHLO as fatal")
val refused = starttls_run_script(STARTTLS_SMTP, "localhost", [smtp_ehlo_with_starttls(), ["454 TLS not available due to temporary reason"]])
expect(refused.ready).to_equal(false)
expect(refused.error).to_contain("STARTTLS refused (454)")
val bad_ehlo = starttls_run_script(STARTTLS_SMTP, "localhost", [["502 Command not implemented"]])
expect(bad_ehlo.error).to_contain("EHLO was not accepted (502)")
expect(bad_ehlo.sent.len()).to_equal(1)
```

</details>

#### parses the EHLO keyword list exactly (dash and space separators, case-insensitive)

- parses the EHLO keyword list exactly (dash and space separators, case-insensitive)
   - Expected: smtp_ehlo_advertises_starttls(["250-x", "250 STARTTLS"]) is true
   - Expected: smtp_ehlo_advertises_starttls(["250-starttls", "250 SIZE 1"]) is true
   - Expected: smtp_ehlo_advertises_starttls(["250-x", "250 SIZE 1", "STARTTLS"]) is false
   - Expected: smtp_ehlo_advertises_starttls(["250-STARTTLS-LIKE", "250 x"]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses the EHLO keyword list exactly (dash and space separators, case-insensitive)")
expect(smtp_ehlo_advertises_starttls(["250-x", "250 STARTTLS"])).to_equal(true)
expect(smtp_ehlo_advertises_starttls(["250-starttls", "250 SIZE 1"])).to_equal(true)
expect(smtp_ehlo_advertises_starttls(["250-x", "250 SIZE 1", "STARTTLS"])).to_equal(false)
expect(smtp_ehlo_advertises_starttls(["250-STARTTLS-LIKE", "250 x"])).to_equal(false)
```

</details>

### IMAP STARTTLS negotiation (RFC 3501 §6.2.1)

#### sends CAPABILITY, finds STARTTLS, sends a tagged STARTTLS and stops at the tagged OK

- sends CAPABILITY, finds STARTTLS, sends a tagged STARTTLS and stops at the tagged OK
   - Expected: st0.next_command equals `A1 CAPABILITY\r\n`
   - Expected: st1.error equals ``
   - Expected: st1.next_command equals `A2 STARTTLS\r\n`
   - Expected: st2.ready is true
   - Expected: st2.sent equals `["A1 CAPABILITY\r\n", "A2 STARTTLS\r\n"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("sends CAPABILITY, finds STARTTLS, sends a tagged STARTTLS and stops at the tagged OK")
val st0 = starttls_begin(STARTTLS_IMAP, "")
expect(st0.next_command).to_equal("A1 CAPABILITY\r\n")
val st1 = starttls_feed(st0, imap_capability_with_starttls())
expect(st1.error).to_equal("")
expect(st1.next_command).to_equal("A2 STARTTLS\r\n")
val st2 = starttls_feed(st1, ["A2 OK Begin TLS negotiation now."])
expect(st2.ready).to_equal(true)
expect(st2.sent).to_equal(["A1 CAPABILITY\r\n", "A2 STARTTLS\r\n"])
```

</details>

#### refuses when CAPABILITY lacks STARTTLS or the tagged STARTTLS reply is NO

- refuses when CAPABILITY lacks STARTTLS or the tagged STARTTLS reply is NO
   - Expected: missing.ready is false
   - Expected: missing.sent equals `["A1 CAPABILITY\r\n"]`
   - Expected: no.ready is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("refuses when CAPABILITY lacks STARTTLS or the tagged STARTTLS reply is NO")
val missing = starttls_run_script(STARTTLS_IMAP, "", [imap_capability_without_starttls()])
expect(missing.ready).to_equal(false)
expect(missing.error).to_contain("does not advertise STARTTLS")
expect(missing.sent).to_equal(["A1 CAPABILITY\r\n"])
val no = starttls_run_script(STARTTLS_IMAP, "", [imap_capability_with_starttls(), ["A2 NO STARTTLS unavailable"]])
expect(no.ready).to_equal(false)
expect(no.error).to_contain("STARTTLS refused")
```

</details>

#### reads STARTTLS from a greeting-style [CAPABILITY ...] code as well

- reads STARTTLS from a greeting-style [CAPABILITY ...] code as well
   - Expected: imap_capability_advertises_starttls(["* OK [CAPABILITY IMAP4rev1 STARTTLS] ready"]) is true
   - Expected: imap_capability_advertises_starttls(["* CAPABILITY IMAP4rev1"]) is false
- A transcript that ends mid-negotiation is an error, never a silent success


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reads STARTTLS from a greeting-style [CAPABILITY ...] code as well")
expect(imap_capability_advertises_starttls(["* OK [CAPABILITY IMAP4rev1 STARTTLS] ready"])).to_equal(true)
expect(imap_capability_advertises_starttls(["* CAPABILITY IMAP4rev1"])).to_equal(false)
step("A transcript that ends mid-negotiation is an error, never a silent success")
val short = starttls_run_script(STARTTLS_IMAP, "", [])
expect(short.error).to_contain("transcript ended before the server answered 'A1 CAPABILITY'")
```

</details>

### mail_send on the STARTTLS port

#### refuses 587 before any connect, naming the missing runtime symbol

- refuses 587 before any connect, naming the missing runtime symbol
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("refuses 587 before any connect, naming the missing runtime symbol")
reset_config()
parse_config_text("mail:\n    smtp_host: smtp.invalid\n    smtp_port: 587\n    user: u\n    secret_env: X\n")
val (ok, err) = mail_send("a@b.test", "s", "b")
expect(ok).to_equal(false)
expect(err).to_contain("587")
expect(err).to_contain("STARTTLS")
expect(err).to_contain(STARTTLS_MISSING_RUNTIME_SYMBOL)
expect(err).to_contain("tls_no_fd_upgrade_blocks_starttls_2026-08-25.md")
expect(starttls_runtime_gap_error(587)).to_contain("rt_tls_client_from_fd")
reset_config()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LLM-CARET-MAIL-STARTTLS`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `242c6edc069118874f095c9c06c8a5b723dec561a7ae0543198c3bd3f4a2ae74`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `242c6edc069118874f095c9c06c8a5b723dec561a7ae0543198c3bd3f4a2ae74`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `242c6edc069118874f095c9c06c8a5b723dec561a7ae0543198c3bd3f4a2ae74`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/infra_mail_starttls_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/infra_mail_starttls_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/infra_mail_starttls_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/infra_mail_starttls_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/infra_mail_starttls_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/infra_mail_starttls_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/infra_mail_starttls_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sends EHLO, reads STARTTLS from the 250 block, sends STARTTLS and stops at 220 ready to upgrade' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/infra_mail_starttls_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses to continue when the server does not advertise STARTTLS' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/infra_mail_starttls_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats a non-220 answer to STARTTLS as a refusal, and a bad EHLO as fatal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
