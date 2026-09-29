# fetch_parse_spec

> RFC 3501 FETCH response parsing for the IMAP owner module.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fetch_parse_spec

RFC 3501 FETCH response parsing for the IMAP owner module.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/imap/fetch_parse_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

RFC 3501 FETCH response parsing for the IMAP owner module.

Who: a mail client author (LLM Caret's mail_list / mail_read tools) reading
`* N FETCH (...)` responses off a socket. Why: the previous line scanner
treated every line independently, so a message body containing ")" or a
tag-looking line could end a response early and header values could be
mis-attributed. The parser here frames by literal byte count and returns
typed items, and the framer is shared by the TCP and TLS transports.

Transcripts are RFC-exact, hand-crafted in greenmail's shape (UID first,
FLAGS, RFC822.SIZE, then a BODY[...] literal). Literal headers are built by
concatenation because `{N}` inside a spec string literal is interpolation.

## Scenarios

### IMAP FETCH response framing (imap_response_complete)

#### recognises a literal size suffix and rejects everything else

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- recognises a literal size suffix and rejects everything else
- Parse the {N} suffix of a response line
   - Expected: imap_literal_size("* 1 FETCH (BODY[] " + "{" + "42" + "}") equals `42`
   - Expected: imap_literal_size("* 1 FETCH (BODY[] " + "{" + "0" + "}") equals `0`
   - Expected: imap_literal_size("A1 OK done") equals `-1`
   - Expected: imap_literal_size("* 1 FETCH (BODY[] {}") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("recognises a literal size suffix and rejects everything else")
step("Parse the {N} suffix of a response line")
expect(imap_literal_size("* 1 FETCH (BODY[] " + "{" + "42" + "}")).to_equal(42)
expect(imap_literal_size("* 1 FETCH (BODY[] " + "{" + "0" + "}")).to_equal(0)
expect(imap_literal_size("A1 OK done")).to_equal(-1)
expect(imap_literal_size("* 1 FETCH (BODY[] {}")).to_equal(-1)
```

</details>

#### does not let a tag-looking line inside a literal terminate the response

- does not let a tag-looking line inside a literal terminate the response
- Build a body whose literal contains the tagged OK line and a ')'
- The framer consumes exactly through the real tagged line
   - Expected: imap_response_complete(raw, "A3") equals `raw.length()`
- A prefix that ends inside the literal is incomplete
   - Expected: imap_response_complete(raw.substring(0, 40), "A3") equals `-1`
- A prefix that ends after the literal but before the tag is incomplete
   - Expected: imap_response_complete(raw.substring(0, cut), "A3") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not let a tag-looking line inside a literal terminate the response")
step("Build a body whose literal contains the tagged OK line and a ')'")
val body = "A3 OK fake)\r\nreal body\r\n"
val raw = "* 1 FETCH (UID 9 BODY[] " + lit(body) + ")" + crlf() + "A3 OK Fetch completed" + crlf()
step("The framer consumes exactly through the real tagged line")
expect(imap_response_complete(raw, "A3")).to_equal(raw.length())
step("A prefix that ends inside the literal is incomplete")
expect(imap_response_complete(raw.substring(0, 40), "A3")).to_equal(-1)
step("A prefix that ends after the literal but before the tag is incomplete")
val cut = raw.length() - 5
expect(imap_response_complete(raw.substring(0, cut), "A3")).to_equal(-1)
```

</details>

#### accepts the untagged greeting when asked for tag '*'

- accepts the untagged greeting when asked for tag '*'
   - Expected: imap_response_complete(greeting, "*") equals `greeting.length()`
   - Expected: imap_response_complete("* OK partial", "*") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts the untagged greeting when asked for tag '*'")
val greeting = "* OK IMAP4rev1 Server GreenMail v2.1.3 ready" + crlf()
expect(imap_response_complete(greeting, "*")).to_equal(greeting.length())
expect(imap_response_complete("* OK partial", "*")).to_equal(-1)
```

</details>

### IMAP FETCH response parsing (imap_parse_fetch_response)

#### returns typed items for a header-fields FETCH with UID, FLAGS and RFC822.SIZE

- returns typed items for a header-fields FETCH with UID, FLAGS and RFC822.SIZE
- Feed one greenmail-shaped FETCH row followed by the tagged OK
   - Expected: r.error equals ``
   - Expected: r.tag_seen is true
   - Expected: r.tag_status equals `IMAP_STATUS_OK`
   - Expected: r.messages.len() equals `1`
- Items are addressable by name, case-insensitively
   - Expected: m.seq equals `1`
   - Expected: imap_fetch_uid(m) equals `101`
   - Expected: imap_fetch_size(m) equals `512`
   - Expected: imap_fetch_flags(m) equals `["\\Seen"]`
   - Expected: imap_fetch_item(m, "rfc822.size") equals `512`
- The literal is returned byte-exact, CRLFs included
   - Expected: imap_fetch_item_prefixed(m, "BODY[HEADER") equals `headers`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns typed items for a header-fields FETCH with UID, FLAGS and RFC822.SIZE")
step("Feed one greenmail-shaped FETCH row followed by the tagged OK")
val headers = "Subject: Weekly report" + crlf() + "From: Ann <ann@example.test>" + crlf() + "Date: Mon, 24 Aug 2026 09:00:00 +0000" + crlf() + crlf()
val raw = header_row(1, 101, headers) + "A3 OK FETCH completed." + crlf()
val r = imap_parse_fetch_response(raw, "A3")
expect(r.error).to_equal("")
expect(r.tag_seen).to_equal(true)
expect(r.tag_status).to_equal(IMAP_STATUS_OK)
expect(r.messages.len()).to_equal(1)
step("Items are addressable by name, case-insensitively")
val m = r.messages[0]
expect(m.seq).to_equal(1)
expect(imap_fetch_uid(m)).to_equal("101")
expect(imap_fetch_size(m)).to_equal(512)
expect(imap_fetch_flags(m)).to_equal(["\\Seen"])
expect(imap_fetch_item(m, "rfc822.size")).to_equal("512")
step("The literal is returned byte-exact, CRLFs included")
expect(imap_fetch_item_prefixed(m, "BODY[HEADER")).to_equal(headers)
```

</details>

#### parses several messages, interleaved untagged responses and folded headers

- parses several messages, interleaved untagged responses and folded headers
- Two FETCH rows with an EXISTS/RECENT pair between them
   - Expected: r.error equals ``
   - Expected: r.messages.len() equals `2`
   - Expected: r.others equals `["5 EXISTS", "1 RECENT"]`
   - Expected: imap_fetch_uid(r.messages[0]) equals `7`
   - Expected: imap_fetch_uid(r.messages[1]) equals `8`
- Folded header lines are unfolded into one value
   - Expected: imap_header_value(fields, "subject") equals `a very long subject that folds onto a second line`
   - Expected: imap_header_value(fields, "Date") equals `Tue, 25 Aug 2026 10:00:00 +0000`
   - Expected: imap_header_value(fields, "X-Missing") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses several messages, interleaved untagged responses and folded headers")
step("Two FETCH rows with an EXISTS/RECENT pair between them")
val h1 = "Subject: first" + crlf() + "From: a@x" + crlf() + crlf()
val h2 = "Subject: a very long subject" + crlf() + " that folds onto a second line" + crlf() + "From: b@y" + crlf() + "Date: Tue, 25 Aug 2026 10:00:00 +0000" + crlf() + crlf()
val raw = header_row(3, 7, h1) + "* 5 EXISTS" + crlf() + "* 1 RECENT" + crlf() + header_row(4, 8, h2) + "A3 OK done" + crlf()
val r = imap_parse_fetch_response(raw, "A3")
expect(r.error).to_equal("")
expect(r.messages.len()).to_equal(2)
expect(r.others).to_equal(["5 EXISTS", "1 RECENT"])
expect(imap_fetch_uid(r.messages[0])).to_equal("7")
expect(imap_fetch_uid(r.messages[1])).to_equal("8")
step("Folded header lines are unfolded into one value")
val fields = imap_parse_header_fields(imap_fetch_item_prefixed(r.messages[1], "BODY[HEADER"))
expect(imap_header_value(fields, "subject")).to_equal("a very long subject that folds onto a second line")
expect(imap_header_value(fields, "Date")).to_equal("Tue, 25 Aug 2026 10:00:00 +0000")
expect(imap_header_value(fields, "X-Missing")).to_equal("")
```

</details>

#### keeps a body literal containing ')' and CRLF intact for UID FETCH BODY[]

- keeps a body literal containing ')' and CRLF intact for UID FETCH BODY[]
   - Expected: r.error equals ``
   - Expected: r.messages.len() equals `1`
   - Expected: imap_fetch_item_prefixed(r.messages[0], "BODY[") equals `body`
   - Expected: r.tag_message equals `UID FETCH completed.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps a body literal containing ')' and CRLF intact for UID FETCH BODY[]")
val body = "From: a@x" + crlf() + "Subject: parens" + crlf() + crlf() + "line one (with parens)" + crlf() + ")" + crlf() + "A3 OK not really" + crlf()
val raw = "* 2 FETCH (UID 44 BODY[] " + lit(body) + ")" + crlf() + "A3 OK UID FETCH completed." + crlf()
val r = imap_parse_fetch_response(raw, "A3")
expect(r.error).to_equal("")
expect(r.messages.len()).to_equal(1)
expect(imap_fetch_item_prefixed(r.messages[0], "BODY[")).to_equal(body)
expect(r.tag_message).to_equal("UID FETCH completed.")
```

</details>

#### handles multibyte UTF-8 in a literal by byte count, and an empty literal

- handles multibyte UTF-8 in a literal by byte count, and an empty literal
   - Expected: r.error equals ``
   - Expected: imap_fetch_item(r.messages[0], "BODY[HEADER]") equals `body`
   - Expected: imap_fetch_item(r.messages[0], "BODY[TEXT]") equals ``
   - Expected: r.messages[0].items.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles multibyte UTF-8 in a literal by byte count, and an empty literal")
val body = "Subject: caf\u{e9} \u{2603}" + crlf() + crlf()
val raw = "* 1 FETCH (UID 1 BODY[HEADER] " + lit(body) + " BODY[TEXT] " + "{" + "0" + "}" + crlf() + ")" + crlf() + "A9 OK ok" + crlf()
val r = imap_parse_fetch_response(raw, "A9")
expect(r.error).to_equal("")
expect(imap_fetch_item(r.messages[0], "BODY[HEADER]")).to_equal(body)
expect(imap_fetch_item(r.messages[0], "BODY[TEXT]")).to_equal("")
expect(r.messages[0].items.len()).to_equal(3)
```

</details>

#### reports an empty mailbox FETCH (no rows, tagged OK) and NO/BAD terminators

- reports an empty mailbox FETCH (no rows, tagged OK) and NO/BAD terminators
- Only the tagged line
   - Expected: empty.error equals ``
   - Expected: empty.messages.len() equals `0`
   - Expected: empty.tag_status equals `IMAP_STATUS_OK`
- Tagged NO carries the server's reason
   - Expected: no.tag_status equals `IMAP_STATUS_NO`
   - Expected: no.tag_message equals `[NONEXISTENT] no such message`
- Tagged BAD is distinguished from NO
   - Expected: imap_parse_fetch_response("A3 BAD parse error" + crlf(), "A3").tag_status equals `IMAP_STATUS_BAD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports an empty mailbox FETCH (no rows, tagged OK) and NO/BAD terminators")
step("Only the tagged line")
val empty = imap_parse_fetch_response("A3 OK FETCH completed." + crlf(), "A3")
expect(empty.error).to_equal("")
expect(empty.messages.len()).to_equal(0)
expect(empty.tag_status).to_equal(IMAP_STATUS_OK)
step("Tagged NO carries the server's reason")
val no = imap_parse_fetch_response("A3 NO [NONEXISTENT] no such message" + crlf(), "A3")
expect(no.tag_status).to_equal(IMAP_STATUS_NO)
expect(no.tag_message).to_equal("[NONEXISTENT] no such message")
step("Tagged BAD is distinguished from NO")
expect(imap_parse_fetch_response("A3 BAD parse error" + crlf(), "A3").tag_status).to_equal(IMAP_STATUS_BAD)
```

</details>

#### fails closed on a truncated literal, a foreign tag, or a missing terminator

- fails closed on a truncated literal, a foreign tag, or a missing terminator
   - Expected: truncated.tag_seen is false
   - Expected: open.messages.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed on a truncated literal, a foreign tag, or a missing terminator")
val truncated = imap_parse_fetch_response("* 1 FETCH (UID 1 BODY[] " + "{" + "100" + "}" + crlf() + "short)" + crlf() + "A3 OK" + crlf(), "A3")
expect(truncated.error).to_contain("literal truncated")
expect(truncated.tag_seen).to_equal(false)
val foreign = imap_parse_fetch_response("A2 OK earlier" + crlf(), "A3")
expect(foreign.error).to_contain("unexpected tag 'A2'")
val open = imap_parse_fetch_response("* 1 FETCH (UID 1 FLAGS ())" + crlf(), "A3")
expect(open.error).to_contain("response ended before tag 'A3'")
expect(open.messages.len()).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-IMAP-FETCH-PARSE`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `11fee871249d14508459ff14bd41ca8845fa3e58246c47b75e75ba26f5f39c30`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `11fee871249d14508459ff14bd41ca8845fa3e58246c47b75e75ba26f5f39c30`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `11fee871249d14508459ff14bd41ca8845fa3e58246c47b75e75ba26f5f39c30`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/nogc_sync_mut/imap/fetch_parse_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/imap/fetch_parse_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/lib/nogc_sync_mut/imap/fetch_parse_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/imap/fetch_parse_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/imap/fetch_parse_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/imap/fetch_parse_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/nogc_sync_mut/imap/fetch_parse_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognises a literal size suffix and rejects everything else' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/imap/fetch_parse_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not let a tag-looking line inside a literal terminate the response' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/imap/fetch_parse_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts the untagged greeting when asked for tag '*'' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
