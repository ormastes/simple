# infra_servers_system_spec

> Purpose: Prove LIVE round trips of the LLM Caret infrastructure tools against

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 3 | 0 | 1 |

<details>
<summary>Full Scenario Manual</summary>

# infra_servers_system_spec

Purpose: Prove LIVE round trips of the LLM Caret infrastructure tools against

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/app/llm_caret/infra_servers_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove LIVE round trips of the LLM Caret infrastructure tools against
real servers: send a mail, list it, read its body; put an object, list it, get
identical bytes back. Every example runs the real IMAP/SMTP or SigV4 client
through run_tool (the permission gate) - nothing is fabricated from the request.
Audience: llm_caret maintainers and infra operators validating a deployment.

## Live gates (honest blocking)
The repository ships no in-process or child SMTP, IMAP, S3-compatible or FTP
server (`std.nogc_sync_mut.imap` / `smtp` are protocol builders only; the
`ftp_sffi` externs are unbacked), and this host has no minio/aiosmtpd/pyftpdlib.
An example therefore runs only when the operator points it at a real server:

- mail:    LLM_CARET_MAIL_LIVE=1 plus LLM_CARET_CONFIG=<llm_caret.sdn with [mail]>
           and the env var named by `secret_env` exported.
- storage: LLM_CARET_STORAGE_LIVE=1 plus LLM_CARET_CONFIG=<llm_caret.sdn with
           [storage]> and the env vars named by access_key_env / secret_key_env.
- wiki:    LLM_CARET_WIKI_LIVE=1 plus LLM_CARET_CONFIG=<llm_caret.sdn with [wiki]
           backend: confluence> and the env var named by token_env exported.
           (No Confluence runs on this host; the local markdown backend is
           covered server-free in test/01_unit/app/llm_caret/infra_wiki_spec.spl.)

Without the gate the example reports `pending(BLOCKED: ...)` and returns; it
never silently passes.

## Scenarios

### infra servers: mail round trip (SMTP send -> IMAP list -> IMAP read)

#### sends a mail, sees it in mail_list and reads its body back

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- sends a mail, sees it in mail_list and reads its body back
   - Expected: cfg_err equals ``
- mail_send goes through the gate with an explicit allow
   - Expected: sent.is_error is false
- mail_list shows the nonce subject with a uid
   - Expected: listed.is_error is false
- mail_read returns the exact body we sent (absolute oracle: the nonce)
   - Expected: read.is_error is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sends a mail, sees it in mail_list and reads its body back")
if not _live("LLM_CARET_MAIL_LIVE"):
    pending("BLOCKED: no local SMTP/IMAP server on this host — set LLM_CARET_MAIL_LIVE=1 with credentials (LLM_CARET_CONFIG + secret_env) to run")
    return
val cfg_err = _load_live_config()
expect(cfg_err).to_equal("")
assert_not_equal(config_mail_imap_host(), "")
val nonce = _nonce()
val subject = "llm-caret-live-" + nonce
val body = "round-trip body " + nonce
val to = env_get("LLM_CARET_MAIL_TO") ?? ""
assert_not_equal(to, "")

step("mail_send goes through the gate with an explicit allow")
val sent = run_tool(allow_all_policy(WS), new_tool_call("send", "mail_send",
    _json([_kv("to", to), _kv("subject", subject), _kv("body", body)])))
expect(sent.is_error).to_equal(false)
expect(sent.content).to_contain("sent to " + to)

step("mail_list shows the nonce subject with a uid")
val listed = run_tool(allow_all_policy(WS), new_tool_call("list", "mail_list",
    _json([_kv("mailbox", "INBOX"), "\"limit\": 50"])))
expect(listed.is_error).to_equal(false)
expect(listed.content).to_contain(subject)
var uid = ""
for line in listed.content.split("\n"):
    if line.contains(subject) and line.starts_with("uid="):
        uid = line.split(" ")[0].substring(4)
assert_not_equal(uid, "")

step("mail_read returns the exact body we sent (absolute oracle: the nonce)")
val read = run_tool(allow_all_policy(WS), new_tool_call("read", "mail_read", _json([_kv("uid", uid)])))
expect(read.is_error).to_equal(false)
expect(read.content).to_contain("Subject: " + subject)
expect(read.content).to_contain(body)
reset_config()
```

</details>

### infra servers: storage round trip (put -> ls -> get)

#### puts an object, lists it and gets identical bytes back

- puts an object, lists it and gets identical bytes back
   - Expected: cfg_err equals ``
- storage_put goes through the gate with an explicit allow
   - Expected: put.is_error is false
- storage_ls under the prefix shows the key with its byte size
   - Expected: ls.is_error is false
- storage_get returns byte-identical content (absolute oracle: nonce + exact length)
   - Expected: got.is_error is false
   - Expected: got.content equals `content`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("puts an object, lists it and gets identical bytes back")
if not _live("LLM_CARET_STORAGE_LIVE"):
    pending("BLOCKED: no local S3-compatible (minio) server on this host — set LLM_CARET_STORAGE_LIVE=1 with credentials (LLM_CARET_CONFIG + access_key_env/secret_key_env) to run")
    return
val cfg_err = _load_live_config()
expect(cfg_err).to_equal("")
assert_not_equal(config_storage_endpoint(), "")
val nonce = _nonce()
val key = "llm-caret-live/" + nonce + ".txt"
val content = "line one " + nonce + "\nline two\n"

step("storage_put goes through the gate with an explicit allow")
val put = run_tool(allow_all_policy(WS), new_tool_call("put", "storage_put",
    _json([_kv("key", key), _kv("content", "line one " + nonce + "\\nline two\\n")])))
expect(put.is_error).to_equal(false)
expect(put.content).to_contain("stored " + content.len().to_text() + " bytes")

step("storage_ls under the prefix shows the key with its byte size")
val ls = run_tool(allow_all_policy(WS), new_tool_call("ls", "storage_ls", _json([_kv("prefix", "llm-caret-live/")])))
expect(ls.is_error).to_equal(false)
expect(ls.content).to_contain(key + "\t" + content.len().to_text())

step("storage_get returns byte-identical content (absolute oracle: nonce + exact length)")
val got = run_tool(allow_all_policy(WS), new_tool_call("get", "storage_get", _json([_kv("key", key)])))
expect(got.is_error).to_equal(false)
expect(got.content).to_equal(content)
reset_config()
```

</details>

### infra servers: ftp backend

#### is blocked until the runtime backs the ftp facade _(pending)_

- is blocked until the runtime backs the ftp facade


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("is blocked until the runtime backs the ftp facade")
pending("BLOCKED: no local FTP server on this host and rt_ftp_* (src/lib/nogc_sync_mut/io/ftp_sffi.spl:17) is an unbacked runtime extern — set LLM_CARET_FTP_LIVE=1 with credentials to run once the facade is backed")
return
```

</details>

### infra servers: confluence wiki round trip (write -> search -> read)

#### creates a page, finds it by title and reads the body back

- creates a page, finds it by title and reads the body back
   - Expected: cfg_err equals ``
- wiki_write creates the page through the gate with an explicit allow
   - Expected: wrote.is_error is false
- wiki_search by title returns the new page id
   - Expected: found.is_error is false
- wiki_read returns the title and the nonce body (absolute oracle)
   - Expected: read.is_error is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates a page, finds it by title and reads the body back")
if not _live("LLM_CARET_WIKI_LIVE"):
    pending("BLOCKED: no local Confluence on this host — set LLM_CARET_WIKI_LIVE=1 with credentials (LLM_CARET_CONFIG with [wiki] backend: confluence + base_url/space/user, and the env var named by token_env exported) to run")
    return
val cfg_err = _load_live_config()
expect(cfg_err).to_equal("")
assert_not_equal(config_wiki_base_url(), "")
val nonce = _nonce()
val title = "llm-caret-live-" + nonce
val body = "<p>round-trip body " + nonce + "</p>"

step("wiki_write creates the page through the gate with an explicit allow")
val wrote = run_tool(allow_all_policy(WS), new_tool_call("w", "wiki_write",
    _json([_kv("title", title), _kv("body", "<p>round-trip body " + nonce + "</p>")])))
expect(wrote.is_error).to_equal(false)
expect(wrote.content).to_contain("created ")
val page_id = wrote.content.split(" ")[1]
assert_not_equal(page_id, "")

step("wiki_search by title returns the new page id")
val found = run_tool(allow_all_policy(WS), new_tool_call("s", "wiki_search", _json([_kv("query", title)])))
expect(found.is_error).to_equal(false)
expect(found.content).to_contain(page_id + "\t" + title)

step("wiki_read returns the title and the nonce body (absolute oracle)")
val read = run_tool(allow_all_policy(WS), new_tool_call("r", "wiki_read", _json([_kv("page_id", page_id)])))
expect(read.is_error).to_equal(false)
expect(read.content).to_contain("Title: " + title)
expect(read.content).to_contain("round-trip body " + nonce)
reset_config()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 1 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9d05ecbde9efbb59eaf8a3ff21e50ada28b83f3e87563070f64477e59859b13f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9d05ecbde9efbb59eaf8a3ff21e50ada28b83f3e87563070f64477e59859b13f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9d05ecbde9efbb59eaf8a3ff21e50ada28b83f3e87563070f64477e59859b13f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/llm_caret/infra_servers_system_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/infra_servers_system_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/app/llm_caret/infra_servers_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/infra_servers_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/infra_servers_system_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): unconditional pending or fail-fast scaffold remains
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/app/llm_caret/infra_servers_system_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sends a mail, sees it in mail_list and reads its body back' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/infra_servers_system_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'puts an object, lists it and gets identical bytes back' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/infra_servers_system_spec.spl:135:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is blocked until the runtime backs the ftp facade' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
