# infra_tools_spec

> Purpose: Prove that the LLM Caret infrastructure tools (mail_list / mail_read /

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# infra_tools_spec

Purpose: Prove that the LLM Caret infrastructure tools (mail_list / mail_read /

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/infra_tools_spec.spl` |
| Updated | 2026-08-25 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that the LLM Caret infrastructure tools (mail_list / mail_read /
mail_send / storage_ls / storage_get / storage_put) are advertised with
well-formed schemas, gated by the same permission policy as bash/write_file,
refuse honestly when unconfigured, and validate their arguments before any
network step.
Audience: llm_caret maintainers and anyone extending the tool surface.

## Scenarios

### infra tool schemas

#### advertises every infra tool with a name, description and object input_schema

- Collect the full schema list run_tool can dispatch
   - Expected: all.len() equals `14`
- Every infra tool has a well-formed entry
   - Expected: _json_get_str(s, "name") equals `name`
   - Expected: _json_get_str(s, "description").len() > 10 is true
   - Expected: _count_char(s, "{") equals `_count_char(s, "}")`
   - Expected: _count_char(s, "[") equals `_count_char(s, "]")`
   - Expected: s.starts_with("{") is true
   - Expected: s.ends_with("}") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Collect the full schema list run_tool can dispatch")
val all = tool_schemas()
expect(all.len()).to_equal(14)

step("Every infra tool has a well-formed entry")
for name in INFRA_TOOLS:
    val s = _schema_named(name)
    assert_not_equal(s, "")
    expect(_json_get_str(s, "name")).to_equal(name)
    expect(_json_get_str(s, "description").len() > 10).to_equal(true)
    expect(s).to_contain("\"input_schema\": {\"type\": \"object\"")
    # balanced braces and brackets => structurally valid JSON object
    expect(_count_char(s, "{")).to_equal(_count_char(s, "}"))
    expect(_count_char(s, "[")).to_equal(_count_char(s, "]"))
    expect(s.starts_with("{")).to_equal(true)
    expect(s.ends_with("}")).to_equal(true)
```

</details>

#### marks required arguments per tool

- mail_send requires to/subject/body; storage_put requires key/content
- read-only listings have no required arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("mail_send requires to/subject/body; storage_put requires key/content")
expect(_schema_named("mail_send")).to_contain("\"required\": [\"to\", \"subject\", \"body\"]")
expect(_schema_named("storage_put")).to_contain("\"required\": [\"key\", \"content\"]")
expect(_schema_named("mail_read")).to_contain("\"required\": [\"uid\"]")
expect(_schema_named("storage_get")).to_contain("\"required\": [\"key\"]")
step("read-only listings have no required arguments")
expect(_schema_named("mail_list")).to_contain("\"required\": []")
expect(_schema_named("storage_ls")).to_contain("\"required\": []")
```

</details>

#### mutating tools say so in their description

- module-level lists agree with the aggregate
   - Expected: mail_tool_schemas().len() equals `3`
   - Expected: storage_tool_schemas().len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_json_get_str(_schema_named("mail_send"), "description")).to_contain("MUTATING")
expect(_json_get_str(_schema_named("storage_put"), "description")).to_contain("MUTATING")
expect(_json_get_str(_schema_named("wiki_write"), "description")).to_contain("MUTATING")
step("module-level lists agree with the aggregate")
expect(mail_tool_schemas().len()).to_equal(3)
expect(storage_tool_schemas().len()).to_equal(3)
```

</details>

### infra tool permission classification

#### classifies mail_list/mail_read/storage_ls/storage_get as read-only

- read-only tools are auto-allowed even under the default policy
   - Expected: permission_decision(default_policy(WS), name) equals `allow`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for name in READ_ONLY:
    expect(is_read_only_tool(name)).to_equal(true)
    expect(is_mutating_tool(name)).to_equal(false)
    expect(is_known_tool(name)).to_equal(true)
    step("read-only tools are auto-allowed even under the default policy")
    expect(permission_decision(default_policy(WS), name)).to_equal("allow")
```

</details>

#### classifies mail_send/storage_put as mutating, same gate as bash/write_file

- default policy resolves to ask, not allow
   - Expected: permission_decision(default_policy(WS), name) equals `ask`
- explicit grant and allow-all resolve to allow
   - Expected: permission_decision(policy_with_allow(WS, [name]), name) equals `allow`
   - Expected: permission_decision(allow_all_policy(WS), name) equals `allow`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for name in MUTATING + ["bash", "write_file"]:
    expect(is_mutating_tool(name)).to_equal(true)
    expect(is_read_only_tool(name)).to_equal(false)
    step("default policy resolves to ask, not allow")
    expect(permission_decision(default_policy(WS), name)).to_equal("ask")
    step("explicit grant and allow-all resolve to allow")
    expect(permission_decision(policy_with_allow(WS, [name]), name)).to_equal("allow")
    expect(permission_decision(allow_all_policy(WS), name)).to_equal("allow")
```

</details>

#### denies mail_send and storage_put by default before touching config

- mail_send with a complete, valid input is still denied
   - Expected: r1.is_error is true
   - Expected: r1.tool_use_id equals `m1`
- storage_put likewise
   - Expected: r2.is_error is true
- a grant for one mutating tool does not leak to the other
   - Expected: r3.is_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_config()
_configure_mail_unreachable()
_configure_storage_unreachable()
step("mail_send with a complete, valid input is still denied")
val r1 = run_tool(default_policy(WS), new_tool_call("m1", "mail_send",
    "{\"to\": \"a@example.test\", \"subject\": \"s\", \"body\": \"b\"}"))
expect(r1.is_error).to_equal(true)
expect(r1.content).to_contain("permission denied")
expect(r1.content).to_contain("mail_send")
expect(r1.tool_use_id).to_equal("m1")
step("storage_put likewise")
val r2 = run_tool(default_policy(WS), new_tool_call("s1", "storage_put",
    "{\"key\": \"k.txt\", \"content\": \"v\"}"))
expect(r2.is_error).to_equal(true)
expect(r2.content).to_contain("permission denied")
expect(r2.content).to_contain("storage_put")
step("a grant for one mutating tool does not leak to the other")
val r3 = run_tool(policy_with_allow(WS, ["mail_send"]), new_tool_call("s2", "storage_put",
    "{\"key\": \"k.txt\", \"content\": \"v\"}"))
expect(r3.is_error).to_equal(true)
expect(r3.content).to_contain("permission denied")
reset_config()
```

</details>

### infra tools when not configured

#### mail tools return the honest not-configured error

- mail_send past the gate reports the same honest error
   - Expected: rs.is_error is true
   - Expected: rs.content equals `mail not configured: set [mail] in llm_caret.sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_config()
for name in ["mail_list", "mail_read"]:
    var input = "{}"
    if name == "mail_read":
        input = "{\"uid\": \"7\"}"
    val r = run_tool(default_policy(WS), new_tool_call("u", name, input))
    expect(r.is_error).to_equal(true)
    expect(r.content).to_equal("mail not configured: set [mail] in llm_caret.sdn")
step("mail_send past the gate reports the same honest error")
val rs = run_tool(allow_all_policy(WS), new_tool_call("u2", "mail_send",
    "{\"to\": \"a@example.test\", \"subject\": \"s\", \"body\": \"b\"}"))
expect(rs.is_error).to_equal(true)
expect(rs.content).to_equal("mail not configured: set [mail] in llm_caret.sdn")
```

</details>

#### storage tools return the honest not-configured error

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_config()
val r1 = run_tool(default_policy(WS), new_tool_call("u", "storage_ls", "{}"))
expect(r1.is_error).to_equal(true)
expect(r1.content).to_equal("storage not configured: set [storage] in llm_caret.sdn")
val r2 = run_tool(default_policy(WS), new_tool_call("u", "storage_get", "{\"key\": \"k\"}"))
expect(r2.content).to_equal("storage not configured: set [storage] in llm_caret.sdn")
val r3 = run_tool(allow_all_policy(WS), new_tool_call("u", "storage_put", "{\"key\": \"k\", \"content\": \"v\"}"))
expect(r3.is_error).to_equal(true)
expect(r3.content).to_equal("storage not configured: set [storage] in llm_caret.sdn")
```

</details>

#### names the missing secret env var, never a value, and never connects

- storage keys resolve the same way
   - Expected: s.is_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_config()
_configure_mail_unreachable()
val r = run_tool(default_policy(WS), new_tool_call("u", "mail_list", "{}"))
expect(r.is_error).to_equal(true)
expect(r.content).to_contain("LLM_CARET_SPEC_MAIL_SECRET_UNSET")
expect(r.content).to_contain("is empty")
step("storage keys resolve the same way")
_configure_storage_unreachable()
val s = run_tool(default_policy(WS), new_tool_call("u", "storage_ls", "{}"))
expect(s.is_error).to_equal(true)
expect(s.content).to_contain("LLM_CARET_SPEC_AK_UNSET")
reset_config()
```

</details>

#### refuses the ftp backend honestly instead of aborting on the unbacked extern

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_config()
parse_config_text("storage:\n    backend: ftp\n    endpoint: 127.0.0.1:2121\n    bucket: b\n    access_key_env: A\n    secret_key_env: B\n")
val r = run_tool(default_policy(WS), new_tool_call("u", "storage_ls", "{}"))
expect(r.is_error).to_equal(true)
expect(r.content).to_contain("ftp")
expect(r.content).to_contain("unbacked")
expect(r.content).to_contain("ftp_sffi.spl")
reset_config()
```

</details>

### infra tool argument validation (before any config or network step)

#### mail_send rejects a missing or malformed 'to' and an empty subject

- through run_tool the same error is surfaced as a tool error
   - Expected: r.is_error is true
   - Expected: r.content equals `mail_send: missing required 'to'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_config()
val (ok1, e1) = mail_send("", "s", "b")
expect(ok1).to_equal(false)
expect(e1).to_equal("mail_send: missing required 'to'")
val (ok2, e2) = mail_send("not-an-address", "s", "b")
expect(ok2).to_equal(false)
expect(e2).to_contain("not an email address")
val (ok3, e3) = mail_send("a@example.test", "", "b")
expect(ok3).to_equal(false)
expect(e3).to_equal("mail_send: missing required 'subject'")
step("through run_tool the same error is surfaced as a tool error")
val r = run_tool(allow_all_policy(WS), new_tool_call("v", "mail_send", "{\"subject\": \"s\", \"body\": \"b\"}"))
expect(r.is_error).to_equal(true)
expect(r.content).to_equal("mail_send: missing required 'to'")
```

</details>

#### mail_send refuses STARTTLS port 587 with an honest facade-gap error

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_config()
parse_config_text("mail:\n    smtp_host: smtp.invalid\n    smtp_port: 587\n    user: u\n    secret_env: X\n")
val (ok, err) = mail_send("a@example.test", "s", "b")
expect(ok).to_equal(false)
expect(err).to_contain("587")
expect(err).to_contain("STARTTLS")
reset_config()
```

</details>

#### mail_build_message emits RFC 5322 headers and exactly ONE DATA terminator (live-server defect 2026-08-25)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Before the fix mail_send used smtp.send.message_build_simple, whose
# mime_type_text_plain() call hit a bodyless forward declaration and
# aborted the whole tool with "missing return in non-unit function"
# against a real greenmail SMTP; it also appended message_terminate()
# on top of smtp_dot_stuff's own terminator (a stray "." command).
val msg = mail_build_message("caret@localhost", "to@example.test", "hello", "line one\n.starts with dot\nline three")
expect(msg).to_equal("From: caret@localhost\r\nTo: to@example.test\r\nSubject: hello\r\nContent-Type: text/plain; charset=utf-8\r\n\r\nline one\r\n..starts with dot\r\nline three\r\n.\r\n")
expect(msg.split("\r\n.\r\n").len()).to_equal(2)
```

</details>

#### mail_read rejects a missing or non-numeric uid

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_config()
val (ok1, e1) = mail_read("")
expect(ok1).to_equal(false)
expect(e1).to_equal("mail_read: missing required 'uid'")
val (ok2, e2) = mail_read("12a")
expect(ok2).to_equal(false)
expect(e2).to_contain("decimal IMAP UID")
```

</details>

#### storage_get and storage_put reject an empty, absolute or traversing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_config()
val (g1, ge1) = storage_get("", "", 0)
expect(g1).to_equal(false)
expect(ge1).to_equal("storage_get: missing required 'key'")
val (g2, ge2) = storage_get("b", "/etc/passwd", 0)
expect(g2).to_equal(false)
expect(ge2).to_contain("no leading '/'")
val (p1, pe1) = storage_put("b", "", "v")
expect(p1).to_equal(false)
expect(pe1).to_equal("storage_put: missing required 'key'")
val (p2, pe2) = storage_put("b", "a/../b", "v")
expect(p2).to_equal(false)
expect(pe2).to_contain("'..'")
```

</details>

#### storage_get enforces the byte cap and storage_put the upload cap

- a cap within range is accepted and the next failure is config, not the cap
   - Expected: ok2 is false
   - Expected: err2 equals `storage not configured: set [storage] in llm_caret.sdn`
- oversized put content is refused before config
   - Expected: big.len() > 4194304 is true
   - Expected: p is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_config()
val cap = storage_get_max_bytes()
expect(cap).to_equal(262144)
val (ok, err) = storage_get("b", "k", cap + 1)
expect(ok).to_equal(false)
expect(err).to_contain("exceeds the tool cap")
expect(err).to_contain(cap.to_text())
step("a cap within range is accepted and the next failure is config, not the cap")
val (ok2, err2) = storage_get("b", "k", cap)
expect(ok2).to_equal(false)
expect(err2).to_equal("storage not configured: set [storage] in llm_caret.sdn")
step("oversized put content is refused before config")
var big = "0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
var i = 0
while i < 16:
    big = big + big
    i = i + 1
expect(big.len() > 4194304).to_equal(true)
val (p, pe) = storage_put("b", "k", big)
expect(p).to_equal(false)
expect(pe).to_contain("over the tool cap")
```

</details>

#### unknown tool names still fail closed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = run_tool(allow_all_policy(WS), new_tool_call("x", "mail_delete", "{}"))
expect(r.is_error).to_equal(true)
expect(r.content).to_equal("unknown tool: mail_delete")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
