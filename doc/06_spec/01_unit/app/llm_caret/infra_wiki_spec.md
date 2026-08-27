# infra_wiki_spec

> Purpose: Prove the LLM Caret wiki tools (wiki_search / wiki_read / wiki_write)

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# infra_wiki_spec

Purpose: Prove the LLM Caret wiki tools (wiki_search / wiki_read / wiki_write)

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/infra_wiki_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove the LLM Caret wiki tools (wiki_search / wiki_read / wiki_write)
round-trip against the LOCAL markdown backend with real files, refuse path
traversal and unconfigured use honestly, and gate wiki_write behind the same
permission policy as write_file. Every write is verified by reading the file
back from disk (absolute oracle: the nonce'd body), never by trusting the
tool's own reply string.
Audience: llm_caret maintainers and anyone extending the wiki surface.

## Scenarios

### wiki tool schemas

#### advertises wiki_search / wiki_read / wiki_write through tool_schemas

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- advertises wiki_search / wiki_read / wiki_write through tool_schemas
   - Expected: wiki_tool_schemas().len() equals `3`
- wiki_write is marked MUTATING; the read-only pair is not
   - Expected: search_desc does not contain `MUTATING`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("advertises wiki_search / wiki_read / wiki_write through tool_schemas")
val names = ["wiki_search", "wiki_read", "wiki_write"]
expect(wiki_tool_schemas().len()).to_equal(3)
for name in names:
    var found = ""
    for s in tool_schemas():
        if _json_get_str(s, "name") == name:
            found = s
    assert_not_equal(found, "")
    expect(found).to_contain("\"input_schema\": {\"type\": \"object\"")
step("wiki_write is marked MUTATING; the read-only pair is not")
val all = tool_schemas()
var write_desc = ""
var search_desc = ""
for s in all:
    if _json_get_str(s, "name") == "wiki_write":
        write_desc = _json_get_str(s, "description")
    if _json_get_str(s, "name") == "wiki_search":
        search_desc = _json_get_str(s, "description")
expect(write_desc).to_contain("MUTATING")
expect(search_desc.contains("MUTATING")).to_equal(false)
```

</details>

### wiki tools: unconfigured and unsupported backends

#### refuses honestly with no [wiki] section

- refuses honestly with no [wiki] section
   - Expected: wiki_config_error() equals `wiki not configured: set [wiki] in llm_caret.sdn`
   - Expected: r.is_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("refuses honestly with no [wiki] section")
reset_config()
expect(wiki_config_error()).to_equal("wiki not configured: set [wiki] in llm_caret.sdn")
val r = run_tool(default_policy(_ws()), new_tool_call("s", "wiki_search", _json([_kv("query", "x")])))
expect(r.is_error).to_equal(true)
expect(r.content).to_contain("wiki not configured")
```

</details>

#### names the missing confluence pieces without touching the network

- names the missing confluence pieces without touching the network
- a token_env that is not an identifier is refused before any shell use


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("names the missing confluence pieces without touching the network")
reset_config()
parse_config_text("wiki:\n    backend: confluence\n    base_url: https://wiki.invalid\n    user: caret@example.test\n    token_env: LLM_CARET_SPEC_WIKI_TOKEN_UNSET\n")
val err = wiki_config_error()
expect(err).to_contain("LLM_CARET_SPEC_WIKI_TOKEN_UNSET")
expect(err).to_contain("is empty")
step("a token_env that is not an identifier is refused before any shell use")
reset_config()
parse_config_text("wiki:\n    backend: confluence\n    base_url: https://wiki.invalid\n    user: caret@example.test\n    token_env: BAD;rm -rf\n")
expect(wiki_config_error()).to_contain("not a valid environment variable name")
```

</details>

#### returns a tool error, never an abort, for an unknown backend

- returns a tool error, never an abort, for an unknown backend
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns a tool error, never an abort, for an unknown backend")
reset_config()
parse_config_text("wiki:\n    backend: mediawiki\n")
val (ok, msg) = wiki_read(_ws(), "any")
expect(ok).to_equal(false)
expect(msg).to_contain("not supported")
reset_config()
```

</details>

### wiki tools: local backend round trip

#### write -> search finds it -> read returns the exact body

- write -> search finds it -> read returns the exact body
- wiki_write creates a page from parent + title under the wiki root (explicit grant)
   - Expected: wrote.is_error is false
- absolute oracle: the file on disk holds the exact body
   - Expected: file_exists(path) is true
   - Expected: read_file_text(path) equals `body`
- wiki_search is case-insensitive and reports id, title, url
   - Expected: hit.is_error is false
- a query nothing matches says so instead of returning stale rows
   - Expected: miss.is_error is false
- wiki_read returns title, id and the byte-exact body
   - Expected: read.is_error is false
   - Expected: read.content equals `"Title: Caret Wiki " + nonce + "\nId: notes/caret_wiki_" + nonce + ".md\n\n" ... (full value in folded executable source)`
- wiki_write with page_id updates in place and the disk reflects it
   - Expected: upd.is_error is false
   - Expected: read_file_text(path) equals `"second " + nonce`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("write -> search finds it -> read returns the exact body")
_configure_local()
val nonce = _nonce()
val body = "# Caret Wiki " + nonce + "\n\nround-trip body " + nonce + "\n"
val ws = _ws()
dir_create_all(ws + "/wiki")

step("wiki_write creates a page from parent + title under the wiki root (explicit grant)")
val wrote = run_tool(policy_with_allow(ws, ["wiki_write"]), new_tool_call("w", "wiki_write",
    _json([_kv("parent", "notes"), _kv("title", "Caret Wiki " + nonce), _kv("body", "# Caret Wiki " + nonce + "\\n\\nround-trip body " + nonce + "\\n")])))
expect(wrote.is_error).to_equal(false)
expect(wrote.content).to_contain("created notes/caret_wiki_" + nonce + ".md")
step("absolute oracle: the file on disk holds the exact body")
val path = ws + "/wiki/notes/caret_wiki_" + nonce + ".md"
expect(file_exists(path)).to_equal(true)
expect(read_file_text(path)).to_equal(body)

step("wiki_search is case-insensitive and reports id, title, url")
val hit = run_tool(default_policy(ws), new_tool_call("s", "wiki_search", _json([_kv("query", "ROUND-TRIP BODY " + nonce)])))
expect(hit.is_error).to_equal(false)
expect(hit.content).to_contain("notes/caret_wiki_" + nonce + ".md\tCaret Wiki " + nonce + "\tfile://" + path)
step("a query nothing matches says so instead of returning stale rows")
val miss = run_tool(default_policy(ws), new_tool_call("s", "wiki_search", _json([_kv("query", "no-such-token-" + nonce + "-zz")])))
expect(miss.is_error).to_equal(false)
expect(miss.content).to_contain("no pages")

step("wiki_read returns title, id and the byte-exact body")
val read = run_tool(default_policy(ws), new_tool_call("r", "wiki_read", _json([_kv("page_id", "notes/caret_wiki_" + nonce + ".md")])))
expect(read.is_error).to_equal(false)
expect(read.content).to_equal("Title: Caret Wiki " + nonce + "\nId: notes/caret_wiki_" + nonce + ".md\n\n" + body)

step("wiki_write with page_id updates in place and the disk reflects it")
val upd = run_tool(allow_all_policy(ws), new_tool_call("u", "wiki_write",
    _json([_kv("page_id", "notes/caret_wiki_" + nonce + ".md"), _kv("body", "second " + nonce)])))
expect(upd.is_error).to_equal(false)
expect(upd.content).to_contain("updated notes/caret_wiki_" + nonce + ".md")
expect(read_file_text(path)).to_equal("second " + nonce)
reset_config()
```

</details>

#### rejects path traversal and pages outside the wiki root

- rejects path traversal and pages outside the wiki root
   - Expected: esc.is_error is true
   - Expected: wesc.is_error is true
   - Expected: file_exists(ws + "/escape.md") is false
- an absolute path outside the root is refused too
   - Expected: abs.is_error is true
- a missing page is a not-found error, not an empty success
   - Expected: missing.is_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects path traversal and pages outside the wiki root")
_configure_local()
val ws = _ws()
val esc = run_tool(default_policy(ws), new_tool_call("r", "wiki_read", _json([_kv("page_id", "../x.md")])))
expect(esc.is_error).to_equal(true)
expect(esc.content).to_contain("path traversal")
val wesc = run_tool(allow_all_policy(ws), new_tool_call("w", "wiki_write", _json([_kv("page_id", "notes/../../escape"), _kv("body", "x")])))
expect(wesc.is_error).to_equal(true)
expect(wesc.content).to_contain("path traversal")
expect(file_exists(ws + "/escape.md")).to_equal(false)
step("an absolute path outside the root is refused too")
val abs = run_tool(default_policy(ws), new_tool_call("r", "wiki_read", _json([_kv("page_id", "/etc/hostname")])))
expect(abs.is_error).to_equal(true)
expect(abs.content).to_contain("escapes the wiki root")
step("a missing page is a not-found error, not an empty success")
val missing = run_tool(default_policy(ws), new_tool_call("r", "wiki_read", _json([_kv("page_id", "nope-" + _nonce() + ".md")])))
expect(missing.is_error).to_equal(true)
expect(missing.content).to_contain("page not found")
reset_config()
```

</details>

### wiki tools: permission gating

#### denies wiki_write under the default policy and allows it with a grant

- denies wiki_write under the default policy and allows it with a grant
- default (ask, non-interactive) resolves to DENY and nothing is written
   - Expected: denied.is_error is true
   - Expected: file_exists(ws + "/wiki/" + id) is false
- read-only wiki tools stay auto-allowed under the same policy
   - Expected: ro.is_error is false
- an explicit grant for wiki_write writes the file
   - Expected: granted.is_error is false
   - Expected: read_file_text(ws + "/wiki/" + id) equals `"gated " + nonce`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("denies wiki_write under the default policy and allows it with a grant")
_configure_local()
val ws = _ws()
val nonce = _nonce()
val id = "gate_" + nonce + ".md"
step("default (ask, non-interactive) resolves to DENY and nothing is written")
val denied = run_tool(default_policy(ws), new_tool_call("w", "wiki_write", _json([_kv("page_id", id), _kv("body", "gated " + nonce)])))
expect(denied.is_error).to_equal(true)
expect(denied.content).to_contain("permission denied")
expect(file_exists(ws + "/wiki/" + id)).to_equal(false)
step("read-only wiki tools stay auto-allowed under the same policy")
val ro = run_tool(default_policy(ws), new_tool_call("s", "wiki_search", _json([_kv("query", "gated " + nonce)])))
expect(ro.is_error).to_equal(false)
step("an explicit grant for wiki_write writes the file")
val granted = run_tool(policy_with_allow(ws, ["wiki_write"]), new_tool_call("w", "wiki_write", _json([_kv("page_id", id), _kv("body", "gated " + nonce)])))
expect(granted.is_error).to_equal(false)
expect(read_file_text(ws + "/wiki/" + id)).to_equal("gated " + nonce)
reset_config()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-LLM-CARET-INFRA-003`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c58cc45ccff080db85e8872b4785e8bfc962362a23d919b373db64d865a7fe5d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c58cc45ccff080db85e8872b4785e8bfc962362a23d919b373db64d865a7fe5d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c58cc45ccff080db85e8872b4785e8bfc962362a23d919b373db64d865a7fe5d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/infra_wiki_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/infra_wiki_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/infra_wiki_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/infra_wiki_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/infra_wiki_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/infra_wiki_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/infra_wiki_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'advertises wiki_search / wiki_read / wiki_write through tool_schemas' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/infra_wiki_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses honestly with no [wiki] section' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/infra_wiki_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names the missing confluence pieces without touching the network' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
