# caret_tools_mcp_system_spec

> Purpose: Prove that LLM Caret's infrastructure tools are reachable from any

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# caret_tools_mcp_system_spec

Purpose: Prove that LLM Caret's infrastructure tools are reachable from any

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/mcp/caret_tools_mcp_system_spec.spl` |
| Updated | 2026-08-25 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that LLM Caret's infrastructure tools are reachable from any
MCP client over the real stdio transport: the MCP server
(`src/app/mcp/main.spl`) is spawned as a child process, driven with
newline-delimited JSON-RPC, and must advertise the nine `caret_*` tools,
answer `caret_wiki_search` against the LOCAL wiki backend with a real hit,
DENY `caret_wiki_write` without `confirm: true`, and write the page with it.
Every write is verified on disk (absolute oracle: a nonce'd body), never by
trusting the reply text alone.
Audience: MCP maintainers, llm_caret maintainers, Claude Code / Codex users
wiring `.mcp.json`.

## Harness
Same shape as `mcp_stdio_contract_spec.spl`: `cat <input> | timeout N
bin/simple run src/app/mcp/main.spl`, stdout captured. The child env carries
`SIMPLE_MCP_TOOL_SET=all` (the default "auto" set serves the 3-tool core list
on the first tools/list, which would hide the caret names) and
`LLM_CARET_CONFIG=<llm_caret.sdn with [wiki] backend: local>`. The server
runs each caret_* call in a one-shot child (`src/app/llm_caret/tool_cli.spl`)
so its own startup path never imports the caret module graph.

## Scenarios

### caret tools over MCP stdio: discovery

#### initialize succeeds and tools/list advertises all nine caret_* tools with confirm semantics

- initialize answered with serverInfo on id 1
- tools/list on id 2 names every caret_* tool
- mutating caret tools document the confirm requirement in their schema


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nonce = _nonce()
_prepare(nonce)
val out = _send(_init() + _tools_list("2"), "300")
step("initialize answered with serverInfo on id 1")
val init = _response_line(out, "1")
assert_not_equal(init, "")
expect(init).to_contain("serverInfo")
step("tools/list on id 2 names every caret_* tool")
val list = _response_line(out, "2")
assert_not_equal(list, "")
for name in CARET_TOOLS:
    expect(list).to_contain("\"name\":\"" + name + "\"")
step("mutating caret tools document the confirm requirement in their schema")
expect(list).to_contain("caret_wiki_write\",\"description\":\"[caret] Create or update a wiki page. MUTATING: denied unless confirm is true")
expect(list).to_contain("\"confirm\":{\"type\":\"string\",\"description\":\"Must be true: this tool is MUTATING and is denied without it\"}")
```

</details>

### caret tools over MCP stdio: local wiki backend

#### caret_wiki_search returns a real hit for a seeded page

- the hit names the seeded page id, title and file url (absolute oracle: the nonce)
   - Expected: resp does not contain `"isError":true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nonce = _nonce()
val seed = _prepare(nonce)
val out = _send(_init() + _call("3", "caret_wiki_search", "{\"query\":\"MCP-SEED-BODY " + nonce + "\"}"), "300")
val resp = _response_line(out, "3")
assert_not_equal(resp, "")
step("the hit names the seeded page id, title and file url (absolute oracle: the nonce)")
expect(resp.contains("\"isError\":true")).to_equal(false)
expect(resp).to_contain("seed_" + nonce + ".md\\tSeed " + nonce + "\\tfile://" + seed)
```

</details>

#### caret_wiki_write is denied without confirm and writes the page with confirm: true

- without confirm: an isError result naming the confirm requirement, and no file on disk
- with confirm: true the page is created and the disk holds the exact body
   - Expected: ok does not contain `"isError":true`
   - Expected: file_exists(_wiki_dir() + "/" + page) is true
   - Expected: read_file_text(_wiki_dir() + "/" + page) equals `body`
- caret_wiki_read (read-only, no confirm needed) returns the body
   - Expected: read does not contain `"isError":true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nonce = _nonce()
_prepare(nonce)
val page = "mcp_written_" + nonce + ".md"
val body = "written over mcp " + nonce
val msgs = _init() +
    _call("4", "caret_wiki_write", "{\"page_id\":\"" + page + "\",\"body\":\"" + body + "\"}") +
    _call("5", "caret_wiki_write", "{\"page_id\":\"" + page + "\",\"body\":\"" + body + "\",\"confirm\":true}") +
    _call("6", "caret_wiki_read", "{\"page_id\":\"" + page + "\"}")
val out = _send(msgs, "400")
step("without confirm: an isError result naming the confirm requirement, and no file on disk")
val denied = _response_line(out, "4")
assert_not_equal(denied, "")
expect(denied).to_contain("\"isError\":true")
expect(denied).to_contain("MUTATING and was denied")
expect(denied).to_contain("confirm")
step("with confirm: true the page is created and the disk holds the exact body")
val ok = _response_line(out, "5")
assert_not_equal(ok, "")
expect(ok.contains("\"isError\":true")).to_equal(false)
expect(ok).to_contain("created " + page)
expect(file_exists(_wiki_dir() + "/" + page)).to_equal(true)
expect(read_file_text(_wiki_dir() + "/" + page)).to_equal(body)
step("caret_wiki_read (read-only, no confirm needed) returns the body")
val read = _response_line(out, "6")
assert_not_equal(read, "")
expect(read.contains("\"isError\":true")).to_equal(false)
expect(read).to_contain(body)
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
