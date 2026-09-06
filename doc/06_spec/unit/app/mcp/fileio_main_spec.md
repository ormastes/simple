# Fileio Main Specification

> Tests covering FileIO Main - Parsing Helpers, FileIO Main - Safe Read, FileIO Main - Safe Write/Delete/Append, FileIO Main - Copy and Move, FileIO Main - Other Tools.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fileio Main Specification

## Scenarios

### FileIO Main - Parsing Helpers

#### parses method and params

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses method and params
   - Expected: parse_method("{\"method\":\"ping\"}") equals `ping`
   - Expected: parse_method("{\"method\":123}") equals ``
   - Expected: parse_method("{}" ) equals ``
   - Expected: params contains `"name"`
   - Expected: parse_params("{\"id\":1}") equals `{}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses method and params")
expect(parse_method("{\"method\":\"ping\"}")).to_equal("ping")
expect(parse_method("{\"method\":123}")).to_equal("")
expect(parse_method("{}" )).to_equal("")
val json = "{\"params\":{\"name\":\"safe_read\",\"arguments\":{\"path\":\"x\"}}}"
val params = parse_params(json)
expect(params.contains("\"name\"" )).to_equal(true)
expect(parse_params("{\"id\":1}")).to_equal("{}")
```

</details>

#### parses arguments and handles missing values

- parses arguments and handles missing values
   - Expected: server.parse_arg("{\"path\":\"/tmp/x\"}", "path") equals `/tmp/x`
   - Expected: server.parse_arg("{\"path\":123}", "path") equals ``
   - Expected: server.parse_arg("{\"other\":\"x\"}", "path") equals ``
   - Expected: server.parse_path_arg("{\"path\":\"/tmp/y\"}") equals `/tmp/y`
   - Expected: server.parse_content_arg("{\"content\":\"hi\"}") equals `hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses arguments and handles missing values")
val server = setup_server()
expect(server.parse_arg("{\"path\":\"/tmp/x\"}", "path")).to_equal("/tmp/x")
expect(server.parse_arg("{\"path\":123}", "path")).to_equal("")
expect(server.parse_arg("{\"other\":\"x\"}", "path")).to_equal("")
expect(server.parse_path_arg("{\"path\":\"/tmp/y\"}")).to_equal("/tmp/y")
expect(server.parse_content_arg("{\"content\":\"hi\"}")).to_equal("hi")
```

</details>

#### formats file lists

- formats file lists
   - Expected: server.files_to_json([]) equals `[]`
   - Expected: json contains `"a"`
   - Expected: json contains `"b"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats file lists")
val server = setup_server()
expect(server.files_to_json([])).to_equal("[]")
val json = server.files_to_json(["a", "b"])
expect(json.contains("\"a\"")).to_equal(true)
expect(json.contains("\"b\"")).to_equal(true)
```

</details>

#### lists tools

- lists tools
   - Expected: resp contains `safe_read`
   - Expected: resp contains `safe_write`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists tools")
val resp = handle_tools_list("1")
expect(resp.contains("safe_read")).to_equal(true)
expect(resp.contains("safe_write")).to_equal(true)
```

</details>

### FileIO Main - Safe Read

#### reads allowed files

- reads allowed files
   - Expected: resp contains `success`
   - Expected: resp contains `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads allowed files")
val server = setup_server()
val path = "/tmp/mcp_allow_read.txt"
write_text(path, "hello")
val resp = server.tool_safe_read("{\"path\":\"{path}\"}")
expect(resp.contains("success")).to_equal(true)
expect(resp.contains("hello")).to_equal(true)
```

</details>

#### denies protected reads

- denies protected reads
   - Expected: resp contains `Read denied`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("denies protected reads")
val server = setup_server()
val resp = server.tool_safe_read("{\"path\":\"/tmp/mcp_deny.txt\"}")
expect(resp.contains("Read denied")).to_equal(true)
```

</details>

#### reads redirected files

- reads redirected files
   - Expected: resp contains `temp-data`
   - Expected: comparison.status equals `EvidenceStatus.passed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads redirected files")
val server = setup_server()
shell("mkdir -p tmp/fileio_temp")
write_text("tmp/fileio_temp/mcp_redirect.txt", "temp-data")
val resp = server.tool_safe_read("{\"path\":\"/tmp/mcp_redirect.txt\"}")
expect(resp.contains("temp-data")).to_equal(true)

val redirect_readback = read_text("tmp/fileio_temp/mcp_redirect.txt")
val capture = UntypedCapture(label: "fileio-main-redirect-readback", raw_value: redirect_readback, source_kind: "log_line")
val evidence = untyped_capture_to_canonical(capture, "fileio_main_spec/redirect-readback")
val comparison = compare_evidence(evidence, oracle_spec("fileio_main_spec/redirect-readback", [
    check_exact("value", "temp-data")
]))
expect(comparison.status).to_equal(EvidenceStatus.passed)
```

</details>

#### reads atomic-protected files

- reads atomic-protected files
   - Expected: resp contains `atomic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads atomic-protected files")
val server = setup_server()
val path = "/tmp/mcp_atomic.sdn"
write_text(path, "atomic")
val resp = server.tool_safe_read("{\"path\":\"{path}\"}")
expect(resp.contains("atomic")).to_equal(true)
```

</details>

#### handles missing path

- handles missing path
   - Expected: resp contains `Missing 'path'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles missing path")
val server = setup_server()
val resp = server.tool_safe_read("{\"content\":\"x\"}")
expect(resp.contains("Missing 'path'")).to_equal(true)
```

</details>

### FileIO Main - Safe Write/Delete/Append

#### writes allowed files

- writes allowed files
   - Expected: resp contains `success`
   - Expected: read_text(path) contains `hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writes allowed files")
val server = setup_server()
val path = "/tmp/mcp_allow_write.txt"
val resp = server.tool_safe_write("{\"path\":\"{path}\",\"content\":\"hi\"}")
expect(resp.contains("success")).to_equal(true)
expect(read_text(path).contains("hi")).to_equal(true)
```

</details>

#### writes redirected files to temp

- writes redirected files to temp
   - Expected: resp contains `temp`
   - Expected: read_text(temp_path) contains `temp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writes redirected files to temp")
val server = setup_server()
val path = "/tmp/mcp_redirect.txt"
val temp_path = server.temp_manager.get_temp_path(path)
val resp = server.tool_safe_write("{\"path\":\"{path}\",\"content\":\"temp\"}")
expect(resp.contains("temp")).to_equal(true)
expect(read_text(temp_path).contains("temp")).to_equal(true)
```

</details>

#### rejects atomic writes when required

- rejects atomic writes when required
   - Expected: resp contains `Atomic write required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects atomic writes when required")
val server = setup_server()
val resp = server.tool_safe_write("{\"path\":\"/tmp/mcp_atomic.sdn\",\"content\":\"x\"}")
expect(resp.contains("Atomic write required")).to_equal(true)
```

</details>

#### rejects denied writes

- rejects denied writes
   - Expected: resp contains `Write denied`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects denied writes")
val server = setup_server()
val resp = server.tool_safe_write("{\"path\":\"/tmp/mcp_deny.txt\",\"content\":\"x\"}")
expect(resp.contains("Write denied")).to_equal(true)
```

</details>

#### deletes allowed files

- deletes allowed files
   - Expected: resp contains `success`
   - Expected: file_exists(path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deletes allowed files")
val server = setup_server()
val path = "/tmp/mcp_allow_delete.txt"
write_text(path, "bye")
val resp = server.tool_safe_delete("{\"path\":\"{path}\"}")
expect(resp.contains("success")).to_equal(true)
expect(file_exists(path)).to_equal(false)
```

</details>

#### deletes redirected temp files

- deletes redirected temp files
   - Expected: resp contains `success`
   - Expected: file_exists(temp_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deletes redirected temp files")
val server = setup_server()
val path = "/tmp/mcp_redirect.txt"
val temp_path = server.temp_manager.get_temp_path(path)
write_text(temp_path, "bye")
val resp = server.tool_safe_delete("{\"path\":\"{path}\"}")
expect(resp.contains("success")).to_equal(true)
expect(file_exists(temp_path)).to_equal(false)
```

</details>

#### rejects denied delete

- rejects denied delete
   - Expected: resp contains `Delete denied`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects denied delete")
val server = setup_server()
val resp = server.tool_safe_delete("{\"path\":\"/tmp/mcp_deny.txt\"}")
expect(resp.contains("Delete denied")).to_equal(true)
```

</details>

#### rejects atomic delete

- rejects atomic delete
   - Expected: resp contains `Cannot delete atomic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects atomic delete")
val server = setup_server()
val resp = server.tool_safe_delete("{\"path\":\"/tmp/mcp_atomic.sdn\"}")
expect(resp.contains("Cannot delete atomic")).to_equal(true)
```

</details>

#### appends to allowed files

- appends to allowed files
   - Expected: resp contains `success`
   - Expected: read_text(path) contains `ab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("appends to allowed files")
val server = setup_server()
val path = "/tmp/mcp_allow_append.txt"
write_text(path, "a")
val resp = server.tool_safe_append("{\"path\":\"{path}\",\"content\":\"b\"}")
expect(resp.contains("success")).to_equal(true)
expect(read_text(path).contains("ab")).to_equal(true)
```

</details>

#### appends to redirected files

- appends to redirected files
   - Expected: resp contains `temp`
   - Expected: read_text(temp_path) contains `ab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("appends to redirected files")
val server = setup_server()
val path = "/tmp/mcp_redirect.txt"
val temp_path = server.temp_manager.get_temp_path(path)
write_text(temp_path, "a")
val resp = server.tool_safe_append("{\"path\":\"{path}\",\"content\":\"b\"}")
expect(resp.contains("temp")).to_equal(true)
expect(read_text(temp_path).contains("ab")).to_equal(true)
```

</details>

#### rejects append on atomic

- rejects append on atomic
   - Expected: resp contains `Atomic write required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects append on atomic")
val server = setup_server()
val resp = server.tool_safe_append("{\"path\":\"/tmp/mcp_atomic.sdn\",\"content\":\"x\"}")
expect(resp.contains("Atomic write required")).to_equal(true)
```

</details>

#### rejects append on denied

- rejects append on denied
   - Expected: resp contains `Append denied`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects append on denied")
val server = setup_server()
val resp = server.tool_safe_append("{\"path\":\"/tmp/mcp_deny.txt\",\"content\":\"x\"}")
expect(resp.contains("Append denied")).to_equal(true)
```

</details>

### FileIO Main - Copy and Move

#### rejects copy when source denied

- rejects copy when source denied
   - Expected: resp contains `Source read denied`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects copy when source denied")
val server = setup_server()
val resp = server.tool_safe_copy("{\"src\":\"/tmp/mcp_deny.txt\",\"dest\":\"/tmp/mcp_allow_copy.txt\"}")
expect(resp.contains("Source read denied")).to_equal(true)
```

</details>

#### copies to allowed destination

- copies to allowed destination
   - Expected: resp contains `success`
   - Expected: read_text(dest) contains `copy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("copies to allowed destination")
val server = setup_server()
val src = "/tmp/mcp_src_copy.txt"
val dest = "/tmp/mcp_allow_copy.txt"
write_text(src, "copy")
val resp = server.tool_safe_copy("{\"src\":\"{src}\",\"dest\":\"{dest}\"}")
expect(resp.contains("success")).to_equal(true)
expect(read_text(dest).contains("copy")).to_equal(true)
```

</details>

#### copies to redirected destination

- copies to redirected destination
   - Expected: resp contains `temp`
   - Expected: read_text(temp_dest) contains `copy2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("copies to redirected destination")
val server = setup_server()
val src = "/tmp/mcp_src_copy2.txt"
val dest = "/tmp/mcp_redirect_dest.txt"
write_text(src, "copy2")
val temp_dest = server.temp_manager.get_temp_path(dest)
val resp = server.tool_safe_copy("{\"src\":\"{src}\",\"dest\":\"{dest}\"}")
expect(resp.contains("temp")).to_equal(true)
expect(read_text(temp_dest).contains("copy2")).to_equal(true)
```

</details>

#### rejects copy when dest denied

- rejects copy when dest denied
   - Expected: resp contains `Destination write denied`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects copy when dest denied")
val server = setup_server()
val resp = server.tool_safe_copy("{\"src\":\"/tmp/mcp_src_copy.txt\",\"dest\":\"/tmp/mcp_deny_dest.txt\"}")
expect(resp.contains("Destination write denied")).to_equal(true)
```

</details>

#### rejects copy when dest atomic

- rejects copy when dest atomic
   - Expected: resp contains `Atomic write required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects copy when dest atomic")
val server = setup_server()
val resp = server.tool_safe_copy("{\"src\":\"/tmp/mcp_src_copy.txt\",\"dest\":\"/tmp/mcp_atomic.sdn\"}")
expect(resp.contains("Atomic write required")).to_equal(true)
```

</details>

#### rejects move when source denied

- rejects move when source denied
   - Expected: resp contains `Source delete denied`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects move when source denied")
val server = setup_server()
val resp = server.tool_safe_move("{\"src\":\"/tmp/mcp_deny.txt\",\"dest\":\"/tmp/mcp_allow_move.txt\"}")
expect(resp.contains("Source delete denied")).to_equal(true)
```

</details>

#### moves to allowed destination

- moves to allowed destination
   - Expected: resp contains `success`
   - Expected: file_exists(src) is false
   - Expected: read_text(dest) contains `move`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("moves to allowed destination")
val server = setup_server()
val src = "/tmp/mcp_src_move.txt"
val dest = "/tmp/mcp_allow_move.txt"
write_text(src, "move")
val resp = server.tool_safe_move("{\"src\":\"{src}\",\"dest\":\"{dest}\"}")
expect(resp.contains("success")).to_equal(true)
expect(file_exists(src)).to_equal(false)
expect(read_text(dest).contains("move")).to_equal(true)
```

</details>

#### moves to redirected destination

- moves to redirected destination
   - Expected: resp contains `temp`
   - Expected: read_text(temp_dest) contains `move2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("moves to redirected destination")
val server = setup_server()
val src = "/tmp/mcp_src_move2.txt"
val dest = "/tmp/mcp_redirect_dest.txt"
write_text(src, "move2")
val temp_dest = server.temp_manager.get_temp_path(dest)
val resp = server.tool_safe_move("{\"src\":\"{src}\",\"dest\":\"{dest}\"}")
expect(resp.contains("temp")).to_equal(true)
expect(read_text(temp_dest).contains("move2")).to_equal(true)
```

</details>

#### rejects move when dest denied

- rejects move when dest denied
   - Expected: resp contains `Destination write denied`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects move when dest denied")
val server = setup_server()
val resp = server.tool_safe_move("{\"src\":\"/tmp/mcp_src_move.txt\",\"dest\":\"/tmp/mcp_deny_dest.txt\"}")
expect(resp.contains("Destination write denied")).to_equal(true)
```

</details>

#### rejects move when dest atomic

- rejects move when dest atomic
   - Expected: resp contains `Atomic write required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects move when dest atomic")
val server = setup_server()
val resp = server.tool_safe_move("{\"src\":\"/tmp/mcp_src_move.txt\",\"dest\":\"/tmp/mcp_atomic.sdn\"}")
expect(resp.contains("Atomic write required")).to_equal(true)
```

</details>

### FileIO Main - Other Tools

#### lists protected files and checks protection

- lists protected files and checks protection
   - Expected: list_resp contains `success`
   - Expected: info_resp contains `Deny`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists protected files and checks protection")
val server = setup_server()
val list_resp = server.tool_list_protected_files("{}")
expect(list_resp.contains("success")).to_equal(true)
val info_resp = server.tool_check_protection("{\"path\":\"/tmp/mcp_deny.txt\"}")
expect(info_resp.contains("Deny")).to_equal(true)
```

</details>

#### adds protection rules and handles missing pattern

- adds protection rules and handles missing pattern
   - Expected: missing contains `Missing 'pattern'`
   - Expected: resp contains `success`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds protection rules and handles missing pattern")
val server = setup_server()
val missing = server.tool_add_protection_rule("{}")
expect(missing.contains("Missing 'pattern'")).to_equal(true)
val rules = [
    "{\"pattern\":\"/tmp/a\",\"type\":\"exact\",\"action\":\"deny\",\"reason\":\"r\"}",
    "{\"pattern\":\"/tmp/b\",\"type\":\"glob\",\"action\":\"protect\",\"reason\":\"r\"}",
    "{\"pattern\":\"/tmp/c\",\"type\":\"regex\",\"action\":\"redirect\",\"reason\":\"r\"}",
    "{\"pattern\":\"/tmp/d\",\"type\":\"unknown\",\"action\":\"atomic\",\"reason\":\"r\"}",
    "{\"pattern\":\"/tmp/e\",\"type\":\"exact\",\"action\":\"allow\",\"reason\":\"r\"}",
    "{\"pattern\":\"/tmp/f\",\"type\":\"exact\",\"action\":\"unknown\",\"reason\":\"r\"}"
]
for r in rules:
    val resp = server.tool_add_protection_rule(r)
    expect(resp.contains("success")).to_equal(true)
```

</details>

#### manages temp files

- manages temp files
   - Expected: list_resp contains `success`
   - Expected: dir_resp contains `tmp/fileio_temp`
   - Expected: clean_resp contains `success`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("manages temp files")
val server = setup_server()
val temp_path = server.temp_manager.get_temp_path("/tmp/mcp_temp.txt")
write_text(temp_path, "temp")
val list_resp = server.tool_list_temp_files("{}")
expect(list_resp.contains("success")).to_equal(true)
val dir_resp = server.tool_get_temp_dir("{}")
expect(dir_resp.contains("tmp/fileio_temp")).to_equal(true)
val clean_resp = server.tool_cleanup_temp("{}")
expect(clean_resp.contains("success")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp/fileio_main_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FileIO Main - Parsing Helpers, FileIO Main - Safe Read, FileIO Main - Safe Write/Delete/Append, FileIO Main - Copy and Move, FileIO Main - Other Tools.
- FileIO Main - Parsing Helpers
- FileIO Main - Safe Read
- FileIO Main - Safe Write/Delete/Append
- FileIO Main - Copy and Move
- FileIO Main - Other Tools

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4343c9c994965cc919dc8b5b46049b94a242bff0b914ded869a9e770d615ea80`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4343c9c994965cc919dc8b5b46049b94a242bff0b914ded869a9e770d615ea80`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4343c9c994965cc919dc8b5b46049b94a242bff0b914ded869a9e770d615ea80`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp/fileio_main_spec.spl
mirror: doc/06_spec/unit/app/mcp/fileio_main_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp/fileio_main_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp/fileio_main_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp/fileio_main_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses method and params' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp/fileio_main_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses arguments and handles missing values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp/fileio_main_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats file lists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
