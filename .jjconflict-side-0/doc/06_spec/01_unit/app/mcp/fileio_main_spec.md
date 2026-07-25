# Fileio Main Specification

> <details>

<!-- sdn-diagram:id=fileio_main_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fileio_main_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fileio_main_spec -> std
fileio_main_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fileio_main_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fileio Main Specification

## Scenarios

### FileIO Main - Parsing Helpers

#### parses method and params

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = setup_server()
expect(server.parse_arg("{\"path\":\"/tmp/x\"}", "path")).to_equal("/tmp/x")
expect(server.parse_arg("{\"path\":123}", "path")).to_equal("")
expect(server.parse_arg("{\"other\":\"x\"}", "path")).to_equal("")
expect(server.parse_path_arg("{\"path\":\"/tmp/y\"}")).to_equal("/tmp/y")
expect(server.parse_content_arg("{\"content\":\"hi\"}")).to_equal("hi")
```

</details>

#### formats file lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = setup_server()
expect(server.files_to_json([])).to_equal("[]")
val json = server.files_to_json(["a", "b"])
expect(json.contains("\"a\"")).to_equal(true)
expect(json.contains("\"b\"")).to_equal(true)
```

</details>

#### lists tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = handle_tools_list("1")
expect(resp.contains("safe_read")).to_equal(true)
expect(resp.contains("safe_write")).to_equal(true)
```

</details>

### FileIO Main - Safe Read

#### reads allowed files

1. write text
   - Expected: resp contains `success`
   - Expected: resp contains `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = setup_server()
val path = "/tmp/mcp_allow_read.txt"
write_text(path, "hello")
val resp = server.tool_safe_read("{\"path\":\"{path}\"}")
expect(resp.contains("success")).to_equal(true)
expect(resp.contains("hello")).to_equal(true)
```

</details>

#### denies protected reads

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = setup_server()
val resp = server.tool_safe_read("{\"path\":\"/tmp/mcp_deny.txt\"}")
expect(resp.contains("Read denied")).to_equal(true)
```

</details>

#### reads redirected files

1. shell
2. write text
   - Expected: resp contains `temp-data`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = setup_server()
shell("mkdir -p tmp/fileio_temp")
write_text("tmp/fileio_temp/mcp_redirect.txt", "temp-data")
val resp = server.tool_safe_read("{\"path\":\"/tmp/mcp_redirect.txt\"}")
expect(resp.contains("temp-data")).to_equal(true)
```

</details>

#### reads atomic-protected files

1. write text
   - Expected: resp contains `atomic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = setup_server()
val path = "/tmp/mcp_atomic.sdn"
write_text(path, "atomic")
val resp = server.tool_safe_read("{\"path\":\"{path}\"}")
expect(resp.contains("atomic")).to_equal(true)
```

</details>

#### handles missing path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = setup_server()
val resp = server.tool_safe_read("{\"content\":\"x\"}")
expect(resp.contains("Missing 'path'")).to_equal(true)
```

</details>

### FileIO Main - Safe Write/Delete/Append

#### writes allowed files

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = setup_server()
val path = "/tmp/mcp_allow_write.txt"
val resp = server.tool_safe_write("{\"path\":\"{path}\",\"content\":\"hi\"}")
expect(resp.contains("success")).to_equal(true)
expect(read_text(path).contains("hi")).to_equal(true)
```

</details>

#### writes redirected files to temp

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = setup_server()
val path = "/tmp/mcp_redirect.txt"
val temp_path = server.temp_manager.get_temp_path(path)
val resp = server.tool_safe_write("{\"path\":\"{path}\",\"content\":\"temp\"}")
expect(resp.contains("temp")).to_equal(true)
expect(read_text(temp_path).contains("temp")).to_equal(true)
```

</details>

#### rejects atomic writes when required

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = setup_server()
val resp = server.tool_safe_write("{\"path\":\"/tmp/mcp_atomic.sdn\",\"content\":\"x\"}")
expect(resp.contains("Atomic write required")).to_equal(true)
```

</details>

#### rejects denied writes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = setup_server()
val resp = server.tool_safe_write("{\"path\":\"/tmp/mcp_deny.txt\",\"content\":\"x\"}")
expect(resp.contains("Write denied")).to_equal(true)
```

</details>

#### deletes allowed files

1. write text
   - Expected: resp contains `success`
   - Expected: file_exists(path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = setup_server()
val path = "/tmp/mcp_allow_delete.txt"
write_text(path, "bye")
val resp = server.tool_safe_delete("{\"path\":\"{path}\"}")
expect(resp.contains("success")).to_equal(true)
expect(file_exists(path)).to_equal(false)
```

</details>

#### deletes redirected temp files

1. write text
   - Expected: resp contains `success`
   - Expected: file_exists(temp_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = setup_server()
val resp = server.tool_safe_delete("{\"path\":\"/tmp/mcp_deny.txt\"}")
expect(resp.contains("Delete denied")).to_equal(true)
```

</details>

#### rejects atomic delete

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = setup_server()
val resp = server.tool_safe_delete("{\"path\":\"/tmp/mcp_atomic.sdn\"}")
expect(resp.contains("Cannot delete atomic")).to_equal(true)
```

</details>

#### appends to allowed files

1. write text
   - Expected: resp contains `success`
   - Expected: read_text(path) contains `ab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = setup_server()
val path = "/tmp/mcp_allow_append.txt"
write_text(path, "a")
val resp = server.tool_safe_append("{\"path\":\"{path}\",\"content\":\"b\"}")
expect(resp.contains("success")).to_equal(true)
expect(read_text(path).contains("ab")).to_equal(true)
```

</details>

#### appends to redirected files

1. write text
   - Expected: resp contains `temp`
   - Expected: read_text(temp_path) contains `ab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = setup_server()
val resp = server.tool_safe_append("{\"path\":\"/tmp/mcp_atomic.sdn\",\"content\":\"x\"}")
expect(resp.contains("Atomic write required")).to_equal(true)
```

</details>

#### rejects append on denied

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = setup_server()
val resp = server.tool_safe_append("{\"path\":\"/tmp/mcp_deny.txt\",\"content\":\"x\"}")
expect(resp.contains("Append denied")).to_equal(true)
```

</details>

### FileIO Main - Copy and Move

#### rejects copy when source denied

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = setup_server()
val resp = server.tool_safe_copy("{\"src\":\"/tmp/mcp_deny.txt\",\"dest\":\"/tmp/mcp_allow_copy.txt\"}")
expect(resp.contains("Source read denied")).to_equal(true)
```

</details>

#### copies to allowed destination

1. write text
   - Expected: resp contains `success`
   - Expected: read_text(dest) contains `copy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. write text
   - Expected: resp contains `temp`
   - Expected: read_text(temp_dest) contains `copy2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = setup_server()
val resp = server.tool_safe_copy("{\"src\":\"/tmp/mcp_src_copy.txt\",\"dest\":\"/tmp/mcp_deny_dest.txt\"}")
expect(resp.contains("Destination write denied")).to_equal(true)
```

</details>

#### rejects copy when dest atomic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = setup_server()
val resp = server.tool_safe_copy("{\"src\":\"/tmp/mcp_src_copy.txt\",\"dest\":\"/tmp/mcp_atomic.sdn\"}")
expect(resp.contains("Atomic write required")).to_equal(true)
```

</details>

#### rejects move when source denied

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = setup_server()
val resp = server.tool_safe_move("{\"src\":\"/tmp/mcp_deny.txt\",\"dest\":\"/tmp/mcp_allow_move.txt\"}")
expect(resp.contains("Source delete denied")).to_equal(true)
```

</details>

#### moves to allowed destination

1. write text
   - Expected: resp contains `success`
   - Expected: file_exists(src) is false
   - Expected: read_text(dest) contains `move`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. write text
   - Expected: resp contains `temp`
   - Expected: read_text(temp_dest) contains `move2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = setup_server()
val resp = server.tool_safe_move("{\"src\":\"/tmp/mcp_src_move.txt\",\"dest\":\"/tmp/mcp_deny_dest.txt\"}")
expect(resp.contains("Destination write denied")).to_equal(true)
```

</details>

#### rejects move when dest atomic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = setup_server()
val resp = server.tool_safe_move("{\"src\":\"/tmp/mcp_src_move.txt\",\"dest\":\"/tmp/mcp_atomic.sdn\"}")
expect(resp.contains("Atomic write required")).to_equal(true)
```

</details>

### FileIO Main - Other Tools

#### lists protected files and checks protection

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = setup_server()
val list_resp = server.tool_list_protected_files("{}")
expect(list_resp.contains("success")).to_equal(true)
val info_resp = server.tool_check_protection("{\"path\":\"/tmp/mcp_deny.txt\"}")
expect(info_resp.contains("Deny")).to_equal(true)
```

</details>

#### adds protection rules and handles missing pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. write text
   - Expected: list_resp contains `success`
   - Expected: dir_resp contains `tmp/fileio_temp`
   - Expected: clean_resp contains `success`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/mcp/fileio_main_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
