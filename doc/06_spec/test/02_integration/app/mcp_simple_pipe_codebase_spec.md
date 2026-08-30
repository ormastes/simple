# MCP Simple Pipe Codebase Execution Specification

> This focused check proves `simple_pipe surface=codebase` no longer duplicates language-neutral codebase/context behavior in Simple MCP. It hands callers to SPipe MCP, while Simple-specific code search remains local.

<!-- sdn-diagram:id=mcp_simple_pipe_codebase_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_simple_pipe_codebase_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_simple_pipe_codebase_spec -> std
mcp_simple_pipe_codebase_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_simple_pipe_codebase_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Simple Pipe Codebase Execution Specification

This focused check proves `simple_pipe surface=codebase` no longer duplicates language-neutral codebase/context behavior in Simple MCP. It hands callers to SPipe MCP, while Simple-specific code search remains local.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/llm_tooling_context_ponytail_mimic.md |
| Source | `test/02_integration/app/mcp_simple_pipe_codebase_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This focused check proves `simple_pipe surface=codebase` no longer duplicates
language-neutral codebase/context behavior in Simple MCP. It hands callers to
SPipe MCP, while Simple-specific code search remains local.

**Requirements:** doc/02_requirements/feature/llm_tooling_context_ponytail_mimic.md

## Scenarios

### MCP simple_pipe codebase

#### hands codebase context to SPipe MCP

- dir create all


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dir_create_all("build/test/mcp_simple_pipe_codebase")
val source_path = "src/app/mcp/main_lazy_query_tools.spl"
val db_path = "build/test/mcp_simple_pipe_codebase/codebase.db"
val index_output = context_sql_index_packs([source_path], "ctx", db_path, "text")
expect(index_output).to_contain("status: ready")

val args = "{\"surface\":\"codebase\",\"sql\":\"true\",\"query\":\"handle_simple_pipe\",\"db\":\"" + db_path + "\",\"requester\":\"" + source_path + "\",\"format\":\"text\"}"
val response = dispatch_tool_content("simple_pipe", args)
expect(response).to_contain("status: moved")
expect(response).to_contain("owner: spipe-mcp")
expect(response).to_contain("server: bin/spipe_mcp_server")
expect(response).to_contain("query: handle_simple_pipe")
expect(response).to_contain("getCodebase")
expect(response).to_contain("saveCodebase")
```

</details>

#### keeps Simple source search local

- dir create all
- file write
- paths = paths push


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dir_create_all("build/test/mcp_simple_pipe_codebase/broad")
var paths: [text] = []
var i = 0
while i < 60:
    val path = "build/test/mcp_simple_pipe_codebase/broad/broad_" + str(i) + ".spl"
    file_write(path, "fn broad_marker_" + str(i) + "() -> text:\n    \"handle_simple_pipe broad marker\"\n")
    paths = paths.push(path)
    i = i + 1
val db_path = "build/test/mcp_simple_pipe_codebase/broad.db"
val index_output = context_sql_index_packs(paths, "ctx", db_path, "text")
expect(index_output).to_contain("status: ready")

val args = "{\"surface\":\"search\",\"query\":\"handle_simple_pipe\",\"requester\":\"src/app/mcp/main_lazy_query_tools.spl\",\"format\":\"text\"}"
val response = dispatch_tool_content("simple_pipe", args)
expect(response).to_contain("-- simple_search query=handle_simple_pipe")
expect(response).to_contain("handle_simple_pipe")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/llm_tooling_context_ponytail_mimic.md](doc/02_requirements/feature/llm_tooling_context_ponytail_mimic.md)


</details>
