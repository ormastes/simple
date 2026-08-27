# Bootstrap MCP Server Native Build Specification

> System tests for the deployed MCP server layout after bootstrap --deploy. The canonical MCP command-line handshake spec and fresh native smoke checker own protocol and feature-call acceptance.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap MCP Server Native Build Specification

System tests for the deployed MCP server layout after bootstrap --deploy. The canonical MCP command-line handshake spec and fresh native smoke checker own protocol and feature-call acceptance.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | REQ-MCP-CMD-002 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | doc/02_requirements/app/build/bootstrap.md |
| Plan | doc/03_plan/sys_test/mcp_cmdline_handshake.md |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/tools/bootstrap_mcp_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

System tests for the deployed MCP server layout after bootstrap --deploy.
The canonical MCP command-line handshake spec and fresh native smoke checker
own protocol and feature-call acceptance.

## Key Concepts

| Concept              | Description                                             |
|----------------------|---------------------------------------------------------|
| native-build         | Compiler command that produces a platform-native binary  |
| MCP server           | JSON-RPC stdio server implementing Model Context Proto  |
| initialize           | First JSON-RPC request a client sends to an MCP server  |
| bootstrap pipeline   | Multi-stage build: Rust seed -> Simple compiler -> self  |
| platform triple      | Target identifier e.g. x86_64-unknown-linux-gnu         |

## Behavior

- After bootstrap --deploy, both platform release binaries are executable
- After bootstrap --deploy, both native binaries have matching integrity sidecars
- After bootstrap --deploy, both bin/ launchers are executable wrappers
- Both deployed launchers complete startup checks
- The --no-mcp flag skips MCP server compilation entirely

## Related Specifications

- [CLI MCP Completeness](cli_mcp_completeness_spec.spl)
- [OS Compiler Bootstrap](os_compiler_bootstrap_spec.spl)
- [T32 MCP Lifecycle](t32_mcp_lifecycle_spec.spl)

## Scenarios

### Bootstrap MCP — binary existence

#### simple_mcp_server binary exists at platform release path

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-MCP-CMD-002
```

</details>

#### simple_lsp_mcp_server binary exists at platform release path

- simple_lsp_mcp_server binary exists at platform release path
   - Expected: file_exists(path) is true
   - Expected: rc equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("simple_lsp_mcp_server binary exists at platform release path")
val path = mcp_binary_path("simple_lsp_mcp_server")
expect(file_exists(path)).to_equal(true)
val (_, _, rc) = process_run("test", ["-x", path])
expect(rc).to_equal(0)
```

</details>

#### native MCP binaries have matching integrity sidecars

- native MCP binaries have matching integrity sidecars
   - Expected: file_exists(sidecar) is true
   - Expected: file_read(sidecar).trim() equals `file_hash_sha256(binary)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("native MCP binaries have matching integrity sidecars")
for name in ["simple_mcp_server", "simple_lsp_mcp_server"]:
    val binary = mcp_binary_path(name)
    val sidecar = binary + ".sha256"
    expect(file_exists(sidecar)).to_equal(true)
    expect(file_read(sidecar).trim()).to_equal(file_hash_sha256(binary))
```

</details>

### Bootstrap MCP — deployed launchers

#### bin/simple_mcp_server launcher exists

- bin/simple_mcp_server launcher exists
   - Expected: file_exists("bin/simple_mcp_server") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bin/simple_mcp_server launcher exists")
expect(file_exists("bin/simple_mcp_server")).to_equal(true)
```

</details>

#### bin/simple_lsp_mcp_server launcher exists

- bin/simple_lsp_mcp_server launcher exists
   - Expected: file_exists("bin/simple_lsp_mcp_server") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bin/simple_lsp_mcp_server launcher exists")
expect(file_exists("bin/simple_lsp_mcp_server")).to_equal(true)
```

</details>

#### bin/simple_mcp_server is executable

- bin/simple_mcp_server is executable
   - Expected: rc equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bin/simple_mcp_server is executable")
val (_, _, rc) = process_run("test", ["-x", "bin/simple_mcp_server"])
expect(rc).to_equal(0)
```

</details>

#### bin/simple_lsp_mcp_server is executable

- bin/simple_lsp_mcp_server is executable
   - Expected: rc equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bin/simple_lsp_mcp_server is executable")
val (_, _, rc) = process_run("test", ["-x", "bin/simple_lsp_mcp_server"])
expect(rc).to_equal(0)
```

</details>

#### deployed MCP launcher passes its native startup probe

- deployed MCP launcher passes its native startup probe
   - Expected: rc equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("deployed MCP launcher passes its native startup probe")
val (out, err, rc) = process_run("bin/simple_mcp_server", ["--probe"])
expect(rc).to_equal(0)
expect(out + err).to_contain("probe ok")
```

</details>

#### deployed MCP launcher anchors real codebase requests at the repository

- deployed MCP launcher anchors real codebase requests at the repository
   - Expected: wrapper contains `script_dir="$(CDPATH= cd "$\{script_dir}" && pwd)"`
   - Expected: wrapper contains `repo_root="$(CDPATH= cd "$\{script_dir}/.." && pwd)"`
   - Expected: wrapper contains `cd "$\{repo_root}"`
   - Expected: rc equals `0`
   - Expected: response contains `"id":"bootstrap-mcp-initialize","result"`
   - Expected: response contains `"id":"bootstrap-mcp-search","result"`
   - Expected: response contains `handle_simple_api`
   - Expected: response does not contain `"error"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("deployed MCP launcher anchors real codebase requests at the repository")
val wrapper = file_read("bin/simple_mcp_server")
expect(wrapper.contains("script_dir=\"$(CDPATH= cd \"$\{script_dir}\" && pwd)\"")).to_equal(true)
expect(wrapper.contains("repo_root=\"$(CDPATH= cd \"$\{script_dir}/..\" && pwd)\"")).to_equal(true)
expect(wrapper.contains("cd \"$\{repo_root}\"")).to_equal(true)
val initialize = "{\"jsonrpc\":\"2.0\",\"id\":\"bootstrap-mcp-initialize\",\"method\":\"initialize\",\"params\":{\"protocolVersion\":\"2025-06-18\",\"capabilities\":{},\"clientInfo\":{\"name\":\"bootstrap\",\"version\":\"1\"}}}"
val search = "{\"jsonrpc\":\"2.0\",\"id\":\"bootstrap-mcp-search\",\"method\":\"tools/call\",\"params\":{\"name\":\"simple_search\",\"arguments\":{\"query\":\"handle_simple_api\",\"kind\":\"fn\",\"scope\":\"app\"}}}"
val command = "runner=; if command -v timeout >/dev/null 2>&1; then runner='timeout 10'; elif command -v gtimeout >/dev/null 2>&1; then runner='gtimeout 10'; elif command -v perl >/dev/null 2>&1; then runner=\"perl -e 'alarm shift; exec @ARGV' 10\"; else exit 127; fi; repo_root=\"$(pwd)\"; workdir=\"$(mktemp -d)\"; trap 'rm -rf \"$workdir\"' EXIT; (cd \"$workdir\" && printf '%s\\n%s\\n' '" + initialize + "' '" + search + "' | $runner \"$repo_root/bin/simple_mcp_server\")"
val (out, err, rc) = process_run("sh", ["-c", command])
expect(rc).to_equal(0)
val response = out + err
expect(response.contains("\"id\":\"bootstrap-mcp-initialize\",\"result\"")).to_equal(true)
expect(response.contains("\"id\":\"bootstrap-mcp-search\",\"result\"")).to_equal(true)
expect(response.contains("handle_simple_api")).to_equal(true)
expect(response.contains("\"error\"")).to_equal(false)
```

</details>

#### deployed LSP MCP launcher passes correlated symbols admission

- deployed LSP MCP launcher passes correlated symbols admission
   - Expected: wrapper contains `native_hash_is_valid`
   - Expected: wrapper contains `cd "$\{repo_root}"`
   - Expected: wrapper contains `probe_timeout "$\{SIMPLE_LSP_MCP_NATIVE_PROBE_TIMEOUT:-3}"`
   - Expected: wrapper contains `&& ! grep -q '"id":"3".*"error"'`
   - Expected: wrapper contains `&& ! grep -q '"id":"3".*"isError"'`
   - Expected: wrapper contains `command failed with exit code`
   - Expected: rc equals `0`
   - Expected: response contains `"id":"bootstrap-lsp-initialize","result"`
   - Expected: response contains `"id":"bootstrap-lsp-tools","result"`
   - Expected: response contains `lsp_symbols`
   - Expected: response contains `"id":"bootstrap-lsp-symbols","result"`
   - Expected: response contains `\\"name\\":\\"log_options_help\\"`
   - Expected: response does not contain `"error"`
   - Expected: response does not contain `"isError":true`
   - Expected: response does not contain `command failed with exit code`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("deployed LSP MCP launcher passes correlated symbols admission")
val wrapper = file_read("bin/simple_lsp_mcp_server")
expect(wrapper.contains("native_hash_is_valid")).to_equal(true)
expect(wrapper.contains("cd \"$\{repo_root}\"")).to_equal(true)
expect(wrapper.contains("probe_timeout \"$\{SIMPLE_LSP_MCP_NATIVE_PROBE_TIMEOUT:-3}\"")).to_equal(true)
expect(wrapper.contains("&& ! grep -q '\"id\":\"3\".*\"error\"'")).to_equal(true)
expect(wrapper.contains("&& ! grep -q '\"id\":\"3\".*\"isError\"'")).to_equal(true)
expect(wrapper.contains("command failed with exit code")).to_equal(true)
val initialize = "{\"jsonrpc\":\"2.0\",\"id\":\"bootstrap-lsp-initialize\",\"method\":\"initialize\",\"params\":{\"protocolVersion\":\"2025-06-18\",\"capabilities\":{},\"clientInfo\":{\"name\":\"bootstrap\",\"version\":\"1\"}}}"
val tools_list = "{\"jsonrpc\":\"2.0\",\"id\":\"bootstrap-lsp-tools\",\"method\":\"tools/list\",\"params\":{}}"
val symbols = "{\"jsonrpc\":\"2.0\",\"id\":\"bootstrap-lsp-symbols\",\"method\":\"tools/call\",\"params\":{\"name\":\"lsp_symbols\",\"arguments\":{\"file\":\"src/app/simple_lsp_mcp/main.spl\"}}}"
val command = "runner=; if command -v timeout >/dev/null 2>&1; then runner='timeout 10'; elif command -v gtimeout >/dev/null 2>&1; then runner='gtimeout 10'; elif command -v perl >/dev/null 2>&1; then runner=\"perl -e 'alarm shift; exec @ARGV' 10\"; else exit 127; fi; repo_root=\"$(pwd)\"; workdir=\"$(mktemp -d)\"; trap 'rm -rf \"$workdir\"' EXIT; (cd \"$workdir\" && printf '%s\\n%s\\n%s\\n' '" + initialize + "' '" + tools_list + "' '" + symbols + "' | $runner \"$repo_root/bin/simple_lsp_mcp_server\")"
val (out, err, rc) = process_run("sh", ["-c", command])
expect(rc).to_equal(0)
val response = out + err
expect(response.contains("\"id\":\"bootstrap-lsp-initialize\",\"result\"")).to_equal(true)
expect(response.contains("\"id\":\"bootstrap-lsp-tools\",\"result\"")).to_equal(true)
expect(response.contains("lsp_symbols")).to_equal(true)
expect(response.contains("\"id\":\"bootstrap-lsp-symbols\",\"result\"")).to_equal(true)
expect(response.contains("\\\"name\\\":\\\"log_options_help\\\"")).to_equal(true)
expect(response.contains("\"error\"")).to_equal(false)
expect(response.contains("\"isError\":true")).to_equal(false)
expect(response.contains("command failed with exit code")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/app/build/bootstrap.md`
- **Plan:** `doc/03_plan/sys_test/mcp_cmdline_handshake.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-MCP-CMD-002`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `54fe9bc7f4a9e9f9a6d22a145b0e9a28eae6d1bb66c5a7c94985cd153b96399c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `54fe9bc7f4a9e9f9a6d22a145b0e9a28eae6d1bb66c5a7c94985cd153b96399c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `54fe9bc7f4a9e9f9a6d22a145b0e9a28eae6d1bb66c5a7c94985cd153b96399c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/03_system/tools/bootstrap_mcp_spec.spl
mirror: doc/06_spec/03_system/tools/bootstrap_mcp_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/bootstrap_mcp_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/bootstrap_mcp_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/bootstrap_mcp_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/bootstrap_mcp_spec.spl:95:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'simple_mcp_server binary exists at platform release path' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/tools/bootstrap_mcp_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'simple_lsp_mcp_server binary exists at platform release path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/bootstrap_mcp_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'native MCP binaries have matching integrity sidecars' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/bootstrap_mcp_spec.spl:135:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bin/simple_mcp_server launcher exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
