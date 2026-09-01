# MCP Command-Line Handshake

> System tests for every Simple-created local MCP command wrapper. Each scenario

<!-- sdn-diagram:id=mcp_cmdline_handshake_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_cmdline_handshake_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_cmdline_handshake_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_cmdline_handshake_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Command-Line Handshake

System tests for every Simple-created local MCP command wrapper. Each scenario

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

System tests for every Simple-created local MCP command wrapper. Each scenario
launches the server by command line, sends real MCP `initialize` and
`tools/list` frames over stdin, and requires a bounded response time.

## Scenarios

### MCP Command-Line Handshake

### REQ-MCP-CMD-001: local MCP wrappers answer real stdio handshakes

#### should launch simple_mcp_server and list Simple tools within the time limit

- build the exact MCP artifact with pure Stage 2
- Strictly native-build src/app/mcp/main.spl with pure Stage 2
   - Expected: build_exit equals `0`
   - Expected: file_exists(pure_simple_mcp_binary()) is true
   - Expected: build_stderr does not contain `stub fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-MCP-CMD-001
# @req REQ-SSPEC-SYSTEM
step("build the exact MCP artifact with pure Stage 2")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
step("Strictly native-build src/app/mcp/main.spl with pure Stage 2")
val (_, build_stderr, build_exit) = build_pure_simple_mcp()
expect(build_exit).to_equal(0)  # oracle: build_exit must equal 0 — authoritative contract constant
expect(file_exists(pure_simple_mcp_binary())).to_equal(true)
expect(build_stderr.contains("stub fallback")).to_equal(false)
```

</details>

#### launch the exact MCP artifact and list Simple tools within the time limit

- launch the exact MCP artifact and list Simple tools within the time limit
- Run the Stage 2-built MCP artifact with initialize and tools/list frames
- Require readiness, successful exit, bounded latency, and simple_pipe
   - Expected: probe.ok is true
   - Expected: probe.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("launch the exact MCP artifact and list Simple tools within the time limit")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
step("Run the Stage 2-built MCP artifact with initialize and tools/list frames")
val probe = mcp_cmdline_probe("simple_mcp", pure_simple_mcp_binary(), 15, 15000, "Simple MCP Server", "simple_pipe", "", "")
step("Require readiness, successful exit, bounded latency, and simple_pipe")
expect(probe.ok).to_equal(true)
expect(probe.exit_code).to_equal(0)  # oracle: probe.exit_code must equal 0 — authoritative contract constant
expect(probe.elapsed_ms).to_be_less_than(15001)
expect(probe.ready_json).to_contain("Simple MCP Server")
expect(probe.stdout).to_contain("simple_pipe")
```

</details>

#### should fail closed when t32_mcp_server native artifact is missing

- run core Simple MCP features without source or Rust fallback
- Launch the cached native Simple MCP artifact
- Check the linked SPipe surface and bounded empty search result
   - Expected: probe.ok is true
   - Expected: probe.stderr does not contain `bootstrap-only`
   - Expected: probe.stderr does not contain `mode=source`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("run core Simple MCP features without source or Rust fallback")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
step("Launch the cached native Simple MCP artifact")
val calls = (
    mcp_tool_call_frame("3", "simple_pipe", "{\"surface\":\"spipe\"}") +
    mcp_tool_call_frame("4", "simple_search", "{\"query\":\"__PURE_SIMPLE_MCP_SANITY_NO_MATCH__\",\"scope\":\"src\"}")
)
val probe = mcp_cmdline_probe("simple_mcp_features", pure_simple_mcp_binary(), 15, 15000, "Simple MCP Server", "simple_search", calls, "status: ready")
step("Check the linked SPipe surface and bounded empty search result")
expect(probe.ok).to_equal(true)
expect(probe.stdout).to_contain("spipe: linked")
expect(probe.stdout).to_contain("No results found.")
expect(probe.stderr.contains("bootstrap-only")).to_equal(false)
expect(probe.stderr.contains("mode=source")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-MCP-CMD-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dda2d8f6a8c93058860fe34f732c264fdb7845306baee1fdd111231c1814e6be`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dda2d8f6a8c93058860fe34f732c264fdb7845306baee1fdd111231c1814e6be`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dda2d8f6a8c93058860fe34f732c264fdb7845306baee1fdd111231c1814e6be`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.spl
mirror: doc/06_spec/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
