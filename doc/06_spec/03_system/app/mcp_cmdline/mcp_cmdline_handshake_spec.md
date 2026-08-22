# MCP Command-Line Handshake

> Verifies the mcp cmdline handshake behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Command-Line Handshake

Verifies the mcp cmdline handshake behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/app/build/bootstrap.md |
| Plan | doc/03_plan/sys_test/mcp_cmdline_handshake.md |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the mcp cmdline handshake behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Pure-Simple MCP Launch and Handshake

### REQ-MCP-CMD-001: pure-Simple MCP answers real stdio handshakes

#### should build the exact MCP artifact with pure Stage 2

- Verify: should build the exact MCP artifact with pure Stage 2
- Strictly native-build src/app/mcp/main.spl with pure Stage 2
   - Expected: build_exit equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: file_exists(pure_simple_mcp_binary()) is true
   - Expected: build_stderr does not contain `stub fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MCP-CMD-001
step("Verify: should build the exact MCP artifact with pure Stage 2")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Strictly native-build src/app/mcp/main.spl with pure Stage 2")
val (_, build_stderr, build_exit) = build_pure_simple_mcp()
expect(build_exit).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(file_exists(pure_simple_mcp_binary())).to_equal(true)
expect(build_stderr.contains("stub fallback")).to_equal(false)
```

</details>

#### should launch the exact MCP artifact and list Simple tools within the time limit

- Verify: should launch the exact MCP artifact and list Simple tools within the time limit
- Run the Stage 2-built MCP artifact with initialize and tools/list frames
- Require readiness, successful exit, bounded latency, and simple_pipe
   - Expected: probe.ok is true
   - Expected: probe.exit_code equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MCP-CMD-001
step("Verify: should launch the exact MCP artifact and list Simple tools within the time limit")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Run the Stage 2-built MCP artifact with initialize and tools/list frames")
val probe = mcp_cmdline_probe("simple_mcp", pure_simple_mcp_binary(), 15, 15000, "Simple MCP Server", "simple_pipe", "", "")
step("Require readiness, successful exit, bounded latency, and simple_pipe")
expect(probe.ok).to_equal(true)
expect(probe.exit_code).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(probe.elapsed_ms).to_be_less_than(15001)
expect(probe.ready_json).to_contain("Simple MCP Server")
expect(probe.stdout).to_contain("simple_pipe")
```

</details>

#### should run core Simple MCP features without source or Rust fallback

- Verify: should run core Simple MCP features without source or Rust fallback
- Launch the cached native Simple MCP artifact
- Check the linked SPipe surface and bounded empty search result
   - Expected: probe.ok is true
   - Expected: probe.stderr does not contain `bootstrap-only`
   - Expected: probe.stderr does not contain `mode=source`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MCP-CMD-001
step("Verify: should run core Simple MCP features without source or Rust fallback")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/app/build/bootstrap.md`
- **Plan:** `doc/03_plan/sys_test/mcp_cmdline_handshake.md`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f6e64d8f25130393cb7dacd03162bde0829c1abb576eb7bafdac01cf97b4f38b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f6e64d8f25130393cb7dacd03162bde0829c1abb576eb7bafdac01cf97b4f38b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f6e64d8f25130393cb7dacd03162bde0829c1abb576eb7bafdac01cf97b4f38b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.spl
mirror: doc/06_spec/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.spl:165:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should build the exact MCP artifact with pure Stage 2' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.spl:175:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should launch the exact MCP artifact and list Simple tools within the time limit' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.spl:188:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should run core Simple MCP features without source or Rust fallback' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
