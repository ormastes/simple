# Claude Full MCP Config Slice

> Focused Simple coverage for stateless MCP config helpers from

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full MCP Config Slice

Focused Simple coverage for stateless MCP config helpers from

## At a Glance

| Field | Value |
|-------|-------|
| Category | MCP |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/services/mcp/config_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused Simple coverage for stateless MCP config helpers from
services/mcp/config.ts.

## Scenarios

### Claude full MCP config parity

#### should model CCR URL unwrapping

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model CCR URL unwrapping
- Check CCR unwrap
   - Expected: unwrapCcrProxyUrlRoute("https://example.test/mcp") equals `https://example.test/mcp`
   - Expected: unwrapCcrProxyUrlRoute("https://proxy/v2/session_ingress/shttp/mcp/?mcp_url=https://server/mcp") equals `https://server/mcp`
   - Expected: unwrapCcrProxyUrlRoute("https://proxy/v2/ccr-sessions/1?mcp_url=https://server/mcp&x=1") equals `https://server/mcp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model CCR URL unwrapping")
step("Check CCR unwrap")
expect(unwrapCcrProxyUrlRoute("https://example.test/mcp")).to_equal("https://example.test/mcp")
expect(unwrapCcrProxyUrlRoute("https://proxy/v2/session_ingress/shttp/mcp/?mcp_url=https://server/mcp")).to_equal("https://server/mcp")
expect(unwrapCcrProxyUrlRoute("https://proxy/v2/ccr-sessions/1?mcp_url=https://server/mcp&x=1")).to_equal("https://server/mcp")
```

</details>

#### should model MCP server signatures

- should model MCP server signatures
- Check signatures
   - Expected: getMcpServerSignatureRoute("stdio", "node", "server.js,--flag", "") equals `stdio:[node|server.js,--flag]`
   - Expected: getMcpServerSignatureRoute("url", "", "", "https://proxy/v2/session_ingress/shttp/mcp/?mcp_url=https://server/mcp") equals `url:https://server/mcp`
   - Expected: getMcpServerSignatureRoute("sdk", "", "", "") equals `null`
   - Expected: commandArraysMatchRoute("node|server.js", "node|server.js") is true
   - Expected: commandArraysMatchRoute("node|a", "node|b") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model MCP server signatures")
step("Check signatures")
expect(getMcpServerSignatureRoute("stdio", "node", "server.js,--flag", "")).to_equal("stdio:[node|server.js,--flag]")
expect(getMcpServerSignatureRoute("url", "", "", "https://proxy/v2/session_ingress/shttp/mcp/?mcp_url=https://server/mcp")).to_equal("url:https://server/mcp")
expect(getMcpServerSignatureRoute("sdk", "", "", "")).to_equal("null")
expect(commandArraysMatchRoute("node|server.js", "node|server.js")).to_equal(true)
expect(commandArraysMatchRoute("node|a", "node|b")).to_equal(false)
```

</details>

#### should model URL pattern matching

- should model URL pattern matching
- Check URL patterns
   - Expected: urlPatternToRegexRoute("https://*.example.com/mcp") equals `https://.*\\.example\\.com/mcp`
   - Expected: urlMatchesPatternRoute("https://api.example.com/mcp", "https://*.example.com/mcp") is true
   - Expected: urlMatchesPatternRoute("https://api.example.com:8443/mcp", "https://api.example.com/mcp") is false
   - Expected: urlMatchesPatternRoute("https://api.example.com/mcp", "https://api.example.com/mcp") is true
   - Expected: mcpConfigSourceLinesModeled() equals `1578`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model URL pattern matching")
step("Check URL patterns")
expect(urlPatternToRegexRoute("https://*.example.com/mcp")).to_equal("https://.*\\.example\\.com/mcp")
expect(urlMatchesPatternRoute("https://api.example.com/mcp", "https://*.example.com/mcp")).to_equal(true)
expect(urlMatchesPatternRoute("https://api.example.com:8443/mcp", "https://api.example.com/mcp")).to_equal(false)
expect(urlMatchesPatternRoute("https://api.example.com/mcp", "https://api.example.com/mcp")).to_equal(true)
expect(mcpConfigSourceLinesModeled()).to_equal(1578)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7e7cabdd576c4e2cc63caa987672d0bcb06d059a7182be460b04aa5763641ffc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7e7cabdd576c4e2cc63caa987672d0bcb06d059a7182be460b04aa5763641ffc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7e7cabdd576c4e2cc63caa987672d0bcb06d059a7182be460b04aa5763641ffc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/services/mcp/config_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/services/mcp/config_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/services/mcp/config_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/services/mcp/config_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/services/mcp/config_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/services/mcp/config_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model CCR URL unwrapping' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/mcp/config_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model CCR URL unwrapping' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/mcp/config_spec.spl:27:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model MCP server signatures' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/mcp/config_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model MCP server signatures' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/mcp/config_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model URL pattern matching' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/mcp/config_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model URL pattern matching' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
