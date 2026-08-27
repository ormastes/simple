# Claude Full Transport Utils

> Checks transport selection priority for Claude CLI session ingress URLs.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Transport Utils

Checks transport selection priority for Claude CLI session ingress URLs.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/cli/transports/transportUtils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks transport selection priority for Claude CLI session ingress URLs.

## Scenarios

### Claude full transport utils

#### should prefer SSE transport when CCR v2 is enabled

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should prefer SSE transport when CCR v2 is enabled
- Select transport for secure websocket URL
   - Expected: choice.kind equals `SSETransport`
   - Expected: choice.url equals `https://api.example/session/1/worker/events/stream`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should prefer SSE transport when CCR v2 is enabled")
step("Select transport for secure websocket URL")
val choice = getTransportForUrl("wss://api.example/session/1", true, false)
expect(choice.kind).to_equal("SSETransport")
expect(choice.url).to_equal("https://api.example/session/1/worker/events/stream")
```

</details>

#### should convert insecure websocket SSE URLs to HTTP

- should convert insecure websocket SSE URLs to HTTP
- Select transport for local websocket URL
   - Expected: choice.kind equals `SSETransport`
   - Expected: choice.url equals `http://localhost/session/1/worker/events/stream`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should convert insecure websocket SSE URLs to HTTP")
step("Select transport for local websocket URL")
val choice = getTransportForUrl("ws://localhost/session/1/", true, false)
expect(choice.kind).to_equal("SSETransport")
expect(choice.url).to_equal("http://localhost/session/1/worker/events/stream")
```

</details>

#### should choose hybrid for websocket ingress post flag

- should choose hybrid for websocket ingress post flag
- Select post-for-ingress transport
   - Expected: choice.kind equals `HybridTransport`
   - Expected: choice.url equals `wss://api.example/session/1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should choose hybrid for websocket ingress post flag")
step("Select post-for-ingress transport")
val choice = getTransportForUrl("wss://api.example/session/1", false, true)
expect(choice.kind).to_equal("HybridTransport")
expect(choice.url).to_equal("wss://api.example/session/1")
```

</details>

#### should choose websocket by default

- should choose websocket by default
- Select default websocket transport
   - Expected: choice.kind equals `WebSocketTransport`
   - Expected: choice.error equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should choose websocket by default")
step("Select default websocket transport")
val choice = getTransportForUrl("ws://localhost/session/1", false, false)
expect(choice.kind).to_equal("WebSocketTransport")
expect(choice.error).to_equal("")
```

</details>

#### should reject unsupported protocols

- should reject unsupported protocols
- Select transport for HTTPS URL without CCR v2
   - Expected: choice.kind equals ``
   - Expected: choice.error equals `Unsupported protocol: https:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject unsupported protocols")
step("Select transport for HTTPS URL without CCR v2")
val choice = getTransportForUrl("https://api.example/session/1", false, false)
expect(choice.kind).to_equal("")
expect(choice.error).to_equal("Unsupported protocol: https:")
```

</details>

#### should expose source line parity

- should expose source line parity
- Pin source size
   - Expected: transportUtilsSourceLinesModeled() equals `45`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose source line parity")
step("Pin source size")
expect(transportUtilsSourceLinesModeled()).to_equal(45)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `e0118d986d3198b9b814088a2d69c08aa0e382d01e832ba321daf889876504b7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e0118d986d3198b9b814088a2d69c08aa0e382d01e832ba321daf889876504b7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e0118d986d3198b9b814088a2d69c08aa0e382d01e832ba321daf889876504b7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/cli/transports/transportUtils_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/cli/transports/transportUtils_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/cli/transports/transportUtils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/cli/transports/transportUtils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/cli/transports/transportUtils_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/cli/transports/transportUtils_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should prefer SSE transport when CCR v2 is enabled' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/transports/transportUtils_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should prefer SSE transport when CCR v2 is enabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/transports/transportUtils_spec.spl:26:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should convert insecure websocket SSE URLs to HTTP' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/transports/transportUtils_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should convert insecure websocket SSE URLs to HTTP' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/transports/transportUtils_spec.spl:34:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should choose hybrid for websocket ingress post flag' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/transports/transportUtils_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should choose hybrid for websocket ingress post flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/transports/transportUtils_spec.spl:42:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should choose websocket by default' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/transports/transportUtils_spec.spl:50:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject unsupported protocols' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/transports/transportUtils_spec.spl:58:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose source line parity' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
