# mcpgdb_log_modes_spec

> Purpose: This spec proves mcpgdb log mode CLI options.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mcpgdb_log_modes_spec

Purpose: This spec proves mcpgdb log mode CLI options.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/mcpgdb_log_modes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves mcpgdb log mode CLI options.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### mcpgdb log mode CLI options

#### shows shared log options in help

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- shows shared log options in help
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MCPGDBLOGMODES-001
step("shows shared log options in help")
val (out, err, code) = _run_mcpgdb(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("mcpgdb MCP Server")
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports log-mode json ready output

- supports log-mode json ready output
- supports log-mode json ready output
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports log-mode json ready output")
step("supports log-mode json ready output")
val (out, err, code) = _run_mcpgdb(["--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"mcpgdb\"")
expect(out).to_contain("\"status\":\"ready\"")
```

</details>

#### supports dot progress for help output

- supports dot progress for help output
- supports dot progress for help output
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports dot progress for help output")
step("supports dot progress for help output")
val (out, err, code) = _run_mcpgdb(["--progress=dot", "--help"])
expect(code).to_equal(0)
expect(out).to_contain(".\nmcpgdb MCP Server")
```

</details>

#### rejects invalid log mode

- rejects invalid log mode
- rejects invalid log mode
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects invalid log mode")
step("rejects invalid log mode")
val (out, err, code) = _run_mcpgdb(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

#### renders json unknown option output

- renders json unknown option output
- renders json unknown option output
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("renders json unknown option output")
step("renders json unknown option output")
val (out, err, code) = _run_mcpgdb(["--log-mode=json", "--surprise"])
expect(code).to_equal(1)
expect(out).to_contain("\"status\":\"error\"")
expect(out).to_contain("Unknown mcpgdb option: --surprise")
```

</details>

#### preserves normal MCP ping handling

- preserves normal MCP ping handling
- preserves normal MCP ping handling
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("preserves normal MCP ping handling")
step("preserves normal MCP ping handling")
val (out, err, code) = _ping_mcpgdb()
expect(code).to_equal(0)
expect(out).to_contain("\"jsonrpc\":\"2.0\"")
expect(out).to_contain("\"result\":{}")
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

- `REQ-SSPEC-INTEGRATION`
- `REQ-MCPGDBLOGMODES-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b624d1cff68deaa95401d4ec2992245d6734083a91b6c41fcc7ba3c99b1d73fb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b624d1cff68deaa95401d4ec2992245d6734083a91b6c41fcc7ba3c99b1d73fb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b624d1cff68deaa95401d4ec2992245d6734083a91b6c41fcc7ba3c99b1d73fb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/app/mcpgdb_log_modes_spec.spl
mirror: doc/06_spec/integration/app/mcpgdb_log_modes_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/mcpgdb_log_modes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/mcpgdb_log_modes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/mcpgdb_log_modes_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/mcpgdb_log_modes_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows shared log options in help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/mcpgdb_log_modes_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports log-mode json ready output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/mcpgdb_log_modes_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports dot progress for help output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
