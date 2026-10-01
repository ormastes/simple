# Mcp Argv Query Contract Specification

> Tests covering MCP argv query contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Argv Query Contract Specification

## Scenarios

### MCP argv query contract

#### reports declaration reordering and real API changes separately

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports declaration reordering and real API changes separately
   - Expected: reordered equals `(declaration order changed)\n`
   - Expected: changed does not contain `class Kept`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports declaration reordering and real API changes separately")
val reordered = _mcp_public_api_change_details(
    ["fn first()", "fn second()"],
    ["fn second()", "fn first()"])
val changed = _mcp_public_api_change_details(
    ["fn old()", "class Kept"],
    ["fn new()", "class Kept"])

expect(reordered).to_equal("(declaration order changed)\n")
expect(changed).to_contain("- fn old()")
expect(changed).to_contain("+ fn new()")
expect(changed.contains("class Kept")).to_equal(false)
```

</details>

#### does not execute a search query as shell syntax

- does not execute a search query as shell syntax
   - Expected: injected is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("does not execute a search query as shell syntax")
val sentinel = "/tmp/simple_mcp_query_argv_injection_" + str(rt_getpid())
val _ = rt_file_delete(sentinel)
val body = "{\"query\":\"needle; touch " + sentinel + "\",\"file\":\"/tmp/no-such-simple-mcp-file\"}"

val _result = handle_simple_search("1", body)

val injected = rt_file_exists(sentinel)
if injected:
    val _ = rt_file_delete(sentinel)
expect(injected).to_equal(false)
```

</details>

#### routes public query fields through argv helpers

- routes public query fields through argv helpers
   - Expected: source does not contain `shell_cmd(cmd)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("routes public query fields through argv helpers")
val source = file_read("src/app/mcp/main_lazy_query_tools.spl")

expect(source).to_contain('["show", "--end-of-options", rev + ":" + file]')
expect(source).to_contain('mcp_run_argv("rg", args, 15000, 262144)')
expect(source).to_contain("head -n 50")
expect(source).to_contain('mcp_run_argv("/bin/sh", args, 15000, 262144)')
expect(source).to_contain('"--query", query, "--requester", effective_requester')
expect(source).to_contain("_mcp_first_lines(rev_out, 30)")
expect(source).to_contain("_mcp_first_lines(out, 51)")
expect(source).to_contain("_mcp_first_lines(out, 50)")
expect(source.contains("shell_cmd(cmd)")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/mcp_argv_query_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MCP argv query contract.
- MCP argv query contract

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

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9b3507acefc5e83875f52517f41774dabaaa80445013cafcb40898e649025aa9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9b3507acefc5e83875f52517f41774dabaaa80445013cafcb40898e649025aa9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9b3507acefc5e83875f52517f41774dabaaa80445013cafcb40898e649025aa9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/app/mcp_unit/mcp_argv_query_contract_spec.spl
mirror: doc/06_spec/01_unit/app/mcp_unit/mcp_argv_query_contract_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/app/mcp_unit/mcp_argv_query_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/mcp_unit/mcp_argv_query_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/mcp_unit/mcp_argv_query_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/mcp_unit/mcp_argv_query_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/mcp_unit/mcp_argv_query_contract_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports declaration reordering and real API changes separately' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/mcp_unit/mcp_argv_query_contract_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not execute a search query as shell syntax' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/mcp_unit/mcp_argv_query_contract_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes public query fields through argv helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
