# Mcp Cli Argv Passthrough Contract Specification

> Tests covering MCP CLI argv passthrough.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Cli Argv Passthrough Contract Specification

## Scenarios

### MCP CLI argv passthrough

#### keeps public path and query metacharacters as literal argv values

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps public path and query metacharacters as literal argv values
   - Expected: path_args equals `["check", "/tmp/a;touch nope"]`
   - Expected: query_args equals `["query", "ast-query", "name; touch nope", "src/*.spl"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps public path and query metacharacters as literal argv values")
val path_args = _cli_args_for_name("check", "{\"path\":\"/tmp/a;touch nope\"}", "simple_check")
val query_args = _cli_args_for_name("query ast-query", "{\"query\":\"name; touch nope\",\"files\":\"src/*.spl\"}", "simple_ast_query")

expect(path_args).to_equal(["check", "/tmp/a;touch nope"])
expect(query_args).to_equal(["query", "ast-query", "name; touch nope", "src/*.spl"])
```

</details>

#### rejects timeout values that could disable the outer deadline

- rejects timeout values that could disable the outer deadline
   - Expected: _parse_positive_int_or_zero("86400") equals `86400`
   - Expected: _parse_positive_int_or_zero("86401") equals `0`
   - Expected: _parse_positive_int_or_zero("9223372036854775807") equals `0`
   - Expected: _mcp_normalize_process_exit(-1, "[TIMEOUT: Process killed after 10ms]") equals `124`
   - Expected: _mcp_normalize_process_exit(0, "[TIMEOUT: Process killed after 10ms]") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects timeout values that could disable the outer deadline")
expect(_parse_positive_int_or_zero("86400")).to_equal(86400)
expect(_parse_positive_int_or_zero("86401")).to_equal(0)
expect(_parse_positive_int_or_zero("9223372036854775807")).to_equal(0)
expect(_mcp_normalize_process_exit(-1, "[TIMEOUT: Process killed after 10ms]")).to_equal(124)
expect(_mcp_normalize_process_exit(0, "[TIMEOUT: Process killed after 10ms]")).to_equal(0)
```

</details>

#### rejects positional child-option injection

- rejects positional child-option injection
   - Expected: _cli_positional_error("{\"filter\":\"-slow\"}", "simple_test") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects positional child-option injection")
expect(_cli_positional_error("{\"path\":\"-delete\"}", "simple_check")).to_contain("option-like")
expect(_cli_positional_error("{\"query\":\"-exec\"}", "simple_ast_query")).to_contain("option-like")
expect(_cli_positional_error("{\"package\":\"--help\"}", "simple_remove")).to_contain("option-like")
expect(_cli_positional_error("{\"filter\":\"-slow\"}", "simple_test")).to_equal("")
```

</details>

#### maps the complete SSpec maintenance request as literal argv

- maps the complete SSpec maintenance request as literal argv


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("maps the complete SSpec maintenance request as literal argv")
val body = "{\"operation\":\"scan\",\"path\":\"test/a spec.spl\"," +
    "\"format\":\"sarif\",\"min_score\":\"80\"," +
    "\"deny_severity\":\"warning\",\"baseline\":\"base.txt\"," +
    "\"suppressions\":\"suppress.txt\",\"rule\":\"SSDOC-NAR-001\"," +
    "\"no_cache\":true,\"debug_timings\":true}"
expect(_cli_args_for_name("sspec-maintain", body,
    "simple_sspec_maintain")).to_equal([
        "sspec-maintain", "scan", "test/a spec.spl", "--format",
        "sarif", "--min-score", "80", "--deny-severity", "warning",
        "--baseline", "base.txt", "--suppressions", "suppress.txt",
        "--rule", "SSDOC-NAR-001", "--no-cache", "--debug-timings"])
expect(_cli_positional_error(
    "{\"operation\":\"--help\",\"path\":\"test/a.spl\"}",
    "simple_sspec_maintain")).to_contain("option-like")
```

</details>

#### does not route passthrough request fields through a shell

- keeps shell metacharacters literal — no expansion, no marker file
   - Expected: _cli_positional_error(body, "simple_check") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps shell metacharacters literal — no expansion, no marker file")
# Executed equivalent of the argv-contract: a value stuffed with shell
# metacharacters must survive as ONE literal argv element. If a shell
# ever sat on this path, the marker file below would exist afterwards.
val marker = "/tmp/mcp_cli_passthrough_pwn_marker"
val body = "{\"path\":\"/tmp/a;touch " + marker + "\"}"
expect(_cli_args_for_name("check", body, "simple_check")).to_equal(
    ["check", "/tmp/a;touch " + marker])
expect(_cli_positional_error(body, "simple_check")).to_equal("")
# oracle: no marker file — the metacharacters were data, never commands
assert_false(file_exists(marker))
```

</details>

#### maps the read-only SSpec scan tool without a mutable operation field

- maps the read-only SSpec scan tool without a mutable operation field


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("maps the read-only SSpec scan tool without a mutable operation field")
val body = "{\"path\":\"test/features\",\"format\":\"json\"," +
    "\"rule\":\"SSDOC-ORA-001\",\"no_cache\":true}"
expect(_cli_args_for_name("sspec-maintain", body,
    "simple_sspec_scan")).to_equal(["sspec-maintain", "scan",
        "test/features", "--format", "json", "--rule",
        "SSDOC-ORA-001", "--no-cache"])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/mcp_cli_argv_passthrough_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MCP CLI argv passthrough.
- MCP CLI argv passthrough

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

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e13f5f60645006d85109411766b9770ec7385eae74685c737a512be8eb4d28ef`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e13f5f60645006d85109411766b9770ec7385eae74685c737a512be8eb4d28ef`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e13f5f60645006d85109411766b9770ec7385eae74685c737a512be8eb4d28ef`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/mcp_unit/mcp_cli_argv_passthrough_contract_spec.spl
mirror: doc/06_spec/01_unit/app/mcp_unit/mcp_cli_argv_passthrough_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/mcp_unit/mcp_cli_argv_passthrough_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/mcp_unit/mcp_cli_argv_passthrough_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/mcp_unit/mcp_cli_argv_passthrough_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/mcp_unit/mcp_cli_argv_passthrough_contract_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps public path and query metacharacters as literal argv values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/mcp_unit/mcp_cli_argv_passthrough_contract_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects timeout values that could disable the outer deadline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/mcp_unit/mcp_cli_argv_passthrough_contract_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects positional child-option injection' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
