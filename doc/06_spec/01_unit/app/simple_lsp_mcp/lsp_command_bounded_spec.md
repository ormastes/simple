# lsp_command_bounded_spec

> Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lsp_command_bounded_spec

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/simple_lsp_mcp/lsp_command_bounded_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## Operator workflow

1. Run `bin/simple test test/01_unit/app/simple_lsp_mcp/lsp_command_bounded_spec.spl`.
2. Every scenario must pass; a failure is a regression in the behavior under test.

## Compatibility and limitations

Covers the behavior asserted here; platform-specific behavior is out of scope.

## Scenarios

### simple_lsp_mcp bounded command dispatch

#### keeps every query dispatch behind the bounded command owner

- Verify: keeps every query dispatch behind the bounded command owner
   - Expected: helpers does not contain `process_run(binary, args)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: keeps every query dispatch behind the bounded command owner")
# @req: REQ-SSPEC-LOCAL-001
val helpers = file_read("src/app/simple_lsp_mcp/json_helpers.spl")
val tools = file_read("src/app/simple_lsp_mcp/tools.spl")

expect(helpers.contains("process_run(binary, args)")).to_equal(false)
expect(tools).to_contain("process_run_bounded(")
expect(tools).to_contain("LSP_COMMAND_TIMEOUT_MS: i64 = 10000")
expect(tools).to_contain("LSP_COMMAND_OUTPUT_CAPTURE_BYTES: i64 = 1024 * 1024")
expect(tools).to_contain("fn run_lsp_query(subcmd: text, file: text, line0: i64, char0: i64) -> text:\n    run_command_text(")
expect(tools).to_contain("fn run_visibility_query(subcmd: text, file: text, line0: i64, char0: i64) -> text:\n    run_command_text(")
expect(tools).to_contain("fn run_visibility_symbols(file: text) -> text:\n    run_command_text(")
```

</details>

#### finds the repo binary from SIMPLE_LIB when cwd is not the repo root

- Verify: finds the repo binary from SIMPLE_LIB when cwd is not the repo root


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: finds the repo binary from SIMPLE_LIB when cwd is not the repo root")
# @req: REQ-SSPEC-LOCAL-001
val helpers = file_read("src/app/simple_lsp_mcp/json_helpers.spl")
expect(helpers).to_contain("val lib_dir = env_get(\"SIMPLE_LIB\") ?? \"\"")
expect(helpers).to_contain("val repo_bin = lib_dir.substring(0, lib_dir.len() - 4) + \"/bin/simple\"")
```

</details>

#### bounds a hung command and caps a flood

- Verify: bounds a hung command and caps a flood
   - Expected: timeout contains `"TIMEOUT") or timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: bounds a hung command and caps a flood")
if host_os() != "windows":
    val timeout = run_command_text("/bin/sh", ["-c", "printf EARLY; sleep 11"])
    val flood = run_command_text("/bin/sh", ["-c", "yes X | head -c 1049600"])

    expect(timeout.contains("TIMEOUT") or timeout.contains("timed out")).to_equal(true)
    expect(flood).to_contain("[output truncated: ")
```

</details>

#### marks nonzero child output as command failure

- Verify: marks nonzero child output as command failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: marks nonzero child output as command failure")
if host_os() != "windows":
    val failure = run_command_text("/bin/sh", ["-c", "printf child-error >&2; exit 7"])
    expect(failure).to_start_with("command failed with exit code 7:")
    expect(failure).to_contain("child-error")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bc64e8c51eb1fb31ab7cf13c77e25fb9ac6b29c4c00401cbecfa8c625a00e59a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bc64e8c51eb1fb31ab7cf13c77e25fb9ac6b29c4c00401cbecfa8c625a00e59a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bc64e8c51eb1fb31ab7cf13c77e25fb9ac6b29c4c00401cbecfa8c625a00e59a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/app/simple_lsp_mcp/lsp_command_bounded_spec.spl
mirror: doc/06_spec/01_unit/app/simple_lsp_mcp/lsp_command_bounded_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=55 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/simple_lsp_mcp/lsp_command_bounded_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/01_unit/app/simple_lsp_mcp/lsp_command_bounded_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/simple_lsp_mcp/lsp_command_bounded_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/simple_lsp_mcp/lsp_command_bounded_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds the repo binary from SIMPLE_LIB when cwd is not the repo root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/simple_lsp_mcp/lsp_command_bounded_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bounds a hung command and caps a flood' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/simple_lsp_mcp/lsp_command_bounded_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'marks nonzero child output as command failure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

<!-- doc06-layout-migration: Historical generated/manual evidence retained; authoritative executable source remains at test/01_unit/app/simple_lsp_mcp/lsp_command_bounded_spec.spl. -->
