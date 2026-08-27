# llm_diag_hook_log_modes_spec

> Purpose: This spec proves llm-diag-hook log mode CLI options.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# llm_diag_hook_log_modes_spec

Purpose: This spec proves llm-diag-hook log mode CLI options.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/llm_diag_hook_log_modes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves llm-diag-hook log mode CLI options.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### llm-diag-hook log mode CLI options

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
# @req: REQ-LLMDIAGHOOKLOGMODES-001
step("shows shared log options in help")
val (out, err, code) = _run_llm_diag_hook(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("LLM Diagnostics Hook")
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
val (out, err, code) = _run_llm_diag_hook(["--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"llm-diag-hook\"")
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
val (out, err, code) = _run_llm_diag_hook(["--progress=dot", "--help"])
expect(code).to_equal(0)
expect(out).to_contain(".\nLLM Diagnostics Hook")
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
val (out, err, code) = _run_llm_diag_hook(["--log-mode=noisy"])
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
val (out, err, code) = _run_llm_diag_hook(["--log-mode=json", "--surprise"])
expect(code).to_equal(1)
expect(out).to_contain("\"status\":\"error\"")
expect(out).to_contain("Unknown llm-diag-hook option: --surprise")
```

</details>

#### logs stdin hook json without blocking

- logs stdin hook json without blocking
- logs stdin hook json without blocking
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("logs stdin hook json without blocking")
step("logs stdin hook json without blocking")
val log_path = "/tmp/simple_llm_diag_hook_log_modes.jsonl"
val input = "{\"hook_event_name\":\"SessionStart\",\"session_id\":\"sid-1\"}"
val (out, err, code) = _run_llm_diag_hook_with_input(["--log-mode=json"], input, log_path)
expect(code).to_equal(0)
expect(out).to_contain("\"status\":\"logged\"")
val logged = rt_file_read_text(log_path) ?? ""
expect(logged).to_contain("\"event\":\"SessionStart\"")
expect(logged).to_contain("\"sid\":\"sid-1\"")
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
- `REQ-LLMDIAGHOOKLOGMODES-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a0c26b5ae3c98ba2093cfdd0615905bed6572f4497720287906bb32775dd635a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a0c26b5ae3c98ba2093cfdd0615905bed6572f4497720287906bb32775dd635a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a0c26b5ae3c98ba2093cfdd0615905bed6572f4497720287906bb32775dd635a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/app/llm_diag_hook_log_modes_spec.spl
mirror: doc/06_spec/integration/app/llm_diag_hook_log_modes_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/llm_diag_hook_log_modes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/llm_diag_hook_log_modes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/llm_diag_hook_log_modes_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/llm_diag_hook_log_modes_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows shared log options in help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/llm_diag_hook_log_modes_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports log-mode json ready output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/llm_diag_hook_log_modes_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports dot progress for help output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
