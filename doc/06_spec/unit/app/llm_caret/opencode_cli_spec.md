# opencode_cli_spec

> Verifies the opencode cli behaviour end to end.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# opencode_cli_spec

Verifies the opencode cli behaviour end to end.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/llm_caret/opencode_cli_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the opencode cli behaviour end to end.
Audience: engineers maintaining this component and its specs.

## Scenarios

### OpenCode CLI wrapper

#### builds a non-interactive json run command

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Verify: builds a non-interactive json run command
   - Expected: args[0] equals `run`
   - Expected: args[arg_at(args, "--format") + 1] equals `json`
   - Expected: args[arg_at(args, "--model") + 1] equals `anthropic/claude`
   - Expected: args[arg_at(args, "--session") + 1] equals `sess-1`
   - Expected: args[arg_at(args, "--auto")] equals `--auto`
   - Expected: args[args.len() - 1] equals `fix the test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLMCARET-OpencodeCli-001
step("Verify: builds a non-interactive json run command")
val args = build_opencode_args("fix the test", "anthropic/claude", "sess-1", "", "", true, ["--dir", "."])

expect(args[0]).to_equal("run")
expect(args[arg_at(args, "--format") + 1]).to_equal("json")
expect(args[arg_at(args, "--model") + 1]).to_equal("anthropic/claude")
expect(args[arg_at(args, "--session") + 1]).to_equal("sess-1")
expect(args[arg_at(args, "--auto")]).to_equal("--auto")
expect(args[args.len() - 1]).to_equal("fix the test")
```

</details>

#### builds attach arguments without shell kill shortcuts

- Verify: builds attach arguments without shell kill shortcuts
   - Expected: args[arg_at(args, "--attach") + 1] equals `http://127.0.0.1:4096`
   - Expected: arg_at(args, "--auto") equals `-1`
   - Expected: arg_at(args, "kill") equals `-1`
   - Expected: arg_at(args, "pkill") equals `-1`
   - Expected: args[args.len() - 1] equals `continue`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLMCARET-OpencodeCli-001
step("Verify: builds attach arguments without shell kill shortcuts")
val args = build_opencode_args("continue", "github-copilot/gpt-5", "sess-2", "json", "http://127.0.0.1:4096", false, ["", "--dir", "."])

expect(args[arg_at(args, "--attach") + 1]).to_equal("http://127.0.0.1:4096")
expect(arg_at(args, "--auto")).to_equal(-1)
expect(arg_at(args, "kill")).to_equal(-1)
expect(arg_at(args, "pkill")).to_equal(-1)
expect(args[args.len() - 1]).to_equal("continue")
```

</details>

#### parses json content without requiring the OpenCode binary

- Verify: parses json content without requiring the OpenCode binary
   - Expected: resp.content equals `done`
   - Expected: resp.session_id equals `abc`
   - Expected: resp.is_error is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLMCARET-OpencodeCli-001
step("Verify: parses json content without requiring the OpenCode binary")
val resp = parse_opencode_response("{\"content\":\"done\",\"sessionID\":\"abc\"}", "anthropic/claude")

expect(resp.content).to_equal("done")
expect(resp.session_id).to_equal("abc")
expect(resp.is_error).to_equal(false)
```

</details>

#### rejects invalid kill pids before signalling

- Verify: rejects invalid kill pids before signalling
   - Expected: result.status equals `not_stopped`
   - Expected: result.reason equals `invalid_pid`
   - Expected: opencode_cli_running_status(-1) equals `not_running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLMCARET-OpencodeCli-001
step("Verify: rejects invalid kill pids before signalling")
val result = opencode_cli_kill(0)

expect(result.status).to_equal("not_stopped")
expect(result.reason).to_equal("invalid_pid")
expect(opencode_cli_running_status(-1)).to_equal("not_running")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LLMCARET-OpencodeCli-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bb91ddc5b8b7cbe9bf54b3bc03f7b0d6d323bc2caf43fbfba1ed3fa7e42dd1e5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bb91ddc5b8b7cbe9bf54b3bc03f7b0d6d323bc2caf43fbfba1ed3fa7e42dd1e5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bb91ddc5b8b7cbe9bf54b3bc03f7b0d6d323bc2caf43fbfba1ed3fa7e42dd1e5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/app/llm_caret/opencode_cli_spec.spl
mirror: doc/06_spec/unit/app/llm_caret/opencode_cli_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/unit/app/llm_caret/opencode_cli_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/llm_caret/opencode_cli_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/llm_caret/opencode_cli_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/llm_caret/opencode_cli_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/app/llm_caret/opencode_cli_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds a non-interactive json run command' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_caret/opencode_cli_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds attach arguments without shell kill shortcuts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_caret/opencode_cli_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses json content without requiring the OpenCode binary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
