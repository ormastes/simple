# dashboard_framework_policy_spec

> Purpose: Prove that Dashboard framework policy.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dashboard_framework_policy_spec

Purpose: Prove that Dashboard framework policy.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/dashboard_framework_policy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Dashboard framework policy.
Audience: APP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### Dashboard framework policy

#### detects and strips internal worker flags

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects and strips internal worker flags
- Verify: detects and strips internal worker flags
   - Expected: is_framework_worker(args) is true
   - Expected: strip_framework_flags(args) equals `["agents", "--gui"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects and strips internal worker flags")
step("Verify: detects and strips internal worker flags")
# @req: REQ-APP-DASHBOARD-FRAMEWORK-POLICY-001
val args = ["agents", "--gui", FRAMEWORK_WORKER_FLAG, FRAMEWORK_PROFILE_PREFIX + "llm_worker"]
expect(is_framework_worker(args)).to_equal(true)
expect(strip_framework_flags(args)).to_equal(["agents", "--gui"])
```

</details>

#### isolates only heavy dashboard commands

- isolates only heavy dashboard commands
- Verify: isolates only heavy dashboard commands
   - Expected: should_isolate_dashboard_command("status", []) is false
   - Expected: should_isolate_dashboard_command("collect", []) is true
   - Expected: should_isolate_dashboard_command("serve", []) is true
   - Expected: should_isolate_dashboard_command("agents", ["--gui"]) is true
   - Expected: should_isolate_dashboard_command("agents", []) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("isolates only heavy dashboard commands")
step("Verify: isolates only heavy dashboard commands")
expect(should_isolate_dashboard_command("status", [])).to_equal(false)
expect(should_isolate_dashboard_command("collect", [])).to_equal(true)
expect(should_isolate_dashboard_command("serve", [])).to_equal(true)
expect(should_isolate_dashboard_command("agents", ["--gui"])).to_equal(true)
expect(should_isolate_dashboard_command("agents", [])).to_equal(false)
```

</details>

#### recognizes gui request flags

- recognizes gui request flags
- Verify: recognizes gui request flags
   - Expected: args_request_gui(["--gui"]) is true
   - Expected: args_request_gui(["--web"]) is true
   - Expected: args_request_gui(["--tui"]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes gui request flags")
step("Verify: recognizes gui request flags")
expect(args_request_gui(["--gui"])).to_equal(true)
expect(args_request_gui(["--web"])).to_equal(true)
expect(args_request_gui(["--tui"])).to_equal(false)
```

</details>

#### builds worker args with internal profile markers

- builds worker args with internal profile markers
- Verify: builds worker args with internal profile markers
   - Expected: args[0] equals `dashboard`
   - Expected: args[1] equals `collect`
   - Expected: args contains `FRAMEWORK_WORKER_FLAG`
   - Expected: args contains `--mode=full`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds worker args with internal profile markers")
step("Verify: builds worker args with internal profile markers")
val launch = dashboard_command_launch("collect", [])
val args = build_dashboard_worker_args("collect", ["--mode=full"], launch)
expect(args[0]).to_equal("dashboard")
expect(args[1]).to_equal("collect")
expect(args.contains(FRAMEWORK_WORKER_FLAG)).to_equal(true)
expect(args.contains("--mode=full")).to_equal(true)
```

</details>

#### exports watchdog memory and timeout budgets to worker shells

- exports watchdog memory and timeout budgets to worker shells
- Verify: exports watchdog memory and timeout budgets to worker shells


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports watchdog memory and timeout budgets to worker shells")
step("Verify: exports watchdog memory and timeout budgets to worker shells")
val launch = dashboard_command_launch("collect", [])
val shell_cmd = build_worker_shell_command(["dashboard", "collect"], launch)
expect(shell_cmd).to_contain("export SIMPLE_MEMORY_LIMIT_MB='8192'; ")
expect(shell_cmd).to_contain("export SIMPLE_TIMEOUT_SECONDS='30'; ")
expect(shell_cmd).to_contain("export SIMPLE_BINARY=")
expect(shell_cmd).to_contain("export SIMPLE_THREAD_BUDGET=")
```

</details>

#### classifies limit failures ahead of exit code mapping

- classifies limit failures ahead of exit code mapping
- Verify: classifies limit failures ahead of exit code mapping
   - Expected: classify_worker_exit(137, true, "memory") equals `memory`
   - Expected: classify_worker_exit(101, false, "") equals `panic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies limit failures ahead of exit code mapping")
step("Verify: classifies limit failures ahead of exit code mapping")
expect(classify_worker_exit(137, true, "memory")).to_equal("memory")
expect(classify_worker_exit(101, false, "")).to_equal("panic")
```

</details>

#### does not inject timeout wrapper for long running dashboard workers

- does not inject timeout wrapper for long running dashboard workers
- Verify: does not inject timeout wrapper for long running dashboard workers
   - Expected: shell_cmd does not contain `timeout --kill-after`
   - Expected: shell_cmd contains `SIMPLE_THREAD_BUDGET`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not inject timeout wrapper for long running dashboard workers")
step("Verify: does not inject timeout wrapper for long running dashboard workers")
val launch = dashboard_command_launch("serve", [])
val shell_cmd = build_worker_shell_command(["dashboard", "serve"], launch)
expect(shell_cmd.contains("timeout --kill-after")).to_equal(false)
expect(shell_cmd.contains("SIMPLE_THREAD_BUDGET")).to_equal(true)
```

</details>

#### trims restart history by the configured window

- trims restart history by the configured window
- Verify: trims restart history by the configured window
   - Expected: trimmed equals `[70_000_000]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trims restart history by the configured window")
step("Verify: trims restart history by the configured window")
val trimmed = _trim_restart_history([1, 5_000_000, 70_000_000], 80_000_000, 60_000_000)
expect(trimmed).to_equal([70_000_000])
```

</details>

#### uses escalating restart backoff

- uses escalating restart backoff
- Verify: uses escalating restart backoff
   - Expected: _restart_backoff_millis(1) equals `250`
   - Expected: _restart_backoff_millis(2) equals `1000`
   - Expected: _restart_backoff_millis(3) equals `5000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses escalating restart backoff")
step("Verify: uses escalating restart backoff")
expect(_restart_backoff_millis(1)).to_equal(250)
expect(_restart_backoff_millis(2)).to_equal(1000)
expect(_restart_backoff_millis(3)).to_equal(5000)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-DASHBOARD-FRAMEWORK-POLICY-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8e3d050d0f665fd02dd9c1f80d61c24579a01e220ca7eb45c222d98f6111dc92`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8e3d050d0f665fd02dd9c1f80d61c24579a01e220ca7eb45c222d98f6111dc92`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8e3d050d0f665fd02dd9c1f80d61c24579a01e220ca7eb45c222d98f6111dc92`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/dashboard_framework_policy_spec.spl
mirror: doc/06_spec/unit/app/dashboard_framework_policy_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/dashboard_framework_policy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/dashboard_framework_policy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/dashboard_framework_policy_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/dashboard_framework_policy_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects and strips internal worker flags' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/dashboard_framework_policy_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'isolates only heavy dashboard commands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/dashboard_framework_policy_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes gui request flags' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
