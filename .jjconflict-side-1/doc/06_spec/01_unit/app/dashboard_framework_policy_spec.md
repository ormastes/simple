# Dashboard Framework Policy Specification

> <details>

<!-- sdn-diagram:id=dashboard_framework_policy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dashboard_framework_policy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dashboard_framework_policy_spec -> std
dashboard_framework_policy_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dashboard_framework_policy_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dashboard Framework Policy Specification

## Scenarios

### Dashboard framework policy

#### detects and strips internal worker flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["agents", "--gui", FRAMEWORK_WORKER_FLAG, FRAMEWORK_PROFILE_PREFIX + "llm_worker"]
expect(is_framework_worker(args)).to_equal(true)
expect(strip_framework_flags(args)).to_equal(["agents", "--gui"])
```

</details>

#### isolates only heavy dashboard commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(should_isolate_dashboard_command("status", [])).to_equal(false)
expect(should_isolate_dashboard_command("collect", [])).to_equal(true)
expect(should_isolate_dashboard_command("serve", [])).to_equal(true)
expect(should_isolate_dashboard_command("agents", ["--gui"])).to_equal(true)
expect(should_isolate_dashboard_command("agents", [])).to_equal(false)
```

</details>

#### recognizes gui request flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(args_request_gui(["--gui"])).to_equal(true)
expect(args_request_gui(["--web"])).to_equal(true)
expect(args_request_gui(["--tui"])).to_equal(false)
```

</details>

#### builds worker args with internal profile markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val launch = dashboard_command_launch("collect", [])
val args = build_dashboard_worker_args("collect", ["--mode=full"], launch)
expect(args[0]).to_equal("dashboard")
expect(args[1]).to_equal("collect")
expect(args.contains(FRAMEWORK_WORKER_FLAG)).to_equal(true)
expect(args.contains("--mode=full")).to_equal(true)
```

</details>

#### exports watchdog memory and timeout budgets to worker shells

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val launch = dashboard_command_launch("collect", [])
val shell_cmd = build_worker_shell_command(["dashboard", "collect"], launch)
expect(shell_cmd).to_contain("export SIMPLE_MEMORY_LIMIT_MB='8192'; ")
expect(shell_cmd).to_contain("export SIMPLE_TIMEOUT_SECONDS='30'; ")
expect(shell_cmd).to_contain("export SIMPLE_BINARY=")
expect(shell_cmd).to_contain("export SIMPLE_THREAD_BUDGET=")
```

</details>

#### classifies limit failures ahead of exit code mapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(classify_worker_exit(137, true, "memory")).to_equal("memory")
expect(classify_worker_exit(101, false, "")).to_equal("panic")
```

</details>

#### does not inject timeout wrapper for long running dashboard workers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val launch = dashboard_command_launch("serve", [])
val shell_cmd = build_worker_shell_command(["dashboard", "serve"], launch)
expect(shell_cmd.contains("timeout --kill-after")).to_equal(false)
expect(shell_cmd.contains("SIMPLE_THREAD_BUDGET")).to_equal(true)
```

</details>

#### trims restart history by the configured window

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val trimmed = _trim_restart_history([1, 5_000_000, 70_000_000], 80_000_000, 60_000_000)
expect(trimmed).to_equal([70_000_000])
```

</details>

#### uses escalating restart backoff

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_restart_backoff_millis(1)).to_equal(250)
expect(_restart_backoff_millis(2)).to_equal(1000)
expect(_restart_backoff_millis(3)).to_equal(5000)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/dashboard_framework_policy_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Dashboard framework policy

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
