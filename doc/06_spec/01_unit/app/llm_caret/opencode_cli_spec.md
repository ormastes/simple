# Opencode Cli Specification

> <details>

<!-- sdn-diagram:id=opencode_cli_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=opencode_cli_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

opencode_cli_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=opencode_cli_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Opencode Cli Specification

## Scenarios

### OpenCode CLI wrapper

#### builds a non-interactive json run command

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_opencode_args("continue", "github-copilot/gpt-5", "sess-2", "json", "http://127.0.0.1:4096", false, ["", "--dir", "."])

expect(args[arg_at(args, "--attach") + 1]).to_equal("http://127.0.0.1:4096")
expect(arg_at(args, "--auto")).to_equal(-1)
expect(arg_at(args, "kill")).to_equal(-1)
expect(arg_at(args, "pkill")).to_equal(-1)
expect(args[args.len() - 1]).to_equal("continue")
```

</details>

#### parses json content without requiring the OpenCode binary

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = parse_opencode_response("{\"content\":\"done\",\"sessionID\":\"abc\"}", "anthropic/claude")

expect(resp.content).to_equal("done")
expect(resp.session_id).to_equal("abc")
expect(resp.is_error).to_equal(false)
```

</details>

#### rejects invalid kill pids before signalling

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = opencode_cli_kill(0)

expect(result.status).to_equal("not_stopped")
expect(result.reason).to_equal("invalid_pid")
expect(opencode_cli_running_status(-1)).to_equal("not_running")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/opencode_cli_spec.spl` |
| Updated | 2026-07-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- OpenCode CLI wrapper

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
