# Llm Diag Hook Log Modes Specification

> <details>

<!-- sdn-diagram:id=llm_diag_hook_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llm_diag_hook_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llm_diag_hook_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llm_diag_hook_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llm Diag Hook Log Modes Specification

## Scenarios

### llm-diag-hook log mode CLI options

#### shows shared log options in help

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_llm_diag_hook(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("LLM Diagnostics Hook")
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports log-mode json ready output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_llm_diag_hook(["--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"llm-diag-hook\"")
expect(out).to_contain("\"status\":\"ready\"")
```

</details>

#### supports dot progress for help output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_llm_diag_hook(["--progress=dot", "--help"])
expect(code).to_equal(0)
expect(out).to_contain(".\nLLM Diagnostics Hook")
```

</details>

#### rejects invalid log mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_llm_diag_hook(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

#### renders json unknown option output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_llm_diag_hook(["--log-mode=json", "--surprise"])
expect(code).to_equal(1)
expect(out).to_contain("\"status\":\"error\"")
expect(out).to_contain("Unknown llm-diag-hook option: --surprise")
```

</details>

#### logs stdin hook json without blocking

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/llm_diag_hook_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- llm-diag-hook log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
