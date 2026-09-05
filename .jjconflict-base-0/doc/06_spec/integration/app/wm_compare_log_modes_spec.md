# Wm Compare Log Modes Specification

## Scenarios

### wm compare log mode CLI options

#### shows shared log options in help

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_wm_compare(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports log-mode json for usage output

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_wm_compare(["--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"wm-compare\"")
expect(out).to_contain("\"status\":\"usage\"")
```

</details>

#### supports dot progress for help output

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_wm_compare(["--progress=dot", "--help"])
expect(code).to_equal(0)
expect(out).to_start_with(".")
expect(out).to_contain("Unified pixel capture")
```

</details>

#### rejects invalid log mode

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_wm_compare(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

#### emits json for missing scene

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_wm_compare(["--log-mode=json", "--source=A"])
expect(code).to_equal(1)
expect(out).to_contain("\"command\":\"wm-compare\"")
expect(out).to_contain("\"error\":\"missing scene\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/wm_compare_log_modes_spec.spl` |
| Updated | 2026-05-31 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wm compare log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

