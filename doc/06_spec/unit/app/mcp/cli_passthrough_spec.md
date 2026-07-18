# Cli Passthrough Specification

## Scenarios

### cli_passthrough: feature_gen

#### does not append a name arg when name is provided

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = _append_cli_args_for_name("", "{\"name\":\"MyFeature\"}", "simple_feature_gen")
val has_name_val = args.contains("MyFeature")
expect(has_name_val).to_equal(false)
```

</details>

#### builds empty args list for feature_gen with no props

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = _append_cli_args_for_name("", "{}", "simple_feature_gen")
expect(args).to_equal("")
```

</details>

### cli_passthrough: task_gen

#### does not append a name arg when name is provided

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = _append_cli_args_for_name("", "{\"name\":\"MyTask\"}", "simple_task_gen")
val has_name_val = args.contains("MyTask")
expect(has_name_val).to_equal(false)
```

</details>

#### builds empty args list for task_gen with no props

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = _append_cli_args_for_name("", "{}", "simple_task_gen")
expect(args).to_equal("")
```

</details>

### cli_passthrough: spec_gen still passes path

#### appends path value positionally for spec_gen

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = _append_cli_args_for_name("", "{\"path\":\"src/foo/bar.spl\"}", "simple_spec_gen")
expect(args.contains("src/foo/bar.spl")).to_equal(true)
```

</details>

### cli_passthrough: simple_test timeout handling

#### keeps outer timeout above requested per-test timeout

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "{\"timeout\":\"240\"}"
expect(_effective_cli_timeout_s("simple_test", body, 120)).to_equal(270)
```

</details>

#### keeps default outer timeout when requested timeout is lower

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "{\"timeout\":\"30\"}"
expect(_effective_cli_timeout_s("simple_test", body, 120)).to_equal(120)
```

</details>

#### ignores nonnumeric simple_test timeout values

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = _append_cli_args_for_name("timeout 120 bin/simple test", "{\"timeout\":\"60;rm -rf /\",\"path\":\"test/01_unit/foo.spl\"}", "simple_test")
expect(cmd).to_contain("test/01_unit/foo.spl")
expect(cmd).to_contain("--timeout 60")
expect(cmd.contains("60;rm")).to_equal(false)
```

</details>

#### preserves numeric simple_test timeout values

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = _append_cli_args_for_name("timeout 270 bin/simple test", "{\"timeout\":\"240\",\"path\":\"test/01_unit/foo.spl\"}", "simple_test")
expect(cmd).to_contain("--timeout 240")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp/cli_passthrough_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- cli_passthrough: feature_gen
- cli_passthrough: task_gen
- cli_passthrough: spec_gen still passes path
- cli_passthrough: simple_test timeout handling

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |
