# Bootstrap Parse Shard Dispatch Specification

> Tests covering Bootstrap parse workers keep their slim owner.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap Parse Shard Dispatch Specification

## Scenarios

### Bootstrap parse workers keep their slim owner

#### selects marked parse children while preserving and fencing the native worker route

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parse = ["simple", "run", "src/app/cli/parse_shard_main.spl", "--parse-shard=0/1"]
val native = ["simple", "run", "src/app/cli/native_build_worker.spl"]
expect(bootstrap_internal_worker_is_parse_v1(parse, "1")).to_equal(true)
expect(bootstrap_internal_worker_is_parse_v1(parse, "")).to_equal(false)
expect(bootstrap_internal_worker_is_parse_v1(native, "1")).to_equal(false)
expect(bootstrap_internal_worker_run_v1(native, "1")).to_equal(true)
expect(bootstrap_internal_worker_run_v1(["simple", "run", "test/unknown.spl"], "1")).to_equal(false)
expect(bootstrap_internal_worker_is_parse_v1(["simple", "run"], "1")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/bootstrap_parse_shard_dispatch_spec.spl` |
| Updated | 2026-10-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Bootstrap parse workers keep their slim owner.
- Bootstrap parse workers keep their slim owner

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
