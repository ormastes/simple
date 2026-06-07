# Web Stack Sample Persistence Specification

> <details>

<!-- sdn-diagram:id=web_stack_sample_persistence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_stack_sample_persistence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_stack_sample_persistence_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_stack_sample_persistence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Stack Sample Persistence Specification

## Scenarios

### web_stack_sample simpledb restart persistence

#### persists app-surface register create login and search across reopen

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (seed_stdout, _seed_stderr, seed_code) = rt_process_run("bin/simple", ["run", RUNNER, "--", "seed", DB_PATH])
expect(seed_code).to_equal(0)
expect(seed_stdout).to_contain("PERSISTENCE_SEEDED")
expect(seed_stdout).to_contain("item=Persistent item")

val (verify_stdout, _verify_stderr, verify_code) = rt_process_run("bin/simple", ["run", RUNNER, "--", "verify", DB_PATH])
expect(verify_code).to_equal(0)
expect(verify_stdout).to_contain("PERSISTENCE_VERIFIED")
expect(verify_stdout).to_contain("item=Persistent item")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/web_stack_sample_persistence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- web_stack_sample simpledb restart persistence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
