# Ignored Event Exit Code Specification

> Verifies that ignored events do not change the final exit code when real tests pass. This keeps the original regression intent, but uses a parser-safe local harness instead of runtime-specific test markers.

<!-- sdn-diagram:id=skip_it_exit_code_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=skip_it_exit_code_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

skip_it_exit_code_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=skip_it_exit_code_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ignored Event Exit Code Specification

Verifies that ignored events do not change the final exit code when real tests pass. This keeps the original regression intent, but uses a parser-safe local harness instead of runtime-specific test markers.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKIP-IT-BUG |
| Category | Testing |
| Difficulty | 2/5 |
| Status | In Progress |
| Source | `test/01_unit/bugs/skip_it_exit_code_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that ignored events do not change the final exit code when real
tests pass. This keeps the original regression intent, but uses a parser-safe
local harness instead of runtime-specific test markers.

## Behavior

- real tests contribute to the pass count
- ignored events contribute only to the ignored count
- the final exit code stays zero when no failures are recorded

## Scenarios

### ignored events do not cause exit code 1

#### passes real tests and ignores non-executed events

1. stats mark pass
2. stats mark pass
3. stats mark ignored
4. stats mark ignored
5. stats mark pass
6. verify clean exit


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = RunStats.create()
stats.mark_pass()
stats.mark_pass()
stats.mark_ignored()
stats.mark_ignored()
stats.mark_pass()
verify_clean_exit(stats, 3, 2)
```

</details>

#### keeps exit code clean after a run of ignored events

1. stats mark ignored
2. stats mark ignored
3. stats mark ignored
4. stats mark pass
5. verify clean exit


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = RunStats.create()
stats.mark_ignored()
stats.mark_ignored()
stats.mark_ignored()
stats.mark_pass()
verify_clean_exit(stats, 1, 3)
```

</details>

#### handles ignored events in the middle of the run

1. stats mark pass
2. stats mark ignored
3. stats mark pass
4. stats mark ignored
5. stats mark pass
6. verify clean exit


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = RunStats.create()
stats.mark_pass()
stats.mark_ignored()
stats.mark_pass()
stats.mark_ignored()
stats.mark_pass()
verify_clean_exit(stats, 3, 2)
```

</details>

#### keeps boundary ignored events from affecting the outcome

1. stats mark ignored
2. stats mark pass
3. stats mark pass
4. stats mark ignored
5. verify clean exit


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = RunStats.create()
stats.mark_ignored()
stats.mark_pass()
stats.mark_pass()
stats.mark_ignored()
verify_clean_exit(stats, 2, 2)
```

</details>

#### tracks only ignored events without reporting failure

1. stats mark ignored
2. stats mark ignored
3. stats mark ignored
   - Expected: stats.total_events() equals `3`
   - Expected: stats.exit_code() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = RunStats.create()
stats.mark_ignored()
stats.mark_ignored()
stats.mark_ignored()
expect(stats.total_events()).to_equal(3)
expect(stats.exit_code()).to_equal(0)
```

</details>

#### would report a non-zero exit code only for failures

1. stats mark pass
2. stats mark ignored
3. stats mark failed
   - Expected: stats.exit_code() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = RunStats.create()
stats.mark_pass()
stats.mark_ignored()
stats.mark_failed()
expect(stats.exit_code()).to_equal(1)
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
