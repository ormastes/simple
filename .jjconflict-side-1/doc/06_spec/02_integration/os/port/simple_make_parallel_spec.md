# simple_make_parallel_spec

> With jobs=2 and two leaf targets with no shared deps, both targets

<!-- sdn-diagram:id=simple_make_parallel_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_make_parallel_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_make_parallel_spec -> std
simple_make_parallel_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_make_parallel_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_make_parallel_spec

With jobs=2 and two leaf targets with no shared deps, both targets

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/port/simple_make_parallel_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## -j N dispatches independent targets concurrently

    With jobs=2 and two leaf targets with no shared deps, both targets
    should be dispatched to separate threads without one waiting on the other.

## Scenarios

### simple_make parallel execution

#### build_target_parallel returns true for a trivially empty makefile

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not parallel_enabled():
    return
val mf = parse_makefile("all:\n")
var built: [text] = []
val ok = build_target_parallel(mf, "all", built, 2)
expect(ok).to_equal(true)
```

</details>

#### build_target_parallel with two independent leaf targets succeeds

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not parallel_enabled():
    return
# Two rules with no deps — both are leaves, eligible for parallel dispatch
val content = "all: a b\na:\n\techo built_a\nb:\n\techo built_b\n"
val mf = parse_makefile(content)
var built: [text] = []
val ok = build_target_parallel(mf, "all", built, 2)
expect(ok).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
