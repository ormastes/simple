# Todo Builtin Interpreter Coverage

> <details>

<!-- sdn-diagram:id=todo_builtin_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=todo_builtin_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

todo_builtin_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=todo_builtin_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Todo Builtin Interpreter Coverage

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/todo_builtin_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### todo builtin interpreter behavior

#### evaluates todo as nil no-op

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = eval_builtin_call("todo", [])
expect(val_get_kind(result)).to_equal(VAL_NIL)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
