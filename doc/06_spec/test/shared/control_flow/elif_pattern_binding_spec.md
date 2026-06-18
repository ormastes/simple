# elif pattern-binding regression

> Regression for the silent wrong-branch bug where `elif val Some(x) = expr:`

<!-- sdn-diagram:id=elif_pattern_binding_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=elif_pattern_binding_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

elif_pattern_binding_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=elif_pattern_binding_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# elif pattern-binding regression

Regression for the silent wrong-branch bug where `elif val Some(x) = expr:`

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/shared/control_flow/elif_pattern_binding_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Regression for the silent wrong-branch bug where `elif val Some(x) = expr:`
was mishandled in BOTH execution modes:

- the interpreter's if-let paths (`exec_if` for statements, `exec_if_core` for
  if-expressions) returned the `else` block directly when the FIRST pattern
  failed, skipping every `elif` branch entirely (silent wrong result, no error);
- the JIT HIR lowerer reused the first branch's subject for elif conditions and
  never registered the elif binding (`Unknown variable: x`, forcing interpreter
  fallback for the whole module).

Without the fix these cases return the `else` value (0) instead of the matching
elif value. Verified to FAIL on the pre-fix compiler and PASS after. Each result
is bound to an intermediate `val` before `expect` so the assertion actually
exercises the function under the test runner.

## Scenarios

### elif pattern binding

#### binds the elif value (statement form)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = pick_stmt(None, Some(Box(v: 7)))
expect(r).to_equal(7)
```

</details>

#### binds the elif value (expression form)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = pick_expr(None, Some(Box(v: 7)))
expect(r).to_equal(7)
```

</details>

#### reaches a later pattern elif in a chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = pick_third(None, None, Some(Box(v: 9)))
expect(r).to_equal(9)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
