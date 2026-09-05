# Parser Await Spawn

> Verifies that the core parser creates await and spawn expression nodes.

<!-- sdn-diagram:id=parser_await_spawn_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_await_spawn_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_await_spawn_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_await_spawn_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Await Spawn

Verifies that the core parser creates await and spawn expression nodes.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/parser/parser_await_spawn_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies that the core parser creates await and spawn expression nodes.

## Scenarios

### Parser Await Spawn
_Parser coverage for async expression front-end forms._

#### parses await expression nodes

- parser init
   - Expected: expr_get_tag(expr) equals `EXPR_AWAIT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
parser_init("await fetch()")
val expr = parse_expr()
expect(expr_get_tag(expr)).to_equal(EXPR_AWAIT)
expect(expr_get_left(expr)).to_be_greater_than(0)
```

</details>

#### parses spawn expression nodes

- parser init
   - Expected: expr_get_tag(expr) equals `EXPR_SPAWN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
parser_init("spawn Worker()")
val expr = parse_expr()
expect(expr_get_tag(expr)).to_equal(EXPR_SPAWN)
expect(expr_get_left(expr)).to_be_greater_than(0)
```

</details>

#### keeps await and spawn operands

- parser init
   - Expected: expr_get_tag(await_call) equals `EXPR_CALL`
   - Expected: expr_get_str(expr_get_left(await_call)) equals `async_operation`
- parser init
   - Expected: expr_get_tag(spawn_call) equals `EXPR_CALL`
   - Expected: expr_get_str(expr_get_left(spawn_call)) equals `Worker`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
parser_init("await async_operation()")
val await_expr = parse_expr()
val await_call = expr_get_left(await_expr)
expect(expr_get_tag(await_call)).to_equal(EXPR_CALL)
expect(expr_get_str(expr_get_left(await_call))).to_equal("async_operation")

parser_init("spawn Worker()")
val spawn_expr = parse_expr()
val spawn_call = expr_get_left(spawn_expr)
expect(expr_get_tag(spawn_call)).to_equal(EXPR_CALL)
expect(expr_get_str(expr_get_left(spawn_call))).to_equal("Worker")
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
