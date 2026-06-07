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
| Source | `test/01_unit/compiler/parser/parser_await_spawn_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies that the core parser creates await and spawn expression nodes.

## Scenarios

### Parser Await Spawn
_Parser coverage for async expression front-end forms._

#### parses await expression nodes

1. parser init
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

1. parser init
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

#### lexes await and spawn keywords before identifiers

1. var await lexer = lexer new
   - Expected: await_token.kind equals `TOK_KW_AWAIT`
   - Expected: await_target.kind equals `TOK_IDENT`
   - Expected: await_target.text equals `async_operation`
2. var spawn lexer = lexer new
   - Expected: spawn_token.kind equals `TOK_KW_SPAWN`
   - Expected: spawn_target.kind equals `TOK_IDENT`
   - Expected: spawn_target.text equals `Worker`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var await_lexer = lexer_new("await async_operation()")
val await_token = lexer_next_token(await_lexer)
val await_target = lexer_next_token(await_lexer)
expect(await_token.kind).to_equal(TOK_KW_AWAIT)
expect(await_target.kind).to_equal(TOK_IDENT)
expect(await_target.text).to_equal("async_operation")

var spawn_lexer = lexer_new("spawn Worker()")
val spawn_token = lexer_next_token(spawn_lexer)
val spawn_target = lexer_next_token(spawn_lexer)
expect(spawn_token.kind).to_equal(TOK_KW_SPAWN)
expect(spawn_target.kind).to_equal(TOK_IDENT)
expect(spawn_target.text).to_equal("Worker")
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
