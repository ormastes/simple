# Inline `if c: X as T else: Y` loses the else arm (2026-10-05)

**Status:** fixed in the Rust seed parser (2026-10-05, `work/inline-if-as-cast-else`).
The pure-Simple parser was measured correct and needed no change. Takes effect
for a seed binary rebuilt from this commit; the linker's parenthesized sites
stay (still valid).

## Root cause

Rust seed only. `x as T else: f` is a real postfix form in the seed
(`Expr::CastElse`, cast with fallback, `parser/src/expressions/postfix.rs`
`TokenKind::As` arm). The inline-if THEN arm was parsed with a plain
`parse_expression()`, so after `as i64` the cast-suffix match saw `else`,
consumed `else: 7` as the cast fallback, and the `if` ended with
`else_branch: None`:

```
If { condition: c, then_branch: CastElse { expr: x, target_type: i64, fallback_fn: 7 }, else_branch: None }
```

A false condition therefore evaluated the missing else (JIT `0`, interpreter
`nil`). The `then ... else 7` form failed to parse outright (`expected Colon`),
and so did a ternary whose condition ends in a cast (`a if n as bool else b`).

The pure-Simple parser (`src/compiler/10.frontend/core/parser_expr.spl`
`parse_unary` cast loop) has no `as T else:` suffix and stops the cast at
`else`; `test/01_unit/compiler/parser/inline_if_as_cast_else_spec.spl` was
11/11 green against it before any change. The Stage 2 symptom therefore did not
come from that parser; the binary that misread the linker source was compiled
through the seed's parser (that path is not re-measured here, and no Stage 2
rebuild was done).

## Fix

`Parser::no_cast_else` (`parser_impl/core.rs`) disables the `as T else:` suffix.
`parse_without_cast_else` (`expressions/helpers.rs`) sets it, then restores the
previous value, also on error, around:

- the inline then arm of `parse_if_expr` (expression and diverging-statement forms),
- the inline then arm of statement `parse_if` (expression, assignment and
  `return`/`break` forms) and inline `elif` bodies,
- the condition of the postfix ternary `a if c else b`.

The else arm and block bodies are unchanged, so `val v = x as T else: f`,
`if c: 7 else: x as T else: f` and `as T else:` inside a block-form arm still
parse as `CastElse`. Census: `grep -rnE " as [A-Za-z0-9_<>]+ else:" src --include=*.spl | grep -vE "(if|elif) [^:]+:"`
finds 0 standalone `CastElse` uses in `src/`, so existing code cannot change
behaviour.

## Evidence

- `cargo test -p simple-parser --lib inline_if_as_cast_else`
  (`parser/src/inline_if_as_cast_else_test.rs`, 12 tests): with the fix
  reverted, 2 passed / 10 failed. With the fix, 12/12 passed. The full
  `cargo test -p simple-parser --no-fail-fast` has the same 5 failures before and
  after (`test_python_def_detection`, `test_multiple_decorators`,
  `test_danger_block_is_unsafe_boundary_not_call`,
  `unsafe_block_is_valid_in_value_position_and_calls_stay_calls`,
  `stage2_failure_consumers_parse_strictly`); none was introduced by this fix.
- Probe (then-arm, indexed, both arms, `return`, nested, call argument) on the
  seed, before → after rebuild (`cargo build --profile bootstrap -p simple-driver`):
  JIT `g1(false)=0, g2(true)=3, g5(false,true)=0` → `7, 9, 4`. Interpreter:
  `nil is forbidden by the non-optional return contract` → all values correct.
- `test/01_unit/compiler/parser/inline_if_as_cast_else_spec.spl`: 13/13 on the
  rebuilt seed (2 runtime witnesses + 11 pure-Simple AST shapes);
  `test/01_unit/compiler/backend/linker/simpleos_internal_entry_spec.spl` 2/2.

## Symptom

An inline if-expression whose THEN arm ends in an `as` cast is miscompiled:

```simple
fn g1(c: bool, x: i64) -> i64:
    val v = if c: x as i64 else: 7
    v
fn g2(c: bool, a: [u8]) -> i64:
    val v = if c: a[1] as i64 else: 7
    v
```

Measured with the x86_64 seed (`/root/work/host-seed-target/bootstrap/simple run`),
`a = [5, 9]`:

| call | expected | JIT | interpreter |
|---|---|---|---|
| `g1(true, 3)` | 3 | 3 | — |
| `g1(false, 3)` | 7 | **0** | **nil** (`nil is forbidden by the non-optional return contract`) |
| `g2(true, a)` | 9 | **3** | — |
| `g2(false, a)` | 7 | **0** | — |
| `if c: 7 else: a[1] as i64` | ok | ok | ok |
| `if c: (a[1] as i64) else: 7` | ok | ok | ok |

A cast only in the ELSE arm, or a parenthesized THEN-arm cast, is correct.

## Impact found

`src/compiler/70.backend/linker/elf_parser.spl:283-284` read ELF symbol
`st_info`/`st_other` with this form, so every ELF64 symbol parsed with binding
LOCAL and no global entered the resolver. The internal ELF engine therefore
failed every link with `entry symbol not defined: _start` — first seen as the
SimpleOS x86_64 user internal link failure from the pure-Simple Stage 2
candidate (built from `release/1.0` `a5cda768103`). That was first read as the
pure-Simple compiler being affected too. The parser-level measurement under
Root cause shows the pure-Simple parser is correct.

Fixed by parenthesizing the cast arms in the 6 linker sites
(`elf_parser.spl`, `elf/stream_emit.spl` x2, `elf/archive_file.spl`,
`elf/elf_file_reader.spl`); regression spec
`test/01_unit/compiler/backend/linker/simpleos_internal_entry_spec.spl`.

## Other call sites (same form, outside the linker): now safe

These were latent miscompiles under the old seed. They are now safe once the
seed is rebuilt from the fix commit; no source edit is needed. Census
(26 sites at the fix commit):
`grep -rnE "if [^:]+: [^()]+ as [a-zA-Z0-9_<>]+ else:" src --include=*.spl`. Examples:
`src/os/sosix/process.spl:141`, `src/os/kernel/ipc/syscall_ipc.spl:113`,
`src/lib/skia/feature/glyph/subpixel.spl:33-55`,
`src/lib/nogc_async_mut/link_working_set/file_store.spl:173`,
`src/lib/gc_async_mut/gpu/engine2d/draw_ir_box_effects.spl:302-305`.
The parenthesized linker sites are kept on purpose. Both spellings are valid.
