# Parser: member-target assignment in single-line colon-suffixed `if`

**Priority:** medium (grammar gap — pushes users to verbose alternatives)
**Filed:** 2026-04-25
**Component:** parser (Rust bootstrap + self-hosted)
**Discovered by:** game2d-framework SStack Phase 7 (rerun) verification

## Description

The single-line colon-suffixed `if cond: <stmt>` form rejects member-target
assignment statements. Local-scalar targets parse fine, but any LHS containing
a `.field` access (whether on `self` or a local var) fails with a parser error
on the `=` / `+=` / `-=` token. This forces users to either expand to a
multi-line `if` block or hoist the member into a local scalar — both inflate
LOC for what is otherwise a one-line LÖVE-style movement idiom.

## Minimal repro (3 lines)

```
class V:
    x: f32

fn main():
    var d = V(x: 0.0)
    if true: d.x = d.x - 1.0
```

## Expected

Parses cleanly (analogous to `if true: dx = dx - 1.0` for a local scalar `dx`,
which does parse).

## Actual

```
error: parse failed in /tmp/repro.spl: Unexpected token: expected expression, found Assign
```

The same shape with `+=` / `-=` instead of `=` fails analogously with
`expected expression, found MinusAssign` / `PlusAssign`. Self-member targets
fail identically:

```
fn bump(self, dt: f32):
    if dt > 0.0: self.x = self.x + 1.0
```

→ `Unexpected token: expected expression, found Assign`.

## Workaround currently in use

Hoist the member into a scalar local, mutate the scalar in single-line `if`s,
then write back once:

```
fn update(self, dt: f32):
    var dx: f32 = 0.0
    if cond_left:  dx -= 1.0
    if cond_right: dx += 1.0
    self.pos = g.Vec2(x: self.pos.x + dx * 120.0 * dt, y: self.pos.y)
```

Alternative workaround: expand each branch to a 3-line `if cond:` block.

## Reference

- First seen: `examples/game2d/hello/main.spl` (game2d-framework Phase 7 rerun
  V1 NO-GO).
- Forms tested at `/tmp/m5c_{A,B,C,D}.spl` during Phase 5c micro-repros:
  - `d.x = d.x - 1.0` (local member, simple) — FAIL
  - `d.x -= 1.0` (local member, compound) — FAIL
  - `dx -= 1.0` (local scalar, compound) — OK
  - `dx = dx - 1.0` (local scalar, simple) — OK

## Suggested fix direction

Parser's single-line `if-suffix` arm appears to dispatch the inline body
through `parse_expression` rather than `parse_statement`. A `.field` LHS is
recognized as a postfix expression, but the trailing `=` / `+=` / `-=` is
then rejected because expression context doesn't admit assignment operators.
Routing the inline body through `parse_simple_statement` (the same path used
for full-line indented statements) should close the gap without grammar
ambiguity.

## Resolved 2026-04-25

Fixed in `src/compiler_rust/parser/src/stmt_parsing/control_flow.rs` by
extending `is_inline_assignment()` to recognize member-target lvalues
(`ident[.field]+ =/+=/-=/*=//=/%=`) using a save/restore lookahead that
pushes consumed tokens back to `pending_tokens` (lexer cannot rewind, so the
push-back is required — see `peek_is_struct_init` for the same pattern).
Also added `Self_` to the head identifier-like set so `if cond: self.x =
...` parses too. The detection-only change keeps `parse_item()` as the body
parser, which already handles member-target assignment statements
correctly outside the `if`-suffix context.

The self-hosted parser at
`src/compiler/10.frontend/core/parser_stmts.spl` does not have a
single-line colon-suffix `if` form (its `parse_if_stmt` always calls
`parse_block()`), so no parallel edit is needed. Component scope reduces
to "parser (Rust bootstrap)" only.

Verification:
- Bug minimal repro `if true: d.x = d.x - 1.0` → parses, runs.
- Compound member assign `if true: d.x -= 1.0` → parses, runs.
- Deep chain `if true: o.inner.n -= 1` → parses, runs.
- Local-scalar `if true: x = 5` / `if true: x -= 1` → unchanged, still passes.
- Bare-expression form `var x = if 1 < 2: 10 else: 20` → unchanged.
- Statement form `if true: print("hi")` → unchanged.
- All 9 game2d specs PASS.
- `test/feature/usage/control_flow_if_else_spec.spl` (11 tests) PASS.
- `test/unit/compiler/parser/parser_attribute_spec.spl` (18) PASS.
- `test/unit/compiler/parser/parser_actor_spec.spl` (16) PASS.

Note: `test/util/game2d_parse_repro{,_b}.spl` track a *different* failure
(member-name in `class T : g.App` extends), tracked under
`game2d_impl_block_parse_repair`. They were never repros for this bug.
