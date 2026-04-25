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
