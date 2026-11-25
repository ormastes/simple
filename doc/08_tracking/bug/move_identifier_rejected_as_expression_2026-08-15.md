# `move` identifier rejected in expression position ("expected expression, found Plus")

- **Date:** 2026-08-15
- **Status:** Closed (2026-11-25) — not reproducible on the committed seed; `move` parses and evaluates correctly in expression position. See the dated verification note at the bottom. (Was: OPEN, workaround applied.)
- **Component:** parser (Rust seed lexer/parser reserved-word handling)

## Symptom

`src/lib/common/mission_critical/draw_ir_packed_generation_store_v3.spl` failed to
parse with `Unexpected token: expected expression, found Plus`, silently breaking
every spec that transitively imports `common.ui.draw_ir` (all engine2d draw_ir
specs went 0-passed with 0% coverage of `draw_ir_adv.spl`).

## Root cause

A local variable named `move` cannot be used in expression position:

```
var move = found.to_u32()
while move + 1u32 < self.queue_len:   # <- "expected expression, found Plus"
```

Bisection (head -n N + parse) pinned the failure to the `while move + 1u32` line;
renaming the variable to `shift` resolves it. `move` behaves as a reserved token
in expression position even though its declaration (`var move = ...`) is
accepted — same defect family as `examples`/`and_then` named-argument rejection
(see `examples_identifier_rejected_in_named_argument_position_2026-08-10.md`).

## Workaround / fix applied

Renamed the compaction cursor `move` -> `shift` in
`src/lib/common/mission_critical/draw_ir_packed_generation_store_v3.spl`
(release() queue-compaction loop, ~line 285).

## Unblock condition

Either make `move` a plain identifier, or reject its declaration with a clear
"reserved keyword" diagnostic instead of failing at the first later use, and add
`move` to the documented reserved-keyword list in `.claude/rules/language.md`.

## Verification 2026-11-25 (p2w3-al lane, Windows) — not reproducible, closing

Runtime: committed `bin/simple.exe` (Rust bootstrap seed v1.0.0-rc.1,
38,403,072 bytes), `SIMPLE_LIB=src ... run`, Windows Git Bash, worktree at
release/1.0.0 @ 1457ddaa176.

Two standalone probes using `move` as a plain local in expression position —
including the doc's failing shape, `move` as the left operand of `+` in a
`while` condition — both parse and evaluate correctly:

```
var move = 1
var x = move + 1        # prints x=2, exit 0   (was: expected expression, found Plus)

var move = 1
var total = 0
while move + 1 < 5:     # prints total=6, exit 0
    total = total + move
    move = move + 1
```

The current deployed seed no longer treats `move` as reserved in expression
position, so the defect does not reproduce. The `shift` rename in
`draw_ir_packed_generation_store_v3.spl` stays (harmless). If a future seed
regresses this, re-open with the probe above. The residual ask — a documented
reserved-keyword list in `.claude/rules/language.md` — is documentation
hygiene, not this bug.
