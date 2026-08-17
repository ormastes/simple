## Re-verified 2026-08-17 — STILL OPEN

Minimal repro (`var move = 3u32` then `while move + 1u32 < 10u32:`) still fails:
```
error: compile failed: parse: Unexpected token: expected expression, found Plus
```
Same defect class as `pub`/`examples`: a reserved token rejected at the USE
site. Blocker: the fix is in the Rust seed lexer/parser
(`src/compiler_rust/parser/src/expressions/helpers.rs` family) and cannot be
verified without a seed rebuild + redeploy.

# `move` identifier rejected in expression position ("expected expression, found Plus")

- **Date:** 2026-08-15
- **Status:** OPEN (workaround applied)
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
