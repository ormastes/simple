# Plan 22: Future Execution in Codegen

## Goal
Make compiled futures execute their body and resolve, replacing the current stub. Align with `fn(ctx)` ABI and reuse actor outlining machinery.

## Current State
- Runtime: `rt_future_new(body_func, ctx)` runs body eagerly and sets state/result to `NIL`.
- Codegen: passes stub body pointer + nil ctx.
- Interpreter: futures run thunks and `await_result`.

## Target Design
- Outline future body as `fn(ctx: *const u8) -> RuntimeValue` (or `()`, storing result externally).
- Runtime should execute body, store result, set state=ready.
- `rt_future_await` returns stored result; if pending, blocks/spins (initial simple model).

## Steps
1. Outline future `body_block` with ctx captures (reuse Plan 20 machinery).
2. Change `rt_future_new` to call body and store its return in the future’s `result`, set `state=ready`.
3. Codegen: pass outlined body pointer + ctx; remove stub.
4. Optional: add pending/ready distinction and blocking await in runtime.
5. Tests: compiled future returning a value; await returns it; multiple awaits idempotent.

## Decisions
- Return value: either return `RuntimeValue` directly from body or write into future struct; simplest is return and store.
- Scheduling: eager execute in this phase (no async runtime).
