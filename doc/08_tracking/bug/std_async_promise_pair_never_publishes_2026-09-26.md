# `std.async.Promise` does not publish its result to its returned `Future`

**Status:** open; source defect confirmed on committed `5390c648662` (2026-09-26). A repair and behavioral spec are drafted in the isolated SOSIX worktree, but no source-matched pure-Simple run has admitted them. This is the RU-021 Future/Promise compatibility gap, not a claim that the whole canonical task bridge is fixed.

## Evidence

`src/lib/nogc_async_mut/async/promise.spl::new` returns `Future.pending<T>()` and a separate `Promise(completed: false)`. Its `complete(value)` only changes `self.completed`; it never stores `value` in the Future. `src/lib/nogc_async_mut/async/future.spl::poll` returns its fixed `poll_result`, so the example in `async/promise.spl` and `async/__init__.spl` cannot become ready through this path. Production `Future`/`Promise` had no direct behavioral spec; similarly named intensive specs define inline test doubles.

This differs from [the July anonymous-tuple report](async_spec_promise_future_anon_tuple_state_inconsistency_2026-07-20.md), which studies an inline test double and unstable successive polls. The production defect is visible before tuple identity is considered: the promise has no reference to its future or shared result cell at all.

## Required repair gate

1. A real `std.async.promise.Promise<i64>.new()` pair starts pending, then `complete(42)` makes the *returned* Future yield `Poll.Ready(42)`; a second completion returns false and preserves 42.
2. Distinct pairs do not share state. Both tuple-destructured and indexed pair access must work in the admitted interpreter and native engines.
3. Document the legacy Future's missing waker/cancellation state honestly. RU-021 remains open until task-backed wake, owned result storage, retirement, and static/pool profiles have their own evidence.

## Verification attempts and blocker

- The installed `bin/release/aarch64-apple-darwin/simple` rejects existing `src/lib/nogc_sync_mut/io/process_ops.spl` syntax while setting up the focused spec. The executable identifies itself as a Rust-built bootstrap seed when used for `check`, so it is inadmissible under `.claude/rules/bootstrap.md`.
- The newer `bin/release/aarch64-apple-darwin-macho/simple` test command exited 139 during setup; its direct `run` command also identifies itself as a Rust-built bootstrap seed. Its diagnostic interpreter probe printed `false`, `true`, `42`, `false` after the draft patch, but this is **not** pure-Simple verification.
- `bin/local/phase2-aarch64-apple-darwin/simple` exists, but no matching admission receipt was found for a general SPipe/test-runner claim. Do not substitute it for the required deployed self-hosted runner.

Next: produce or identify an admitted source-matched pure-Simple test runner, run `test/01_unit/lib/nogc_async_mut/async_promise_pair_spec.spl` in interpreter and native modes, then execute the required `src/lib`, compiler, MCP/LSP and runtime smoke gates before merging the draft.
