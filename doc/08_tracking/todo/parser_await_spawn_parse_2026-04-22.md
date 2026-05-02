# Parser Await Spawn Parse

**Date:** 2026-04-22
**Todo:** `doc/08_tracking/todo/todo_db.sdn` row 185
**Status:** Closed

## Research

- `test/unit/compiler/parser/parser_await_spawn_spec.spl` only ran a skip wrapper and kept the intended lexer/parser tests commented out.
- `src/compiler/10.frontend/core/parser_primary.spl` already parses `await` and `spawn` into `expr_await` and `expr_spawn`.
- `compiler.core.parser` exports `parser_init` and `parse_expr`; `compiler.core.ast` exports expression tags and accessors needed for direct assertions.

## Plan

- Replace the skipped/commented spec with active parser-level assertions.
- Verify `await fetch()` produces `EXPR_AWAIT` with an inner expression.
- Verify `spawn Worker()` produces `EXPR_SPAWN` with an inner expression.
- Keep a small lexer keyword check for await/spawn target-token coverage.
- Close row 185 after lint and focused spec verification.

## Fix

- Rewrote `parser_await_spawn_spec.spl` as active tests.
- Removed the stale commented TODO body.
- Closed `todo_db.sdn` row 185.

## Verification

```sh
bin/simple lint test/unit/compiler/parser/parser_await_spawn_spec.spl
bin/simple test test/unit/compiler/parser/parser_await_spawn_spec.spl
```
