# Runtime errors carry no "Call stack:" section on the live interpreter (2026-08-17)

Status: OPEN — spec is legitimately RED, do not weaken it.

## Summary
`test/03_system/feature/interpreter/runtime_error_stack_spec.spl` asserts that a
runtime error prints a `Runtime error` header followed by a `Call stack:` section
naming each frame (`level1`, `level2`, `level3`). On the live compiler it does
not.

## Repro
```
bin/simple run test/03_system/feature/interpreter/sample/runtime_error_stack.spl
```
Observed (exit 1):
```
[INFO] JIT compilation failed, falling back to interpreter: semantic: function `missing_fn` not found
error[E1002]: function `missing_fn` not found
```
Expected: a `Runtime error` header and a `Call stack:` section with `level1`,
`level2`, `level3` frames.

## Why it reads this way
`missing_fn` is resolved — and rejected — at SEMANTIC analysis, before any frame
exists, so the call chain is never on a stack to print. The spec's premise is
that an *undefined function reached at runtime* produces a stack trace; the live
front end turns that into a compile-time diagnostic instead.

Two candidate resolutions, both real work, neither a spec edit:
1. Emit a call stack for genuine runtime errors and give this fixture a failure
   the front end cannot catch statically (then the fixture needs updating too).
2. Decide that this class is correctly a static error and re-scope the spec to a
   failure that is genuinely dynamic — still requiring the `Call stack:` section
   to exist for that case.

## History — this spec has never passed
Before 2026-08-17 it was doubly broken and therefore vacuous:
- it spawned `src/app/interpreter/main.spl`, a tree declared REMOVED since
  2026-02 that did not parse
  (`app_interpreter_tree_declared_removed_but_still_on_disk_2026-08-10.md`);
- it named the fixture `test/system/interpreter/sample/runtime_error_stack.spl`,
  a path that does not exist — the tracked fixture is under
  `test/03_system/feature/interpreter/sample/`.

Both were repointed at the live path in the app.interpreter deletion commit, at
which point the spec started failing on its actual assertion rather than on a
missing file. That is the intended state: a correct spec failing against a real
gap, per `.claude/rules/testing.md`.

## Unblock condition
The interpreter emits a `Call stack:` section with per-frame entries for runtime
errors. Then this spec goes green with no change to its assertions.

## Content re-verification 2026-08-17 (m4_compiler_spl lane) — STILL OPEN, refined

The triage row's evidence line ("grep for `Call stack:` across `src/` returns
nothing") is now **stale**, but the bug is **not** fixed. Current source:

- `src/compiler/95.interp/mir_interpreter.spl:141-153` defines
  `MirInterpreter.call_stack_trace()`, which renders exactly the
  `Call stack:` / `  #<i> <fn>` section this doc asks for.
- `:155-165` defines `format_error(err)`, joining the message head with that
  trace.
- `CallFrame.function_name` (`:64-66`) exists specifically to make the frames
  nameable, and its comment cites this doc by name.

So the machinery is written. The defect is that it is **wired to nothing**:

    grep -rn "format_error\|call_stack_trace" src/compiler/95.interp src/app
    -> only the three definition lines in mir_interpreter.spl; ZERO call sites.

`format_error` has no callers anywhere in `src/`, so no error-reporting path
ever reaches it and the rendered section is never printed. This is the same
"designed, implemented, exported, called by no one" shape recorded for
`interface_digest_of` in `.claude/rules/commands.md`.

Second, independent blocker on proving a fix: the deployed `bin/simple` is the
**Rust seed**, so the interpreter that actually prints a runtime error for
`bin/simple run` is the Rust one, not this pure-Simple `MirInterpreter`. Wiring
`format_error` into `95.interp` therefore cannot be shown green by running the
named reproducer under the current binary.

**Verdict: OPEN / UNVERIFIED.** No `Results:` line was obtained; no `.spl` was
changed by this lane. Unblock condition unchanged, plus an explicit first step:
give `format_error` a caller on the interpreter's error-reporting path, and
re-verify on a self-hosted binary rather than the seed.
