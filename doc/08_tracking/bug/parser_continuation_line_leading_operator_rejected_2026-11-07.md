# Parser rejects nested leading-operator continuation lines; seed rejects `as *u8` casts and `@rt` decorator

Date: 2026-11-07 (round 16, lane g09). Found while porting
`src/lib/nogc_sync_mut/io/hal_buffer_dispatch.spl` from origin/chore/merge-share-history.
Seed: `D:/dev/wt/seed-r16/simple.exe` (release 725f5dc3a66).

## 1. Nested leading-operator continuation (parser)

A binary operator at the start of a continuation line is accepted for ONE level,
but when that continuation operand itself continues on a further-indented line
(a nested leading operator), the next continuation line fails to parse.

Minimal repro A (`if` statement):

    if x > 100
            or x
                > 9
            or y > 100:
        r = 1

Exact error: `Unexpected token: expected Colon, found Or at line 10, column 17`

Minimal repro B (`val` initializer):

    val eq = x
            == y
        and x
            == y

Exact error: `Unexpected token: expected expression, found Indent at line 8, column 1`

Single-level forms (`val eq = x\n        == y`, `if a\n        or b\n            > 9:`) parse fine.

Workarounds in this PR (src/lib/nogc_sync_mut/io/hal_buffer_dispatch.spl):
- line 188: `or extraction.instruction.result_capacity > RT_HAL_BUFFER_MAX_BYTES_V3` joined onto one line (was split before `>`).
- lines 212-218: `digest_exact` rebuilt as `digest_hi_exact` / `digest_lo_exact` vals combined with `and` (was a nested `==` / `and` / `==` chain), and the `val publication = if digest_exact: execution else:` form replaced by `var publication` plus an `if not digest_exact:` assignment.

Expected: a continuation line whose operand continues on a deeper-indented line parses,
exactly like the one-level case; the continuation chain ends at the line that closes the
condition (`:`) or the statement.

## 2. Seed interpreter: `0 as *u8` cast (seed)

`test/01_unit/lib/nogc_sync_mut/io/hal_device_callback_capsule_spec.spl` line ~110,
scenario "binds one explicit transport cookie and rejects stale shutdown":
`0 as *u8` / `0 as *mut u8` fail with
`semantic: type mismatch: unsupported cast target type: Pointer { kind: Shared, inner: Simple("u8") }`.
Expected: integer to raw-pointer casts evaluate (null pointer) in the interpreter.
No workaround applied; the scenario stays failing (spec is `@tag:in-development`).

## 3. Seed: `@rt(hal, ...)` decorator (seed)

`src/lib/nogc_sync_mut/io/hal_buffer_dispatch.spl` (5 functions, lines 356+) carries
`@rt(hal, operation: ..., providers: pure+c+rust, ...)`. The seed stops with
`semantic: unknown decorator `@rt` on function `hal_file_read_buffer_v3`` from
`src/compiler_rust/compiler/src/decorator_apply.rs` (`is_directive_decorator` does not list `rt`).
Expected: `rt` registered as a compiler annotation (metadata only in the interpreter).
Also missing on every ref: `src/runtime/runtime_hal_buffer_dispatch.c` and
`src/runtime/test/runtime_hal_buffer_dispatch_selfcheck.c`, which
`rt_hal_buffer_dispatch_spec.spl` reads. No workaround applied.
