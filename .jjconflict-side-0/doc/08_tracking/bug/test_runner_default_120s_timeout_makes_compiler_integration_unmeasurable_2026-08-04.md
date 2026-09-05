# `test/02_integration/compiler/` was unmeasurable: the runner's 120 s default per-file timeout kills a 152 s spec

**Status:** FIXED (parser half) / OPEN (timeout default + import cost)
**Found:** 2026-08-04

## Symptom

Every prior attempt to measure `test/02_integration/compiler/` "died at
`import_syntax_spec.spl`". The suspected cause was the filed
`interpreter_strbytes_not_indexable_aborts_batch_test_runs_2026-08-04`. It is
not that.

```
$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple test --no-cache test/02_integration/compiler/import_syntax_spec.spl
… Process timed out          # exit 255, ~300 s wall
```

`SIMPLE_TIMEOUT_SECONDS=0` is honoured (`test_runner_main.spl:662-666` skips the
override when the value is exactly `"0"`), but it only governs
`kill_simple_monitor`. The **per-test-file** timeout is a separate knob whose
default is 120 s (`test_runner_single.spl:129`, `var timeout_secs = 120`), and
"Process timed out" here is the *child* subprocess timeout from
`src/compiler_rust/compiler/src/interpreter_extern/system.rs:165`.

`import_syntax_spec.spl` is 35 lines with 5 examples. It needs **152 s** under
the runner, so it was killed every time and the whole directory run aborted.

Raise the per-file timeout and it passes outright:

```
$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple test --no-cache --timeout 800 test/02_integration/compiler/import_syntax_spec.spl
Results: 5 total, 5 passed, 0 failed        # 2m32s
```

The whole directory then measures for the first time:

```
$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple test --no-cache --timeout 800 test/02_integration/compiler
Results: 443 total, 387 passed, 56 failed
```

## Root causes

**1. `--timeout=N` was rejected by the directory runner (FIXED).**
`--timeout 800` (space) worked; `--timeout=800` (equals) exited 2 with
`Error: unknown option: --timeout=800`, because
`src/lib/nogc_sync_mut/test_runner/test_runner_args.spl` listed neither
`--timeout=` nor `--seed=` nor `--format=` in its `known` set (`:130-167`),
while `test_runner_single.spl:138` accepted both spellings for single files.
The same flag therefore worked on one spec and aborted on the directory.
Fixed: both spellings now parse, with matching empty-value and invalid-value
validation. Verified from source (`test_args_validation_error` +
`parse_test_args` over 11 cases). **The deployed `bin/simple` still carries the
old parser — the fix takes effect after the next bootstrap.**

Writing the `=`-form parse also uncovered
`doc/08_tracking/bug/jit_substring_chained_to_int_returns_pointer_2026-08-04.md`:
`arg.substring(10).to_int()` returned `2363156932769` (a pointer) instead of
`800`, so the parse is written with an intermediate typed `val`.

**2. The 120 s default is too low for this directory (OPEN).** It is not
`import_syntax_spec` that is unusual — a bare `use app.io.{env_get, env_set,
shell}` with a one-line `main` takes **46 s** through `bin/simple run`. The
`app.io` module graph costs ~46 s to bring up and ~150 s under the runner's
interpreter. Until that import cost comes down, any spec touching `app.io`
exceeds the default and reads as a hang rather than as a slow import.

## Why not fixed now

Raising the global default trades one failure mode (unmeasurable directories)
for another (real hangs taking 800 s to surface); the right fix is to make the
`app.io` import cheap, which is a module-loading lane. Until then, measuring
`test/02_integration/compiler/` requires an explicit `--timeout 800`.
