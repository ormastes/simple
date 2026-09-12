# `TestDatabase` is imported from a module that does not define it, and silently becomes `{}`

- Status: OPEN (2026-09-12)
- Area: app / test_runner_new, compiler / module resolution
- Binary: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`, sha256 prefix `3d120a6f`

## Symptom

```
semantic: method `empty` not found on type `dict` (receiver value: {})
```

`TestDatabase` evaluates to an empty dict rather than a type, so
`TestDatabase.empty()` cannot be called from any spec.

## Repro

```bash
cd /home/yoon/dev/simple-todofix-2
cat > /tmp/probe_db.spl <<'SPL'
use app.test_runner_new.test_db_core.{TestDatabase}

fn main():
    val db = TestDatabase.empty()
    print("runs=" + db.test_runs.len().to_text())
SPL
bin/simple run /tmp/probe_db.spl
# -> error: semantic: method `empty` not found on type `dict` (receiver value: {})
```

## Cause

`src/app/test_runner_new/test_db_validation.spl:10` reads:

```
use std.test_runner.test_db_core (TestDatabase)
```

`src/lib/nogc_sync_mut/test_runner/test_db_core.spl` (the module behind
`std.test_runner.test_db_core`) contains **zero** occurrences of `TestDatabase`
— it defines `RunnerTestDbCore`. `grep -n TestDatabase
src/lib/nogc_sync_mut/test_runner/test_db_core.spl` returns nothing.

The struct named `TestDatabase` lives in `src/app/test_runner_new/test_db_core.spl:19`,
but importing it from there fails the same way, so the app-side module path does
not resolve to that file either.

Two defects are stacked here:

1. the import at `test_db_validation.spl:10` names a symbol the target module
   does not provide;
2. an unresolved `use` binds the name to `{}` instead of failing. The compiler
   does emit a `[use-warning] '<name>' is named in `use ...` but module '<path>'
   does not provide it` line for some modules, but the program still runs with a
   dict in place of the type, and the error only surfaces at the first method
   call — far from the import.

## Impact

`validate_database(db: TestDatabase)` and every other signature in
`src/app/test_runner_new/test_db_validation.spl` is typed against a phantom.
`test/01_unit/app/tooling/test_db_validation_spec.spl` calls
`TestDatabase.empty()` at 9+ sites and is affected.

Workaround used by `test/01_unit/app/tooling/test_db_integrity_spec.spl`:
build `RunnerTestDbCore` instead — `validate_database`, `cleanup_stale_runs`,
`prune_runs` and `list_runs` all accept it.

## Not fixed here

Out of the todo-fix shard's scope: picking the right type is an owner decision
(rename `RunnerTestDbCore`, re-export it as `TestDatabase`, or repoint the
import), and the fail-open `use` is a compiler change.
