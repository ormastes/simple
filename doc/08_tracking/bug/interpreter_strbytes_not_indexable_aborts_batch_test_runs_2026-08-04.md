# Interpreter cannot index/slice `Value::StrBytes`, aborting every batch `simple test` run

- **ID:** `interpreter_strbytes_not_indexable_aborts_batch_test_runs_2026-08-04`
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Found:** 2026-08-04
- **Severity:** critical (a whole-directory `simple test` run dies at the first
  affected file and reports **no** verdict for the remaining files)

## Symptom

Minimal repro — slice a text at a byte offset that splits a multi-byte
codepoint, then slice the result again:

```
# scratch.spl
fn main():
    val a = "日本語"
    val b = a[0:2]     # splits U+65E5 (e6 97 a5) mid-codepoint
    print b.len()      # 2
    val c = b[0:1]     # <-- dies here
    print c.len()
```

```
$ SIMPLE_EXECUTION_MODE=interpret bin/simple run scratch.spl
2
error: semantic: invalid operation: cannot slice value of type str with step
```

Expected: `2` then `1` (the JIT lane, `bin/simple run` with no
`SIMPLE_EXECUTION_MODE`, prints exactly that). Actual: a hard semantic error
that terminates the process.

The scalar-index form of the same hole reports the sibling message
`invalid operation: cannot index value of type str`.

### How it surfaces in practice

`bin/simple test <directory>` aborts mid-run:

```
$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple test test/01_unit/compiler_core --no-cache
Running 111 test file(s) [mode: interpreter]...
  PASS  test/01_unit/compiler_core/annotation_intrinsics_spec.spl (4 passed, 324ms)
  PASS  test/01_unit/compiler_core/ast_clone_spec.spl (5 passed, 252ms)
  PASS  test/01_unit/compiler_core/ast_coverage_spec.spl (10 passed, 284ms)
error: semantic: invalid operation: cannot index value of type str
```

3 of 111 files reported; the run is over. Reproduced identically on three
consecutive runs. The verdict line never appears, so a caller that only greps
for `Results:` sees *nothing*, and a caller that trusts the exit code sees a
plain `1` indistinguishable from an ordinary red run. The same abort happens on
any directory whose 4th-or-later spec produces the triggering text; it is not
specific to `compiler_core`.

Bisected with temporary prints (since removed): the abort is inside
`parse_test_output` (`src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl:177`),
which byte-walks the captured child output with `s[i:i+1]` /
`s[i:i+klen]` (`find_raw`, `extract_number_before`,
`extract_number_after_colon`, and `strip_ansi` in
`src/lib/nogc_sync_mut/test_runner/test_runner_files.spl:26`). Those walks are
correct pure-Simple code — byte-indexed slicing is the documented semantics of
`text[a:b]` — they simply cannot survive the hole below once the child output
contains a multi-byte character (the BDD `✓`/`✗` markers, U+2713/U+2717).

## Root cause

`Value::StrBytes` is a first-class text value the interpreter *produces* but
never *accepts* as an index/slice receiver.

- It is produced at
  `src/compiler_rust/compiler/src/interpreter/expr/collections.rs:432-446`
  (`Expr::Index` with a range on a `Value::Str`): a range that splits a
  codepoint deliberately preserves the raw bytes via
  `Value::text_from_bytes(sliced)`, which yields `Value::StrBytes` when the byte
  run is not valid UTF-8. The same is done in the step-slice arm at
  `collections.rs:918-944`.
- It is *not* consumed: every one of the three receiver matches in that file
  lists `Value::Str(s)` and no `Value::StrBytes` arm, so a `StrBytes` receiver
  falls through to the catch-all:
  - `collections.rs:412` (range index) — falls to its `_` arm,
  - `collections.rs:631` (`Value::Str(s) => require_integer_index_value(...)`,
    scalar index) — `_` arm at `collections.rs:673-681` emits
    `invalid operation: cannot index value of type str`,
  - `collections.rs:916` (slice with step) — `_` arm at `collections.rs:948-960`
    emits `invalid operation: cannot slice value of type str with step`.

Both messages say `str` because `Value::StrBytes(_) => "str"` in
`src/compiler_rust/compiler/src/value_impl.rs:589` — the diagnostic therefore
names a type that the very next line of the match *does* support, which is why
the error reads as impossible.

`src/compiler_rust/compiler/src/interpreter_method/mod.rs:1909` already does the
right thing for the method lane (`matches!(recv_val, Value::Str(_) |
Value::StrBytes(_))`), so `.slice()`/`.substring()` work on a `StrBytes` while
the bracket forms do not — the two lanes disagree on the same value.

This is provably seed-only: the message text exists nowhere in `src/compiler/`
(the pure-Simple compiler); `grep -rn "cannot index value of type" src/compiler/`
matches one comment and no emitter. The deployed `bin/simple`
(`bin/release/x86_64-unknown-linux-gnu/simple`, 2026-08-04) prints the
`this Rust-built Simple binary is a bootstrap seed only` banner, so `simple test`
currently executes its whole runner through this interpreter.

## Why not fixed now

The fix is three added match arms in
`src/compiler_rust/compiler/src/interpreter/expr/collections.rs` (treat
`Value::StrBytes(b)` exactly like `Value::Str(s).as_bytes()` in the range-index,
scalar-index and step-slice arms). That is small, but landing it requires
rebuilding the Rust seed **and** replacing the live `bin/simple` that other
concurrent sessions in this working copy are actively running tests against;
overwriting it mid-flight breaks them ("Text file busy" / partially-written
binary). Deferred to a session that owns the tree.

Workaround for measurement in the meantime: run each spec directly,
`SIMPLE_EXECUTION_MODE=interpret bin/simple run <spec>.spl`, and sum the
`N examples, M failures` lines — this is exactly what the batch runner does per
file, minus the crashing output parser, and it agrees file-for-file with the
runner where the runner survives (verified on
`test/00_formal_verification/compiler`, 16 files).
