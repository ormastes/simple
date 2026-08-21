# `_parse_duplicate_typed_arg_signature` returned nil on a non-optional return contract (2026-08-21)

## Symptom

Running lint with a build that enforces the stricter SFFI-style return
contract (`validate_sffi_return_contract`,
`src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs:62`)
dies at ~4-7.7s with:

```
error: semantic: nil is forbidden by the non-optional return contract of '_parse_duplicate_typed_arg_signature'
```

The deployed `bin/simple` (`bin/release/x86_64-unknown-linux-gnu/simple`,
built 2026-08-21 05:10) does **not** reproduce — it lints clean. A newer seed
built the same day, `/mnt/data/.cargo-target-prof/release/simple` (built
2026-08-21 11:44), does reproduce, meaning this contract check is newer than
the deployed binary and not yet a false-negative there.

## Root cause

`sffi_return_contract` (`function_exec.rs:46-53`) classifies a declared
return type as `Optional` **only** when the parser produced `Type::Optional`,
which only the `T?` sugar produces
(`src/compiler_rust/parser/src/parser_types.rs:218,235,259,581,591`). The
explicit generic form `Option<T>` parses to a plain generic `Type::Simple`
(or `Type::Generic`), which the contract classifies as `NonOptional`.

`_parse_duplicate_typed_arg_signature` was declared:

```
fn _parse_duplicate_typed_arg_signature(ctx: LineContext) -> Option<DuplicateTypedArgSignature>:
```

in both:

- `src/lib/nogc_sync_mut/tooling/easy_fix/rules.spl:136`
- `src/compiler/90.tools/fix/rules/impl_/lint_code.spl:93`

The function legitimately `return nil`s on almost every input (no `(`, no
matching paren, empty name, `< 2` typed params, no duplicate types) before
ever reaching a `Some(...)` at the end. Under the stricter contract this now
faults, because the generic `Option<T>` annotation is (mis)classified
`NonOptional`.

This function itself was not touched by 8d3b7d009b9 ("perf(lint): native
find() in duplicate-typed-args scan") — that commit rewrote
`_short_find_text_from` and `_collect_line_call_replacements` to use native
`find()` instead of a per-character interpreted loop. The perf commit is
implicated only as the trigger that made this file link into the newer
build/JIT path that now enforces the contract; the return-type mismatch
itself predates that commit.

## Fix

Changed the declared return type from `Option<DuplicateTypedArgSignature>` to
`DuplicateTypedArgSignature?` (the sugar form) in both files — no other
change. The function body is untouched: it still `return nil`s on every miss
path and returns `Some(DuplicateTypedArgSignature(...))` on the match path
(both forms are accepted for a `T?`-declared function elsewhere in the
codebase, e.g. `cli_fs_find` in `src/lib/common/cli_fs_commands.spl:25-30`).
Call sites (`match sig: case Some(found): ... case nil: pass`) needed no
change.

## Evidence

Pre-fix, on the strict binary:

```
$ /mnt/data/.cargo-target-prof/release/simple lint src/lib/common/base_encoding.spl
...
error: semantic: nil is forbidden by the non-optional return contract of '_parse_duplicate_typed_arg_signature'
rc=1 wall=4.18
```

Post-fix, same binary:

```
$ /mnt/data/.cargo-target-prof/release/simple lint src/lib/common/base_encoding.spl
...
Lint passed: all files clean
rc=0 wall=7.50
```

Regression spec added:
`test/01_unit/lib/nogc_sync_mut/tooling/easy_fix/duplicate_typed_arg_signature_nil_miss_spec.spl`
— exercises a signature with no duplicate parameter types and a
single-parameter signature (both walk every early `return nil` and never
reach `Some(...)`).

- Pre-fix, strict binary: `2 examples, 2 failures` (both fail with the exact
  `nil is forbidden...` message).
- Pre-fix, deployed `bin/simple`: `2 examples, 0 failures` (does not
  reproduce — confirms the deployed binary predates this contract check).
- Post-fix, strict binary: `2 examples, 0 failures`.

Existing easy_fix specs re-run clean under the fix:
`test/01_unit/compiler/lint/collection_easy_fix_spec.spl` (4/4 pass, no
regression). `test/01_unit/compiler/lint/lint_cli_duplicate_typed_args_contract_check.spl`
fails both before and after this change (verified via `git stash` on an
unmodified tree) — a pre-existing, unrelated failure, not introduced here.
