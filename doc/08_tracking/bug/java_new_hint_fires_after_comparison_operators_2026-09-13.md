# A `new` identifier after any comparison operator raises a bogus "Common mistake" ERROR

- Status: **FIXED (2026-09-13, continuation)** — see "Fix, applied" below.
- Binary at discovery: `/home/yoon/dev/cargo-fulltest/release/simple`, sha256 `4dfdf671742007d30210` (Rust seed, 2026-09-13 16:00)
- Verification binary: rebuilt in this worktree, `CARGO_TARGET_DIR=/home/yoon/cargo-unitp1`, `/home/yoon/cargo-unitp1/release/simple`, built 2026-09-13 23:12 from this branch's tip (guide explicitly permits an own-worktree rebuild to verify a `src/compiler_rust` change: "rebuild your own with `CARGO_TARGET_DIR=/home/yoon/cargo-unitp1`")
- Base: `origin/main` `f4cd1c306dd`
- Area: `src/compiler_rust/parser/src/error_recovery.rs:414-444`

## Impact, measured

This is the **single largest failure bucket found anywhere in the 2026-09-13
`test/01_unit` sweep**: 87 spec failures in `test/01_unit/os` alone carry

```
error: Common mistake detected: Use struct literal: Type { field: value }
```

and it is not the specs' own code that trips it. The diagnostic points at
product source they merely import, e.g.
`src/lib/nogc_async_mut/fs_driver/fat32_stub.spl:391:23`:

```
391 |         if old.raw == new.raw:
    |                       ^
```

`test/01_unit/os/formal/process_wait_refinement_spec.spl` reports
`outcome=ERROR declared>=3 executed=0` — the spec declares three examples and
executes none. Whatever else those specs are worth, none of it is being
measured.

## Repro, and the control that isolates the operator

```
struct B:
    raw: i64

fn f(old: B, new: B) -> bool:
    val t = old.raw <OP> new.raw
    true

fn main():
    print f(B(raw: 1), B(raw: 2))
```

| `<OP>` | diagnostic fires |
|---|---|
| `==` `!=` `<` `>` `<=` `>=` | yes |
| `+` `-` `=` | no |

Exactly the comparison operators. The program still runs and prints the right
answer when invoked directly, so the token stream is fine — this is a
false-positive hint, emitted at ERROR severity.

## Cause — an allow-list that does not match its own comment

`error_recovery.rs:414` opens with:

```rust
// Check for 'new' keyword (Java/C++) - but NOT when used as method/function name
// In Simple, 'new' is a valid identifier for:
//   ...
//   - Variable names in patterns (e.g., val (saved_path, new, diff) = ...)
//   - After operators (e.g., is_new or new)
// Only flag standalone 'new Type()' pattern as a mistake
if matches!(current.kind, TokenKind::New)
    && !matches!(previous.kind,
        TokenKind::Dot | TokenKind::Fn | TokenKind::DoubleColon | TokenKind::Comma
        | TokenKind::LParen | TokenKind::Val | TokenKind::Var | TokenKind::Or
        | TokenKind::And | TokenKind::Assign | TokenKind::Plus | TokenKind::Minus
        | TokenKind::Star | TokenKind::Slash)
{
    return Some(CommonMistake::JavaNew);
}
```

The list is of PRECEDING tokens and the comment says "After operators". The
arithmetic and logical operators are there; **none of the six comparison
operators is**. So the guard's stated intent and its implementation disagree,
and the gap is precisely the operators most likely to precede a value.

`CommonMistake::JavaNew` is classified `ErrorHintLevel::Error`
(`error_recovery.rs:292`), which is why a hint about a coding style becomes a
compile error and takes the importing spec's whole run with it.

## Fix, applied

Added `TokenKind::{Eq, NotEq, Lt, Gt, LtEq, GtEq}` to the `!matches!` allow-list
at `error_recovery.rs:424-441`.

**Rust-level regression tests** (`error_recovery.rs::tests`, run via
`cargo test --release -p simple-parser --lib error_recovery`, all 7 pass
including the 2 new ones):
- `test_new_after_comparison_operator_is_not_a_java_mistake` — all six
  comparison operators before `new` must yield `None`.
- `test_java_new_declaration_still_detected` — the positive case
  (`new` after `Newline`) must still yield `Some(CommonMistake::JavaNew)`, so
  the fix narrows rather than disables the rule.

**Spec-level RED -> GREEN**
`test/01_unit/compiler/frontend/parser_java_new_hint_after_comparison_operator_spec.spl`
(new file):
- RED on `/home/yoon/dev/cargo-fulltest/release/simple` (the sha `4dfdf671…`
  binary at the top of this file): `2 examples, 1 failure` — the six-operator
  negative case fails, the `return new Foo()` positive control (deliberately
  NOT `val f = new Foo()`, since `Assign` was already allow-listed and would
  not exercise the rule) passes, so the control discriminates.
- GREEN verified directly against the rebuilt seed (not yet run through the
  test runner, to avoid mixing binaries mid-sweep — see below): all six
  comparison-operator probes print no `Common mistake` text, the positive
  control still does, and `bin/simple compile
  src/lib/nogc_async_mut/fs_driver/fat32_stub.spl` — the real product file
  that triggered the 87-failure bucket — goes from erroring to compiling
  clean.

**Not yet done:** re-pointing this worktree's `bin/simple` symlink to the
rebuilt seed, which is deferred until the concurrent `test/01_unit/lib` sweep
(started under the old binary) finishes, so that sweep's row is not a mixed-
binary result. Once switched, rerun the spec through `bin/simple test` for a
runner-level GREEN and rerun the `os`/`compiler` spec files that previously hit
this bucket to get the 87→0 (or whatever the real number is) proof at the
directory level. The same file deserves one look for the sibling hints
(`JavaThis`, `JavaVoid`, `CTypeFirst`, ...) for the same defect shape — not done
here, out of scope for this specific bucket.

## Related

Same family, filed separately:
`doc/08_tracking/bug/allow_reserved_as_hard_keyword_2026-09-13.md` — `allow`
and `forbid` are hard keywords against the lexer's own comment. Both are cases
of an ordinary English word that the front end reserves without meaning to.
