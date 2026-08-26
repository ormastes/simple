# Seed redeployed 2026-08-25 05:16 UTC cannot parse `tooling/easy_fix/accessor_rewrite.spl` — `bin/simple test` and md doctests abort

**Status:** OPEN (observed; owner = the session that redeployed). **Binary:** `bin/release/x86_64-unknown-linux-gnu/simple`, 60,641,352 bytes, mtime 2026-08-25 05:16:29.

## Symptom
Every `bin/simple test <spec|md>` — including the trivial fixture `test/fixtures/doctest/green.md`
which passed at 04:5x on the previous seed — now aborts before executing anything:
```
error: compile failed: parse: in ".../src/lib/nogc_sync_mut/tooling/easy_fix/accessor_rewrite.spl": Unexpected token: expected Colon, found If
```
`accessor_rewrite.spl` is unmodified in the working tree (clean vs HEAD, mtime 2026-08-24 22:10);
the previous seed (`/mnt/data/worktrees/goal-main-1/bin/release/x86_64-unknown-linux-gnu/simple`,
60,650,360 bytes, 2026-08-23 04:47) parses it and runs the same doctests green. So the regression is
in the redeployed seed's parser (or a grammar change that landed in `src/compiler_rust` without the
stdlib file being updated), not in the stdlib.

## Impact
No spec or md doctest can be executed through the deployed `bin/simple` on this box until fixed;
`run` of ordinary programs still works. Workaround used by the GPU hardening session: run
`test`/doctests through the 08-23 seed above.

## Reproduce
`bin/simple test test/fixtures/doctest/green.md` → exit 1 with the parse error;
`/mnt/data/worktrees/goal-main-1/bin/release/x86_64-unknown-linux-gnu/simple test test/fixtures/doctest/green.md` → `SDoctest Results: 1 total, 1 passed`.

## Bisect (2026-08-25)

### Minimal reproduction (6 lines)
`/mnt/data/tmp/claude-1000/parsefix/repro.spl`:
```
fn main():
    var unsafe: List<text> = []
    unsafe.push("a")
    for existing in unsafe:
        print(existing)
    if unsafe.len() > 0:
        print("done")
```
- OLD seed (`/mnt/data/worktrees/goal-main-1/bin/release/x86_64-unknown-linux-gnu/simple`,
  60,650,360 B, 2026-08-23 04:47): prints `a` / `done`.
- NEW seed (`bin/release/x86_64-unknown-linux-gnu/simple`, 60,641,352 B,
  sha256 `706fa636…`): `error: compile failed: parse: … Unexpected token: expected Colon, found If`.

Name-discriminating control: identical fixtures with the variable renamed to
`xs` / `items` / `foo` / `todo` / `pass_dn` all parse on BOTH binaries; only
`unsafe` and `danger` fail. The same failure appears for `while unsafe:` and
`if unsafe:` — any block header whose last token is such a variable.
In the real file this is
`src/lib/nogc_sync_mut/tooling/easy_fix/accessor_rewrite.spl:134`,
`for existing in unsafe:` (`unsafe` is a local `List<text>` declared at :129).

### Cause: NOT a landed commit — the seed was built from an unlanded tree
`/mnt/data/cargo-target-caret-seed/release/simple.d` (the target dir that
produced the deployed binary) names its source root as
`/mnt/data/tmp/claude-1000/caret-clean`, not any git worktree. That tree carries
an uncommitted parser change absent from `origin/main`:

`/mnt/data/tmp/claude-1000/caret-clean/src/compiler_rust/parser/src/expressions/primary/mod.rs:164-169`
```rust
TokenKind::Identifier { ref name, .. }
    if (name == "unsafe" || name == "danger")
        && (self.peek_is(&TokenKind::Colon)
            || self.unsafe_block_header_is_valid()) =>
{
    self.parse_unsafe_block_primary()
}
```
The `self.peek_is(&TokenKind::Colon)` disjunct makes ANY expression-position
identifier `unsafe`/`danger` followed by `:` an unsafe-block primary. In
`for e in unsafe:` the iterable expression therefore consumes the header's own
colon, the NEWLINE/INDENT and the whole body; the for-header's later
`expect(&TokenKind::Colon)` then reports the next statement's token — `If`.
`git log --oneline origin/main --since=2026-08-22 -- src/compiler_rust/parser`
lists 5 commits, none of which contains this hunk; `git log -S 'name == "danger"'`
shows the only landed name-discriminating site is the STATEMENT-level handler
`parser_impl/core.rs:931`, which is correct and predates both seeds (25ceca69380,
2026-08-21).

### Why the redeploy happened (do not simply roll back)
The value-bound form is real and the OLD seed cannot parse it:
`val home = unsafe(capabilities: [ffi]):` → OLD seed: `error[E1002]: function
'unsafe' not found`; NEW seed: runs. It is used by
`test/fixtures/engine_differential/value_bound_unsafe_block.spl:15,18` and
`test/01_unit/compiler/lint/raw_sffi_call_spec.spl:31`. Statement-position
`unsafe(capabilities: [ffi]):` works on both. So the two seeds each break
something the other handles.

### Fix
Port the caret-clean arm to `origin/main` **without** the bare-colon disjunct:
`src/compiler_rust/parser/src/expressions/primary/mod.rs` now gates the
expression-position unsafe block on `unsafe_block_header_is_valid()` alone
(strictly `(` + `reason:`/`capabilities:` args + `):`), and
`parse_unsafe_block_primary` no longer has a bare-`unsafe:` branch. A bare
`unsafe:` block stays what it always was: a STATEMENT, handled at
`parser_impl/core.rs:931`. Both behaviours are kept — there is no conflict, the
deployed seed's guard was simply too wide.

A second edit was required and was found by the new Rust test, not by hand: the
STATEMENT-position capability branch in `parser_impl/core.rs` parsed its header
with `parse_expression()`, which now re-enters the expression-position rule and
consumes the block's own colon — `unsafe(capabilities: [ffi]):` at statement
start regressed to `expected Colon, found Identifier`. That branch now delegates
to `parse_unsafe_block_primary()` when `unsafe_block_header_is_valid()` holds, so
the header is consumed exactly once. The old `parse_expression()` fallback is
kept for call-shaped headers the validator rejects.

### Verification (2026-08-25 06:0x)
Built from `/mnt/data/worktrees/parsefix-iso` = `origin/main` HEAD `ac08f56f762`
plus the two hunks above (the shared `simple-main` tree was NOT used as the build
source: another session currently has unrelated parser reverts staged there).

- Binary: `/mnt/data/cargo-target-parsefix2/release/simple`, 60,646,096 bytes,
  sha256 `3ef64bffc68d0b1c2dd851d1f02976ca98fba6f88fbb406dddf56ba7f3ca27c0`
  (deployed-seed sha was `706fa636…`).
- `cargo test --release -p simple-parser --test unsafe_block_vs_identifier`:
  `test result: ok. 8 passed; 0 failed`. Before the core.rs edit the same run was
  `7 passed; 1 failed` on `statement_position_capability_unsafe_block_still_parses`.
- `cargo build --release --bin simple`: rc=0.
- Parses cleanly with the rebuilt binary: `accessor_rewrite.spl` (verbatim copy),
  the minimal repro, the value-bound `unsafe(capabilities: [ffi]):` probe, and the
  statement-position capability probe — zero `Unexpected token` on all four.
- `simple test test/fixtures/doctest/green.md` →
  `SDoctest Results: 1 total, 1 passed, 0 failed, 0 skipped, 0 errors` (rc 0).
- `simple test test/01_unit/compiler/parser/unsafe_identifier_block_header_spec.spl`
  → `Results: 4 total, 4 passed, 0 failed`.
- `simple test test/01_unit/app/llm_caret/infra_tools_spec.spl` →
  `Results: 17 total, 17 passed, 0 failed`.
- `sh scripts/check/check-seed-builds-push.shs --selftest` →
  `PASS — 6 fixture(s) checked` (rc 0).

### Recommendation
DEPLOY the rebuilt binary above; do NOT roll back to the 2026-08-23 seed. Rolling
back re-breaks `val x = unsafe(capabilities: [ffi]):`, which the 08-23 seed
rejects with `error[E1002]: function 'unsafe' not found` and which
`test/fixtures/engine_differential/value_bound_unsafe_block.spl` and
`test/01_unit/compiler/lint/raw_sffi_call_spec.spl` depend on. The rebuilt binary
is the only one of the three that handles every form. The `caret-clean` lane
should rebase onto these hunks rather than re-deploying its own build.

### Specs
- `src/compiler_rust/parser/tests/unsafe_block_vs_identifier.rs` — 8 pins:
  `for/while/if` headers ending in `unsafe`, the same for `danger`,
  statement-position bare and capability blocks, and the value-bound capability
  block with and without `reason:`.
- `test/01_unit/compiler/parser/unsafe_identifier_block_header_spec.spl` —
  Simple-level behavioural regression exercising the same headers.
