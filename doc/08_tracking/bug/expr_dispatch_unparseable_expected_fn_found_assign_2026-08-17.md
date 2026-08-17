# `expr_dispatch.spl` "does not parse" — NOT a source defect. The deployed binary was stale.

- **Status:** RESOLVED / NOT-A-BUG in the source. **No `.spl` change is needed or
  wanted.** The remaining real defects are listed under "What IS still open".
- **Found:** 2026-08-17. **Corrected the same day** — the first version of this
  row said "OPEN, UNLOCALIZED" and listed four leads. All four were wrong. This
  rewrite replaces them.
- **Not fenced:** not one of the `CLAIMED-OFFHOST 2026-08-17` set.

## Symptom

```
error: compile failed: parse: in
  "src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl":
  Unexpected token: expected Fn, found Assign
```

## Root cause: an 8.5-hour-stale compiler, not the source

`literal` is a lexer keyword (`TokenKind::Literal`, for
`literal fn _suffix ...`). The OLD parser routed it unconditionally to
`parse_literal_function()`, which does `expect(Fn)` — so a bare re-assignment
`literal = ...` failed. `expr_dispatch.spl` uses `literal` as a local in
`me bare_scalar_const_pattern`: the declaration on line 136 (`var literal = ...`)
was fine, only the bare reassignments on 140/142/144 tripped it.

**That parser bug was already fixed before this row was first written.**
`src/compiler_rust/parser/src/parser_impl/core.rs` disambiguates it:

```rust
TokenKind::Literal => {
    if self.peek_next().kind == TokenKind::Fn { self.parse_literal_function() }
    else { self.parse_expression_or_assignment() }
}
```

- fix landed: **`d7213eb6174`, 2026-08-17 07:36:55Z**
- deployed `bin/release/x86_64-unknown-linux-gnu/simple`: built **2026-08-16 22:59:37Z**

The deployed binary predates the fix by 8.5 hours. Every "parse failure" observed
through it was an artifact of that staleness.

**Proof.** Built the current seed into an isolated `CARGO_TARGET_DIR` (never
overwriting the shared binary — that clobbers concurrent lanes) and ran the
**unmodified** `origin/main` blob through it:

```bash
cd src/compiler_rust
CARGO_TARGET_DIR=/mnt/data/tmp/claude-1000/seedbuild-vscfix cargo build --release --bin simple
git show origin/main:src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl > /tmp/a.spl
/mnt/data/tmp/claude-1000/seedbuild-vscfix/release/simple run /tmp/a.spl 2>&1 \
  | grep -c "expected Fn, found Assign"
# -> 0
```

A rename `literal` -> `lit_expr` was written, tested, committed locally, and then
**deliberately dropped** once this was understood. Do not re-apply it: it would
be churn on a file that is already correct.

## Contrast — the or-pattern gap in the SAME guard IS real

The same guard (`check-native-trailing-default-param.shs`) was RED for a second,
genuinely source-level reason: wrapped or-patterns (trailing `|` then an indented
continuation) in `src/compiler/50.mir/verification_semantic_coverage.spl`. That
one **still fails on a freshly built seed** (same isolated binary, 2 errors on
the pre-fix blob), so it is not a staleness artifact. Fixed in `eb4d4d9cd25` by
unwrapping both patterns. Note `parser_patterns.rs` *does* have
`peek_through_newlines_and_indents_is(&TokenKind::Pipe)` (lines 82/96) — it
exists but does not cover this shape, so reading that code is not sufficient
evidence either way. **Test with a current binary; do not infer from source.**

Also note `d9dfcbf80e0` landed that file, and `d86d01a39f9` — titled "make
verification_semantic_coverage.spl parse" — contained **no source change at all**
(1 file / 68 insertions, a bug doc). Verify fixes by content, never by subject.

## Dead ends — all four original "leads" were wrong

1. **Misattribution through the re-export cycle: NO.** The attribution is
   correct. All four `_MirLoweringExpr/` files plus `mir_lowering_expr.spl`
   report the same file because it is re-exported and therefore transitively
   parsed by each. Looks like misattribution; isn't.
2. **Missing `__init__.spl` in `_MirLoweringExpr/`: irrelevant** to a parse error.
3. **Bad wipe-restore: NO.** `ae55a7467197` restored blob `ddb1529…`,
   byte-identical to the pre-wipe blob at `e99a5b76d11`/`52f3b8c118f`. No
   corruption. No parsing ancestor exists either — the construct has been present
   since at least `cfe0506e336` (2026-08-05) and was "broken" under every
   pre-`d7213eb6174` binary.
4. **Delete-one-method bisect: unnecessary.** (It does work, and it is the sound
   method if ever needed — prefix-truncation bisect is **unsound** here, the
   predicate is non-monotonic, and it falsely fingers line 49.)

Other things checked and cleared: `me` is the normal method keyword (2918 uses),
not corrupted `fn`; module-level `var x: text = ""` parses fine; no tabs, no
decorators, no stray assignment at impl-body indent, no working-copy divergence
from `origin/main`.

## What IS still open

1. **The diagnostic carries no line or column.** `expected Fn, found Assign`
   against a 4483-line file, with no span, is what made this cost two agent-hours
   and two needless commits. Every `expect()` failure on this path should carry a
   span.
2. **Nothing warns that the deployed toolchain is older than the source.**
   `bin/simple` is a gitignored symlink with no vintage check anywhere in the
   guards. A guard (or a line in the guard preamble) comparing the binary's build
   time against `HEAD`'s commit time would have turned this whole investigation
   into one line of output. CLAUDE.md already tells you to `readlink -f
   bin/simple && stat` alongside any timing measurement — the same discipline
   belongs on any RED verdict.
3. `_MirLoweringExpr/` still has no `__init__.spl` while sibling package dirs
   under `50.mir/` do. Unrelated to this, but noted.

## Method note for whoever hits the next RED

**Check binary-vs-source vintage BEFORE localizing any parse error.**

```bash
readlink -f bin/simple && stat -c '%y' "$(readlink -f bin/simple)"
git log -1 --format='%ad' --date=iso HEAD
```

If the binary is older than the source, a RED tells you nothing about the source
until you rebuild into an isolated `CARGO_TARGET_DIR` and re-test.
Also: a silent exit is not a verdict, and a wrapper's exit 0 is not the guard's
exit 0 — read the verdict line, which is always last on stdout.
