# Bug: `a < b[i]` — bracket index after `<` still misread as generics (reopens a same-day closure)

- **ID:** parser_bracket_index_after_less_than_still_misread_as_generics_2026-08-17
- **Severity:** P1 — bootstrap-blocking. The seed cannot parse the compiler's own source.
- **Discovered:** 2026-08-17, while re-baselining an unrelated MIR finding against a fresh seed.
- **Status:** FIXED 2026-08-17 — see "Verdict" at the bottom. Severity corrected from
  P1 to P3: the parse was never wrong, only a diagnostic leaked.
- **Status:** OPEN
- **Reopens:** `parser_array_index_misread_as_generics_2026-06-14.md`, which was marked
  `CLOSED 2026-08-17 — the parser false positive no longer fires`. It still fires.

## Summary

The parser reads `name[...]` as a `[...]`-style generic type application — the exact
defect the 2026-06-14 row describes — when the index expression appears on the
right-hand side of a `<` comparison:

```
--> src/compiler/70.backend/backend/native/regalloc.spl:158:58
158 |   if target_start < block_start_pos[block.block_id]:
    |                                    ^
Use angle brackets: block_start_pos<...> instead of block_start_pos[...]
```

## Why the trigger is `<`, not the indexing

The strongest evidence is inside the failing file itself. Three consecutive lines
index the *same* variable; only the one preceded by `<` fails:

```
156 |  val target_start = block_start_pos[target_id]        # parses fine
157 |  val src_end      = block_end_pos[block.block_id]     # parses fine
158 |  if target_start < block_start_pos[block.block_id]:   # FAILS
```

So the construct `name[expr]` is not itself the problem. On seeing `<`, the parser
commits to a generic-argument parse and then rejects the `[` that follows.

This also matches the closed row's own reproducer, which nobody appears to have
noticed was the same shape:

```
559 |  while j >= 0 and current.selector.specificity < matched[j].selector.specificity:
```

Again an index on the RHS of `<`. The two reproducers are the same defect, which is
why closing one did not fix the other.

## Independent corroboration (not one bad build)

Reproduced at the identical file, line and column by two separately built seeds:

| seed | built | source tree |
|---|---|---|
| `/mnt/data/cgtw2/release/simple` (59,582,624 bytes) | 2026-08-17 11:10Z | clean `wt-vsc-fix`, byte-identical to `origin/main` |
| `/mnt/data/cargo-w0001/release/simple` | 2026-08-17 08:28Z | another lane, independently |

Both built with `cargo build --release --bin simple`, rc read directly (not through a
pipe). A third cross-check (`cargo-target-c2`) ended `exit 143` and is recorded here as
**UNVERIFIED, not corroboration** — earlyoom is actively SIGTERMing `simple` on this host.

## Impact

`regalloc.spl` is compiler source. A seed that cannot parse the compiler's own source
cannot bootstrap it, so this is not a cosmetic lint gap. It is currently masked because
the affected guard fails for this reason *after* the code path most lanes exercise.

## Why the 2026-06-14 closure was premature

That row was closed on source inspection of its single original reproducer
(`src/lib/common/ui/style.spl`). The closure verified that one site, not the defect
class. The `<`-precedes-index shape was never enumerated, so a second live instance in
`src/compiler/**` survived the closure untouched. Two specs are needed here, per the
standing rule: one reproducing `regalloc.spl:158`, and one defect-CLASS spec that walks
`a < b[i]`, `a <= b[i]`, and the `and`-chained form from the style.spl case.

## Verdict (2026-08-17) — FIXED, and the severity in the header above was wrong

### The parse was always correct; only the diagnostic leaked

The report's framing ("the seed cannot parse the compiler's own source",
"bootstrap-blocking") is **not what was measured**. On the unpatched seed
`/mnt/data/cgtw2/release/simple`:

```
$ simple compile src/compiler/70.backend/backend/native/regalloc.spl
rc=0     # compiled successfully, emitting regalloc.smf
angle-bracket warnings: 1   (at regalloc.spl:158:58 — the exact reported site)
```

and a minimal reproducer `if a < arr[i]:` **ran and produced the correct answer**
(`ge`, i.e. `5 < 1` correctly false) with `rc=0`. The message is a `warning`, not
an error. So the real defect is a **spurious diagnostic**, not a parse failure —
severity P3, not P1. Nothing here blocked bootstrap. (The original filing's
"cannot parse" reading appears to come from the `[INFO] JIT compilation failed …
function \`fun\` not found` line that accompanied it; that is an **unrelated**
artifact of writing `fun` instead of `fn`, and reproduces identically on a
control file with no `<` at all.)

### Root cause

`src/compiler_rust/parser/src/expressions/postfix.rs`, two speculative
generic-argument parsers: `try_skip_ident_generic_args` (the one that fires here)
and `try_parse_method_generic_args`.

On `a < arr[i]` the postfix layer cannot know whether `<` opens a generic
argument list (`Foo<T>(…)`) or is a less-than operator, so it **speculates**: it
saves `current` / `previous` / `pending_tokens` / `lexer`, tries to read a type
list, and restores all four if the shape does not pan out. That backtracking is
correct, which is why the comparison parses and evaluates fine.

The leak is that the speculation calls `parse_type`, and `parse_type`
(`parser_types.rs:414-429`) treats a following `[` as a `[...]`-style generic
argument list and **pushes an `ErrorHint` into `self.error_hints` as a side
effect**. `error_hints` is not part of the saved state, so the warning produced
by an abandoned parse survives the backtrack and is reported against the user's
source. The trigger is the `<` because only a `<` starts the speculation — which
is exactly the observation in the "Why the trigger is `<`" section above, and why
the 2026-06-14 row and this one are the same defect.

### Fix

Four lines: record `self.error_hints.len()` as a watermark alongside the existing
saved state, and `truncate` back to it on each of the two backtrack paths. The
expression parser is otherwise untouched.

### Ablation (proves causation)

Built from a clean `origin/main` extract with an isolated `CARGO_TARGET_DIR`
(`/mnt/data/cargo-brk`), `cargo build --release --bin simple` rc=0, rc read
directly rather than through a pipe.

| build | `regalloc.spl` angle-bracket warnings | parser gate |
|---|---|---|
| unpatched (`origin/main`) | **1**, at `regalloc.spl:158:58` | 2 of 4 FAILED |
| patched | **0**, `rc=0`, compiles to `.smf` | 4 of 4 ok |
| patch reverted again (`sed` removed only the 2 `truncate` calls) | — | 2 of 4 FAILED again |
| patch re-applied | — | 4 of 4 ok |

Full parser suite, same tree, both ways: **282 passed / 6 failed unpatched →
284 passed / 4 failed patched**. The 4 residual failures are pre-existing
f-string/lexer tests (`test_interpolated_strings`, `test_triple_fstring_literals`,
`double_braces_collapse_to_one_literal_brace`,
`test_double_brace_escape_still_works`), present identically with and without the
patch, and unrelated to this change.

### Specs

- `src/compiler_rust/parser/src/lt_index_hint_leak_tests.rs` — the
  **ablation-sensitive** gate, because a leaked warning is not observable from a
  running program; it asserts on `error_hints()` directly. Covers the reproducer,
  the class (`<`, `<=`, the `and`-chained `x >= 0 and y < arr[j].field`, nested
  `a < b[c[d]]`, `b[i].len()`), a control, and an **over-correction guard** so the
  fix cannot be "passed" by deleting the warning outright (a real `List[i64]`
  annotation must still warn).
- `test/01_unit/compiler/parser/lt_then_bracket_index_repro_spec.spl` —
  `Results: 2 total, 2 passed, 0 failed`.
- `test/01_unit/compiler/parser/comparison_then_bracket_index_class_spec.spl` —
  `Results: 5 total, 5 passed, 0 failed`.

  Note honestly: these two `.spl` specs pin the **semantics** of the shape, which
  were already correct before the fix, so they are green on both sides of the
  ablation. They guard against a future regression that breaks the backtrack
  itself; they do not by themselves demonstrate this fix.

### Ownership check

The other lane's uncommitted `src/compiler_rust/parser/` edits mentioned above
have since landed as `579a0e1a171` (relative-import soft-keyword regression) and
`c3506bfbc4b` (multi-line or-pattern). Neither touches the speculative
generic-argument backtrack, and `src/compiler_rust/parser/` was clean at the time
of this work. No competing fix.

### Not covered

`peek_brace_is_lambda_block` (`parser_helpers.rs:315`) is a third speculative
backtrack that also restores only token state, but it never calls `parse_type`
and pushes no hints, so it is not a member of this defect class today. It would
become one if it ever grew a type-parsing path.
## Not yet done

### The parse was always correct; only the diagnostic leaked

The report's framing ("the seed cannot parse the compiler's own source",
"bootstrap-blocking") is **not what was measured**. On the unpatched seed
`/mnt/data/cgtw2/release/simple`:

```
$ simple compile src/compiler/70.backend/backend/native/regalloc.spl
rc=0     # compiled successfully, emitting regalloc.smf
angle-bracket warnings: 1   (at regalloc.spl:158:58 — the exact reported site)
```

and a minimal reproducer `if a < arr[i]:` **ran and produced the correct answer**
(`ge`, i.e. `5 < 1` correctly false) with `rc=0`. The message is a `warning`, not
an error. So the real defect is a **spurious diagnostic**, not a parse failure —
severity P3, not P1. Nothing here blocked bootstrap. (The original filing's
"cannot parse" reading appears to come from the `[INFO] JIT compilation failed …
function \`fun\` not found` line that accompanied it; that is an **unrelated**
artifact of writing `fun` instead of `fn`, and reproduces identically on a
control file with no `<` at all.)

### Root cause

`src/compiler_rust/parser/src/expressions/postfix.rs`, two speculative
generic-argument parsers: `try_skip_ident_generic_args` (the one that fires here)
and `try_parse_method_generic_args`.

On `a < arr[i]` the postfix layer cannot know whether `<` opens a generic
argument list (`Foo<T>(…)`) or is a less-than operator, so it **speculates**: it
saves `current` / `previous` / `pending_tokens` / `lexer`, tries to read a type
list, and restores all four if the shape does not pan out. That backtracking is
correct, which is why the comparison parses and evaluates fine.

The leak is that the speculation calls `parse_type`, and `parse_type`
(`parser_types.rs:414-429`) treats a following `[` as a `[...]`-style generic
argument list and **pushes an `ErrorHint` into `self.error_hints` as a side
effect**. `error_hints` is not part of the saved state, so the warning produced
by an abandoned parse survives the backtrack and is reported against the user's
source. The trigger is the `<` because only a `<` starts the speculation — which
is exactly the observation in the "Why the trigger is `<`" section above, and why
the 2026-06-14 row and this one are the same defect.

### Fix

Four lines: record `self.error_hints.len()` as a watermark alongside the existing
saved state, and `truncate` back to it on each of the two backtrack paths. The
expression parser is otherwise untouched.

### Ablation (proves causation)

Built from a clean `origin/main` extract with an isolated `CARGO_TARGET_DIR`
(`/mnt/data/cargo-brk`), `cargo build --release --bin simple` rc=0, rc read
directly rather than through a pipe.

| build | `regalloc.spl` angle-bracket warnings | parser gate |
|---|---|---|
| unpatched (`origin/main`) | **1**, at `regalloc.spl:158:58` | 2 of 4 FAILED |
| patched | **0**, `rc=0`, compiles to `.smf` | 4 of 4 ok |
| patch reverted again (`sed` removed only the 2 `truncate` calls) | — | 2 of 4 FAILED again |
| patch re-applied | — | 4 of 4 ok |

Full parser suite, same tree, both ways: **282 passed / 6 failed unpatched →
284 passed / 4 failed patched**. The 4 residual failures are pre-existing
f-string/lexer tests (`test_interpolated_strings`, `test_triple_fstring_literals`,
`double_braces_collapse_to_one_literal_brace`,
`test_double_brace_escape_still_works`), present identically with and without the
patch, and unrelated to this change.

### Specs

- `src/compiler_rust/parser/src/lt_index_hint_leak_tests.rs` — the
  **ablation-sensitive** gate, because a leaked warning is not observable from a
  running program; it asserts on `error_hints()` directly. Covers the reproducer,
  the class (`<`, `<=`, the `and`-chained `x >= 0 and y < arr[j].field`, nested
  `a < b[c[d]]`, `b[i].len()`), a control, and an **over-correction guard** so the
  fix cannot be "passed" by deleting the warning outright (a real `List[i64]`
  annotation must still warn).
- `test/01_unit/compiler/parser/lt_then_bracket_index_repro_spec.spl` —
  `Results: 2 total, 2 passed, 0 failed`.
- `test/01_unit/compiler/parser/comparison_then_bracket_index_class_spec.spl` —
  `Results: 5 total, 5 passed, 0 failed`.

  Note honestly: these two `.spl` specs pin the **semantics** of the shape, which
  were already correct before the fix, so they are green on both sides of the
  ablation. They guard against a future regression that breaks the backtrack
  itself; they do not by themselves demonstrate this fix.

### Ownership check

The other lane's uncommitted `src/compiler_rust/parser/` edits mentioned above
have since landed as `579a0e1a171` (relative-import soft-keyword regression) and
`c3506bfbc4b` (multi-line or-pattern). Neither touches the speculative
generic-argument backtrack, and `src/compiler_rust/parser/` was clean at the time
of this work. No competing fix.

### Not covered

`peek_brace_is_lambda_block` (`parser_helpers.rs:315`) is a third speculative
backtrack that also restores only token state, but it never calls `parse_type`
and pushes no hints, so it is not a member of this defect class today. It would
become one if it ever grew a type-parsing path.
