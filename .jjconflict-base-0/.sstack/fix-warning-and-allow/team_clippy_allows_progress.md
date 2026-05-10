# Team Clippy Allows — Progress Report

**Date:** 2026-04-28
**Task:** Reduce `bin/simple build lint` warnings via workspace-level Cargo.toml lint allowlist

## Summary

**Before:** 1619 warnings
**After:** 17 warnings (behind pre-existing compile error in `simple-compiler`)
**Reduction:** 1602 warnings eliminated (99%)

## Root Cause Discovery

The `bin/simple build lint` runner passes `-W clippy::all` as a rustc flag via `-- -W clippy::all`.
This overrides workspace-level `[workspace.lints.clippy]` allows because command-line lint flags
and manifest lint flags share the same priority (0) and command-line wins on tie.

**Fix:** Use `{ level = "allow", priority = 1 }` syntax to give workspace allows higher priority
than the `-W clippy::all` flag. This is supported since Cargo 1.74.

**Verified empirically:** Changed `result_large_err` from `"allow"` to `{ level = "allow", priority = 1 }`.
Warnings dropped 1619 → 94 (1525 eliminated in one change).

## Lints Updated to priority = 1

All were already in `[workspace.lints.clippy]` but ineffective against `-W clippy::all`:

| Lint | Warnings Suppressed | Reason |
|------|---------------------|--------|
| `result_large_err` | 1512 | Large Err types are common/intentional in compiler error types |
| `unnecessary_map_or` | 4 | Style preference, readability in some contexts |
| `collapsible_if` | 3 | Style preference, nested ifs can be clearer |
| `doc_overindented_list_items` | 7 | Cosmetic doc formatting |
| `while_let_on_iterator` | 2 | Style preference |
| `too_many_arguments` | 2 | Common in AST/IR builders |
| `needless_borrow` | 2 | Style preference |
| `manual_strip` | 2 | Style preference |
| `manual_repeat_n` | 2 | Style preference |
| `manual_is_multiple_of` | 2 | Style preference |
| `useless_format` | 1 | Readability in error/test formatting |
| `unnecessary_cast` | 1 | Style preference |
| `type_complexity` | 1 | Complex types common in FFI-heavy compiler code |
| `question_mark` | 1 | Style preference |
| `needless_range_loop` | 1 | Style preference |
| `needless_borrows_for_generic_args` | 1 | Style preference |
| `manual_range_contains` | 1 | Style preference |
| `manual_pattern_char_comparison` | 1 | Style preference |
| `manual_find` | 1 | Style preference |
| `io_other_error` | 1 | io::Error::other() is clearer in some contexts |
| `if_same_then_else` | 1 | Style preference |
| `field_reassign_with_default` | 1 | Style preference |
| `collapsible_else_if` | 1 | Style preference |

## Remaining 17 Warnings

These come from `simple-compiler` crate which has a **pre-existing compile error** (E0308
mismatched types in `compiler/src/interpreter_method/collections.rs:362`). Clippy emits
warnings for code it processes before encountering the error. Once the compile error is fixed
by another team, these warnings should also be suppressed (all their lint names are in our
priority=1 allow list: `unnecessary_map_or`, `unnecessary_cast`, `needless_range_loop`,
`manual_repeat_n`, `manual_pattern_char_comparison`, `manual_is_multiple_of`, `collapsible_if`).

## Lints NOT Allowed (per task constraints)

| Lint | Count | Reason Not Allowed |
|------|-------|-------------------|
| `large_enum_variant` | already in list | Memory layout impact — excluded by task |
| `dead_code` | already in [workspace.lints.rust] | Audit per-case — excluded by task |

## Files Modified

- `src/compiler_rust/Cargo.toml` — added `priority = 1` to 23 existing clippy allow entries
