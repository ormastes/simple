# Bug: `use .relative.path.{Name}` fails to parse — the seed cannot parse its own compiler source

- **ID:** relative_use_with_brace_member_list_fails_to_parse_2026-08-17
- **Severity:** P1 — **bootstrap-blocking**, not a cosmetic lint gap. The Rust
  seed built from the current `origin/main` cannot parse
  `src/compiler/70.backend/backend/vhdl_backend.spl`, a file in its own
  compiler source tree, so any `native-build` whose source closure reaches
  that file aborts.
- **Status:** OPEN — filed, not fixed. **No parser fix attempted in this lane.**
- **Discovered:** 2026-08-17, while re-baselining
  `scripts/check/check-native-trailing-default-param.shs` against a
  freshly-built seed.
- **Not fenced:** not one of the `CLAIMED-OFFHOST 2026-08-17` set.

## Symptom

```
error: compile failed: parse: in
  "src/compiler/70.backend/backend/vhdl_backend.spl":
  Unexpected token: expected identifier, found LBrace
```

Note there is **no line/column** in the diagnostic — that is part of what made
this expensive to localise, and is worth fixing alongside the parse rule.

## Minimal reproducer (4 lines, isolated from the compiler tree)

```
/tmp/tdp/rel/sub/mod.spl:
    fn helper() -> i64:
        7

/tmp/tdp/rel/main.spl:
    use .sub.mod.{helper}

    fn main() -> i64:
        helper()
```

```
$ /mnt/data/cgtw2/release/simple run main.spl
rc=1
error: compile failed: parse: in "/tmp/tdp/rel/main.spl":
  Unexpected token: expected identifier, found LBrace
```

### Controls that isolate the trigger to exactly one construct

| # | `use` line | parses? | rc | LBrace errors |
|---|------------|---------|----|---------------|
| repro | `use .sub.mod.{helper}` (relative **and** braces) | **NO** | 1 | 1 |
| A | `use .sub.mod` (relative, no braces) | yes | 1 (later semantic error, not parse) | 0 |
| B | `use sub.mod.{helper}` (absolute, braces) | **yes — and runs** | **7** | 0 |

Control B returning `rc=7` is the strongest half of this: with the leading dot
removed the identical member-list import parses, resolves, executes, and
returns `helper()`'s value. Only the **combination** of a leading-dot relative
path with a `.{...}` member list fails. Neither half fails alone.

Mechanically this reads as: the relative-path branch of the `use` parser
consumes `.` `sub` `.` `mod` `.` and then unconditionally expects an
identifier, whereas the absolute-path branch handles `.{` as the start of a
member list. Not verified in the parser source — no fix attempted — but it
matches the error text exactly.

## Independent corroboration: two separately built seeds

Both fail at the same file with the same message. They were built by different
lanes, from different worktrees, hours apart:

| seed | size | mtime |
|------|------|-------|
| `/mnt/data/cgtw2/release/simple` (built in this lane from a clean `origin/main` tree, `cargo build --release --bin simple` → `rc=0`) | 59,582,624 | 2026-08-17T11:10:48Z |
| `/mnt/data/cargo-w0001/release/simple` (another lane's build) | 59,488,384 | 2026-08-17T08:28:58Z |

`grep -c "expected identifier, found LBrace"` = 1 in each run's log. So this is
a property of the current seed, not of one lane's tree or one build.

## Blast radius

16 files under `src/compiler/` use the `use .relative.path.{Name}` form, e.g.:

```
src/compiler/70.backend/backend/vhdl_backend.spl        (lines 14, 17, 29)
src/compiler/70.backend/backend/vhdl_expr.spl
src/compiler/70.backend/backend/vhdl_validation.spl
src/compiler/70.backend/backend/vhdl/vhdl_rv32i_decode.spl
src/compiler/70.backend/backend/vhdl/vhdl_register_file.spl
src/compiler/70.backend/backend/vhdl/vhdl_memory_templates.spl
src/compiler/70.backend/backend/vhdl/vhdl_design_catalog.spl
```

`vhdl_backend.spl:14` is the concrete instance that aborts the build:

```simple
use .vhdl.vhdl_builder.{VhdlBuilder}
```

## Why this is a compiler bug, not a source bug

`use .path.{A, B}` is accepted language syntax used throughout the tree, and
the absolute spelling of the identical import parses and runs (control B).
Rewriting the 16 call sites to the absolute form would be silently normalising
around a parser defect, which the project rules forbid — so this is filed
instead.

## Do NOT confuse with the angle-bracket false positive

The same build also emits four `Use angle brackets: X<...> instead of X[...]`
diagnostics. Those are **warnings** and are NOT what fails the build; they are a
separate, older defect — see
`parser_array_index_misread_as_generics_2026-06-14.md` (whose 2026-08-17
closure they contradict; a note has been added there) and
`angle_bracket_index_lint_parse_mismatch_2026-06-06.md`. Reading the first
diagnostic in the log as the cause is exactly the mistake this section exists
to prevent: the fatal error is the `LBrace` one, several screens further down.

## Reproduce

```bash
# with any seed built from origin/main at or after 2026-08-17T08:28Z
/mnt/data/cgtw2/release/simple run src/compiler/70.backend/backend/vhdl_backend.spl
# rc=1, "Unexpected token: expected identifier, found LBrace"
```

## Proposed fix (not attempted here)

1. Make the relative/leading-dot `use` path parser share the absolute branch's
   `.{ member, ... }` handling, so `use .a.b.{C}` parses like `use a.b.{C}`.
2. Attach a span to this diagnostic — the current message names only the file,
   with no line or column.
3. Add a parse-level spec covering all four cells of the control table above,
   so the relative+braces combination cannot regress silently again.
