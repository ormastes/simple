---
id: backend_linker_check_arm_body_const_assign_2026-07-02
status: RESOLVED
severity: low
discovered: 2026-07-02
discovered_by: `bin/simple check src/compiler/70.backend/linker/symbol_analysis.spl` while re-applying explicit dict-value type annotations
related: src/compiler/70.backend/linker/symbol_analysis.spl
related: src/compiler/10.frontend/core/parser_stmts.spl
---

# `bin/simple check` on backend/linker files hits unrelated "cannot assign to const 'arm_body'"

## Summary

`timeout 180 bin/simple check src/compiler/70.backend/linker/symbol_analysis.spl`
fails with `error: semantic: cannot assign to const 'arm_body'` and no
file/line location (plain text, `--json` and default modes both omit it).

This is unrelated to `symbol_analysis.spl` itself:

- The same error reproduces against the pre-fix (git HEAD) version of the
  file, so it is not caused by the `val sym: AnalyzedSymbol = ...` type
  annotations added in this pass.
- `bin/simple check src/compiler/70.backend/linker/__init__.spl` (which
  transitively includes `symbol_analysis.spl`) passes cleanly (warnings only,
  no error) — the failure is specific to invoking `check` with
  `symbol_analysis.spl` as the direct target file, which appears to pull a
  different/larger transitive module set than checking via `__init__.spl`.
- `arm_body` is a local variable name used in match-arm parsing in
  `src/compiler/10.frontend/core/parser_stmts.spl` (e.g. `val arm_body = parse_block()`
  around lines 861-967) — nothing in `symbol_analysis.spl` references it.
- The functional spec (`test/03_system/compiler/symbol_analysis_spec.spl`)
  passes 1/1, confirming `symbol_analysis.spl`'s actual logic is correct.

## Scope note

Blocks the literal "clean check" acceptance bar for
`symbol_analysis.spl` as a standalone target, but is a pre-existing,
unrelated compiler self-check quirk (likely in how `check <file>` resolves
transitive dependencies for backend/linker-layer files vs. `__init__.spl`
aggregation), not part of the 2026-07-02 "5 lost fixes" restoration.

---

## Resolution (2026-11-25)

status: RESOLVED (parse defect fixed; residual standalone-check limitation is
pre-existing and file-independent)

### Root cause

The original `cannot assign to const 'arm_body'` symptom no longer
reproduces with the current self-hosted binary: `parser_stmts.spl` was
rewritten since 2026-07-02 (the `arm_body` locals are now `case_arm_body`)
and that const-assignment error is gone. The standalone check still failed,
but the current manifestation was a parser defect in the same function
family the bug pointed at — `parse_match_arms_common()` in
`src/compiler/10.frontend/core/parser_stmts.spl`:

1. After `match <scrutinee>:` the parser called `parser_expect(181)`
   (Indent) **unconditionally**. The inline match form
   `match self: case Export: true; case _: false` — used at
   `symbol_analysis.spl:30` and `:33` and accepted by the Rust seed
   (`stmt_parsing/control_flow.rs`, "Inline match") — keeps the first arm on
   the same line as the `:`, so the lexer emits no Indent and the check
   failed with `expected Indent, got case 'case'`, followed by cascading
   errors (`unexpected token in expression: ;`, `expected :, got case`).
2. Even past that, the arm loop had no handling for `;` as an inline arm
   separator, so the `;` fell through to the caseless-arm branch and was
   parsed as the next pattern.

The `__init__.spl` asymmetry described above no longer exists structurally:
`src/compiler/70.backend/linker/__init__.spl` was removed by a later
restructure and no `__init__.spl` references `symbol_analysis.spl` anymore.
The parse failure was file-content-dependent (inline match arms), not
module-set-dependent.

### Fix

`src/compiler/10.frontend/core/parser_stmts.spl`, `parse_match_arms_common()`:

- The Indent after `match …:` is now consumed only when present. When it is
  absent and the next token sits on the **same line** as the `:`, the match
  is parsed as an inline match; a first arm on a *later* line still requires
  the Indent, so the original diagnostic is preserved for genuinely
  un-indented arm blocks.
- The arm loop treats `;` as an inline arm separator and ends the match at
  the first arm not followed by `;` (only `case`/`|` arms may follow a `;`),
  mirroring the Rust seed's inline-match loop. This runs **before** the
  DEDENT check because an inline match opened no Indent of its own — a
  DEDENT there belongs to the enclosing block and must stay unconsumed.

No special-casing of `symbol_analysis.spl`; the fix is in the shared match
parser.

### Evidence

Before (tracked `bin/simple.exe`, this branch):

```
$ SIMPLE_LIB=src bin/simple.exe check src/compiler/70.backend/linker/symbol_analysis.spl
[parser_error] path …/symbol_analysis.spl line 30:21: expected Indent, got case 'case'
[parser_error] line 30:38: unexpected token in expression: ; ';'
[parser_error] path …/symbol_analysis.spl line 30:40: expected :, got case 'case'
(… same triple for line 33 …)
6 error(s) found in 1 of 1 file(s)   → exit 1
```

After:

- Minimal repro `match self: case Export: true; case _: false`:
  before → 3 parse errors; after → `Semantic check passed with complete
  syntax and semantic coverage`, exit 0.
- `symbol_analysis.spl` standalone: parse errors gone; the file now parses
  and reaches HIR lowering, where it fails only on
  `missing module surface for compiler.common.cache.reverse_reference_facts`
  / `unresolved name: reverse_reference_owner_mark_known_v1`. This residual
  failure is **pre-existing and file-independent**: the untouched sibling
  `src/compiler/70.backend/linker/link.spl` fails standalone with the same
  class of errors (`missing module surface for
  std.nogc_sync_mut.io.file_ops`, …). Single-file `check` not loading
  imported module surfaces is a separate limitation of the check driver,
  not this bug.
- Indented match form: still passes.
- `test/01_unit/compiler/parser_inline_match_in_argument_list_spec.spl`
  (interpreter): 9/9 passed.
- `test/01_unit/language/enum_match_dispatch_spec.spl` (interpreter):
  8/8 passed.
- Runtime semantics: a program using both inline-match spellings prints
  `true false true false` as expected.

### Secondary defect note

The "no file/line location" complaint is partly addressed upstream of this
fix: `parser_expect` now prefixes diagnostics with
`path <module> line L:C:` (see `parser.spl`), so the parse errors this bug
produced were located. The duplicate `0:0` summary lines emitted alongside
them come from the non-located `par_record_error` mirror and were left
as-is.
