---
id: lint_code_impl_indent_parse_error_2026-07-05
Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
severity: low
discovered: 2026-07-05
discovered_by: Stage-4 bootstrap module graph loading diagnostics
related: src/compiler/tools/fix/rules/impl_/lint_code.spl
---

# Lint module: parse error on `impl` block due to Indent token handling

## Summary

The file `src/compiler/tools/fix/rules/impl_/lint_code.spl` at line 253 fails to parse during stage-4 module graph loading with the error:

```
unexpected token in expression: Indent
```

The parse failure is nonfatal (file is skipped during loading) but pollutes bootstrap logs and excludes the module from the build, reducing linting functionality. The root cause is improper handling of the `Indent` token within the `impl` block structure.

## Evidence

- File: `src/compiler/tools/fix/rules/impl_/lint_code.spl`
- Error location: Line 253
- Error message: "unexpected token in expression: Indent"
- Timing: Module graph loading phase during stage-4 bootstrap
- Impact: File skipped, tooling module incomplete
- Severity: Nonfatal (bootstrap continues; linting degraded)

## Impact

The lint rule module is excluded from the build during stage-4 bootstrap. While the bootstrap proceeds successfully, the resulting binary lacks the `lint_code` implementation, reducing the effectiveness of the linting toolchain.

## Scope

Parser error on a specific syntactic construct (likely indentation-sensitive code inside an `impl` block expression). The `Indent` token is being encountered in a context where the parser does not expect it, suggesting either:
- A missing case in the expression parser for indented blocks
- Improper nesting of indent/dedent handling in `impl` contexts
- A comment or string literal being parsed as code due to inadequate delimiter handling

## Next Steps

1. Review the code structure around line 253 of `lint_code.spl` to identify the problematic `impl` block and Indent usage.
2. Verify whether the construct is valid Simple syntax or a genuine code error.
3. If valid, add parser support for the indentation pattern in impl blocks.
4. If invalid, refactor the code to use a supported syntax pattern.
5. Add a regression test to prevent this parse error from reoccurring.

## Verification 2026-08-17 (w02/s4 lane) — occurrence GONE, class NOT proven fixed

Classified by CONTENT of current source (session brief CORRECTION 1).

`src/compiler/tools/fix/rules/impl_/lint_code.spl` (547 lines) now contains
**zero `impl` blocks** (`grep -c '^impl '` = 0) and **22 top-level free
functions** (`grep -c '^fn \|^pub fn '` = 22). The reported failure was
"fails to parse due to Indent token handling in impl blocks"; the file has been
restructured so that it has no impl blocks to mis-indent.

The module is live and reachable, not orphaned: it is imported by
`src/compiler/tools/fix/rules/registry.spl:12` and
`src/compiler/tools/fix/rules/impl_/impl.spl:33`, and re-exported via
`impl_/__init__.spl:25`. A module that failed to parse could not be imported by
a working registry.

**Verdict: this file's occurrence is FIXED (by restructuring). Closing the row.**
**Explicitly NOT proven:** the underlying parser defect — Indent token handling
inside `impl` blocks — is *not* shown to be fixed. This close is a
workaround-close for one file, not a fix of the parser behaviour. If the parser
issue matters independently it needs its own row against the frontend (a lane
claimed by another session; not touched here).
