# Production `simple lint` omits semantic AST rules

- **Status:** OPEN; confirmed while repairing query diagnostics.
- **Observed:** the CLI `Linter` registers ARG/STUB codes but its `lint_source` path only executes line/source and EasyFix checks. A zero-parameter default-return function can exit clean without STUB002.
- **Cause:** production lint and query diagnostics use different adapters over the shared `compiler.semantics.lint.*` leaves; neither adapter was a whole shared owner.
- **Required fix:** parse once in `Linter.lint_source`, invoke the semantic leaf checks, translate warnings to configured `LintResult` values, and add a narrow CLI/query code-parity regression. Do not import app/query code into the compiler lint layer.
