# Production `simple lint` omits semantic AST rules

- **Status:** PARTIALLY FIXED / STAGE 4 QUALIFICATION PENDING.
- **Observed:** the CLI `Linter` registers ARG/STUB codes but its `lint_source` path only executes line/source and EasyFix checks. A zero-parameter default-return function can exit clean without STUB002.
- **Cause:** production lint and query diagnostics use different adapters over the shared `compiler.semantics.lint.*` leaves; neither adapter was a whole shared owner.
- **Implemented slice:** the CLI-owned lint path parses once and translates
  ARG001/ARG002, COLL001-COLL008, and STUB001/STUB002 into configured `LintResult` values with
  parser-backed source lines, and runs W0404 through its file-aware checker as
  one module-level line-1 result with `visibility_boundary` configuration and
  facade suppression. The generic `pass_todo` check stays the STUB003
  owner so that placeholder is emitted once. Generic in-process
  `Linter.lint_source` remains parser-free because parsing resets shared
  compiler AST state. The unified CLI fallback uses that same canonical
  lint-command owner. The existing EasyFix rule remains the sole public DTYP
  owner, while the query/LSP semantic leaf now ignores named calls.
- **Remaining fix:** route wildcard-import/export semantic leaves through the
  CLI-owned parsed adapter, then qualify the exact fresh Stage 4 binary.
