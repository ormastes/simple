<!-- codex-research -->
# Dangerous Comment Grammar NFR Options

Date: 2026-04-23

## Option 1: Warning-Only Migration Gate

Targets:

- New lints run under `bin/simple lint <path>`.
- No more than 5% runtime increase for linting a representative compiler file.
- Diagnostics include code, construct, site, and actionable hint.
- Existing code continues compiling.

Pros:

- Safe migration path.
- Easy to adopt incrementally.

Cons:

- Does not prevent new unjustified constructs unless CI opts in.

Effort: S-M.

## Option 2: Strict Production Gate

Targets:

- Production paths under `src/compiler`, `src/lib`, `src/os`, MCP/LSP tooling,
  drivers, FFI, and backend code deny unjustified dangerous constructs.
- Test/example paths warn unless configured otherwise.
- CI can fail on any new unjustified dangerous construct.

Pros:

- Matches the repo's no-stub and production readiness standards.
- Stops dangerous placeholders from entering critical paths.

Cons:

- Requires migration suppressions or cleanup for existing code.

Effort: M-L.

## Option 3: Performance-Sensitive Lint Gate

Targets:

- Required-comment and wildcard checks reuse parsed AST when available.
- No repeated full-tree scans in hot tooling requests.
- Representative `bin/simple lint src/compiler` RSS and latency recorded before
  and after.

Pros:

- Aligns with MCP/LSP startup and hot-path rules.
- Prevents lint improvements from becoming tooling regressions.

Cons:

- More measurement work before the feature feels done.

Effort: M.

## Option 4: Audit-Quality Rationale Text

Targets:

- Reject rationale strings shorter than 10 meaningful characters.
- Reject weak text such as `todo`, `fix`, `later`, `because`, `unknown`, or
  duplicated construct names.
- For unsafe/raw/unchecked operations, require an `invariant:` phrase.
- For placeholders, require "what remains" and a next-step hint or issue id.

Pros:

- Prevents fake compliance.
- Better for audits and future maintainers.

Cons:

- Can feel strict for small prototypes.
- Needs clear docs and examples.

Effort: M.

## Recommendation

Select Option 1 for initial rollout, plus Option 4 for critical constructs. Add
Option 2 after the codebase warning count is low enough to make strict mode
useful instead of noisy.

