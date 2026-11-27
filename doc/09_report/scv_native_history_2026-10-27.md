# Native SCV history implementation evidence

Base: explicit fresh `origin/release/1.0.0` at `65055a380bb`.
Worktree: `/tmp/simple-scv-jj-work`, branch `work/scv-jj-work`.
Tests-first commit: `bc9a4c7d3cf` (before history source or CLI edits).

Implemented additive all-parent history and selected logical change ancestry
through the real CLI. The independent guide reviewed cycle/dedup/order,
reference and field admission, budget behavior, CLI scripts, and selected
latest semantics. Review caught a fixture sharing a derived ChangeId; fixture
construction now supplies distinct explicit change IDs and asserts inequality.

Evidence:

- PASS: initial and final staged whitespace checks (`git diff --check` and
  `git diff --cached --check`).
- PASS: working and staged direct environment/process facade guards.
- PASS: executable-spec layout count under `doc/06_spec` is zero.
- Earlier independent `/bin/sh -n` validation covered all three extracted CLI
  scenario scripts; final-content revalidation is pending guide review.
- NOT_RUN: integration/system execution, `check src/compiler`, `check src/lib`,
  MCP/LSP checks and stdio smoke; no admitted `bin/release` runtime is available.
- NOT_RUN: native core/MCP smoke, coverage, performance, SPipe docgen and
  `sspec-maintain`, for the same runtime prerequisite.

The change is implemented and statically reviewed, with runtime qualification
pending. **STATUS: NOT_RUN** for production verification. This report does not
claim release admission. The guide documents loose-only reads, ancestry rather
than rewrite evolution, absent snapshot isolation, and existing restore safety
limitations.
