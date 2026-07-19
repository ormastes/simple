# `simple fix` failed-write false-green

**Status:** SOURCE FIXED / STAGE 4 QUALIFICATION PENDING  
**Severity:** P1 — a failed persistence was reported as an applied fix

## Root cause

`FixApplicator.apply_to_disk` ignored the Boolean result from delete-first
`file_write`, added the path to `modified_files`, and returned `Ok`. All CLI
adapters therefore printed success and exited zero after a denied write.

## Solution

The shared applicator now uses the existing canonical `file_atomic_write` and
returns `Err` before recording success when persistence fails. Dry-run behavior
is unchanged.

## Evidence

- deterministic directory-as-file regression reaches the real applicator: PASS
- failed write returns `Err` and preserves the destination directory: PASS
- focused source checks for the regression and applicator: PASS
- compiler, lib, MCP, and LSP MCP source checks: PASS
- source-runner MCP stdio integration on the bootstrap seed: 3 examples,
  0 failures, exit 0 after the automatic-docgen hang was fixed
- admitted self-hosted Stage 4 evidence: pending

## Remaining sibling

Formatter `--write` checks failure but still uses delete-first `file_write`.
Route it through the same atomic provider in a separate bounded item.
