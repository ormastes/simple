# Workspace diagnostics nested-process overhead

## Status

Open. Static process-topology evidence only; execution measurement was not run
under the user's no-verify instruction.

## Observed path

For each of `N` discovered files, workspace JSON calls `_run_query_check_json`,
which starts `simple run ... query check`; that query starts `_run_simple_check`.
The active path therefore has `2N` explicit per-file process launches, versus
`N` for workspace text output. It also builds, captures, scans, and slices an
intermediate MCP diagnostic wrapper once per file.

## Rejected shortcut

Running `_emit_source_lint_diagnostics` directly in the workspace parent was
rejected in static parallel review:

- `SIMPLE_TRACE_AST_RESET=1` formerly made parser initialization print into
  stdout. Silent/structured scopes now suppress optional frontend trace output,
  with ordinary traced parsing retained as a positive control.
- lint owns private `_LINT_TIER_ACTIVE` state in addition to common diagnostic
  collection and severity globals; restoring only common globals changes caller
  state.
- source-shape tests cannot prove cross-file isolation, exact envelope bytes,
  suppression, ordering, duplicates, or exit behavior.

## Required fix

1. Optional parser/AST traces now have a structured-scope suppression owner.
   Convert always-on safety-containment output into structured failure evidence.
2. Collection, severity, and tier activation now have a lint-owned nested-safe
   snapshot/restore boundary. Move parser/AST reset and failure cleanup behind
   request-owned state before workspace integration.
3. Keep execution serial until parser/lexer/AST globals are request-owned.
4. Add byte-for-byte standalone/session parity and sibling-contamination fixtures.
5. Measure the same 50- and 200-file fixtures before/after: explicit/descendant
   process counts, cold/warm p50/p95, and peak RSS.

## Acceptance

Zero per-file subprocesses; unchanged file/diagnostic order, duplicates,
clean-file omission, lint-profile behavior, totals, JSON bytes, and exit status;
no trace stdout; no cross-file state contamination; peak RSS no more than 10%
above baseline.
