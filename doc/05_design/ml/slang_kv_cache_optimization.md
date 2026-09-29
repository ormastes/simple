<!-- codex-design -->
# Slang KV cache optimization detail design

Date: 2026-09-09

## Interfaces

- Extend `KvPageTelemetry` with `committed_prefix_restores`, `reused_tokens`,
  `prefilled_tokens`, `boundary_evaluations`, `copied_tail_rows`, and generation
  failure counters. Saturate counters at `u64` maximum.
- Add manager mutations that record committed work only after both provider and
  logical publication succeed.
- Replace whole-prompt `find_prefix` dispatch in `paged_executor_generate` with
  `find_longest_prefix`, returning a private restoration plan containing prefix
  length and page shape.
- Add a mode-tagged engine statistics projection. Existing public generation
  return types remain unchanged.
- Add an opt-in matched CPU context profile to the shim; reject changes while a
  model context, request, or physical pool exists.

## Prefix extension

Full sealed pages are shared. If the retained prefix ends inside a page, copy
only its occupied rows into a newly reserved exclusive page. Add suffix rows to
that page and additional pages as necessary. Empty suffixes use boundary-logit
evaluation; nonempty suffixes start at the retained token count. Commit updates
cursor, logits, rows, logical references, and counters together. Abort releases
new pages and preserves the old cached prefix.

## Errors

Invalid token identity, namespace mismatch, insufficient headroom, stale page,
provider failure, or cleanup failure returns the existing typed executor error.
No request is replayed through snapshot mode after physical evaluation starts.

## Benchmark

Each fresh process runs one mode/workload, emits a textual receipt, and exits
only after cleanup. A producer alternates mode order across five repetitions and
publishes raw samples plus median/range. It records TTFT only after the first
emitted token and uses actual produced-token count for throughput.
