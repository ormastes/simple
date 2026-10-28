# Shared scheduling constraints

- Retain existing process/worker/RSS admission bounds and finite deadlines;
  sharing must not introduce the fiber scheduler's soft-budget over-admission.
- Keep bounded stdout/stderr capture (4 MiB per stream), including head/tail
  and omission markers, and preserve descendant cleanup evidence.
- Retain deterministic manifest-order reporting despite completion order.
- Keep test dispatch incremental; avoid adding a full inventory rescan for
  every spawn to the current cursor-based path. Measure any changed hot path.
- Do not change OS-specific behavior in app leaves; use existing shared I/O.
- New performance targets are not claimed. Compare applicable existing gates
  and record any regression rather than declaring an unmeasured speedup.
