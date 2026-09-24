# Theme snapshot catalog hard stop — TLDR
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Status: open and fail-closed; three review cycles are exhausted.
- Rejected commits: `9f9a921689`, `d404042bc4`, `7ed0ae0a1a`.
- Registry aliases/defaults, full tuple keys, deterministic generation,
  generated-default boot, and resolver closure checks were candidate-only.
- Final blockers: existing non-default active snapshots bypass catalog parity,
  and external-frame authorization is not revalidated after active-theme
  changes.
- Resume from current `origin/main`; do not cherry-pick the series piecemeal.
- No runtime, entry-closure, pixel, event, timing, or RSS PASS exists.

```text
registry/catalog -> active snapshot validation -> current frame authority
stale active or stale registration -> reject
```

