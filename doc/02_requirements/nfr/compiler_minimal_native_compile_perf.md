# Minimal Native-Compile Performance NFRs

- **NFR-CMNCP-001 — Reproducibility.** The report binds compiler path and
  SHA-256, fixture path, run count, thresholds, and artifact SHA-256.
- **NFR-CMNCP-002 — Bounded execution.** Version probe, compile, and artifact
  execution use the configured timeout; the campaign has exactly five samples.
- **NFR-CMNCP-003 — Fail-closed evidence.** Missing tools, receipt, baseline,
  fixture, work directory, measurement values, or artifact proof produces
  `blocked` or `fail`, never a synthetic passing row.
