# Simple Build/Test Abnormality Detection — NFR Requirements

- NFR-001 Trust: no inferred OOM/timeout verdict from exit code alone; every proven verdict names its evidence source and quality.
- NFR-002 Safety: a hard scope always protects CI independently of baseline availability; every kill/wait path rejects `pid <= 0`.
- NFR-003 Compatibility: existing stable test identities remain readable and volatile observations live in append-oriented run records.
- NFR-004 Determinism: identical normalized semantic inputs produce the same cohort identity regardless of map iteration order; aspect order remains significant.
- NFR-005 Baseline integrity: a candidate regression cannot update an approved baseline, including after a failed or interrupted comparison.
- NFR-006 Statistical policy: warning defaults require at least 10%, three MAD, and an absolute floor; failure defaults require at least 15%, four MAD, an absolute floor, and a confirming paired run.
- NFR-007 Overhead: default structured counters are bounded O(1) per event and traces are hierarchical summaries; large time series/profiles are stored externally by digest.
- NFR-008 Portability: unsupported exact-tree metrics degrade explicitly to a named evidence quality rather than fabricating parity.
- NFR-009 Diagnostics: every decision explains cohort match, baseline state, thresholds, observed deltas, missing evidence, and the first unavailable enforcement/measurement rung.
- NFR-010 Convergence: a single feature verification session runs each acceptance gate once and stops after at most three fix/verify cycles.
