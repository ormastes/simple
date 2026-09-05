# Stage 2 rejects stale and ambiguous bare variant owners

- **Status:** FIXED
- **Owner:** `codex-stage4-bootstrap-close`
- **Found:** 2026-08-02, incremental-unlimited cycle 2
- **Area:** pure-Simple compiler sources

## Exact reproduction

The fresh Rust authority completed, then Stage 2 rejected six files. The group
had three pure-source mechanisms: `Unit` and `Ret` were stale spellings for
`HirExprKind.UnitLit` and `LocalKind.Return`; the backend `CodegenTarget` omitted
both macOS variants used by native consumers; and bare `PatternKind.Wildcard`
was ambiguous in the global bare-name registry.

## Fix and adjacent family

Fix the pure owners first: use the current variants, add both macOS targets to
the backend enum, and qualify every `Wildcard` arm in the two reported pattern
consumers. The regression covers each exact spelling and its adjacent paired
case so a one-off replacement cannot satisfy it.
