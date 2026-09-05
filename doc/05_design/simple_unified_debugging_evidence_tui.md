<!-- codex-design -->
# Simple Unified Debugging — Minimal TUI Design

**Status:** CLI/TUI baseline
**Date:** 2026-08-14

The default interface is stable text suitable for humans and capture tests;
`--format sdn` provides typed automation output.

```text
$ simple debug doctor firmware.sdn
PROFILE  firmware.sdn                 RESULT  BLOCKED (1 required)
TARGET          CAPABILITY   SUPPORT      VERIFIED         PERTURBATION  DETAIL
board/core0     dump         Native       LiveVerified     Passive       build …a91
board/core0     watch        Native       LiveVerified     Stopping      4 slots
board/core0     source-step  Native       Blocked          Stopping      T32 unreachable
sqlite/main     query-plan   Unavailable  Unverified       Passive       not configured

Policy: production-observe-only   Tools: OpenOCD 0.12, T32 blocked
Evidence: build/debug-doctor/2026-08-14T…/doctor.sdn
```

Columns never disappear for blocked/unavailable rows and color is never the
sole signal. Long detail is folded; stable target/capability names remain
machine-readable. Secrets and bind values render as `[redacted:<class>]`.

`simple debug inspect <bundle>` shows manifest/build integrity, raw/normalized
artifact counts, receipts, target graph summary and resolution state. `probe
list` includes probe ID, target, kind, perturbation, TTL, policy and cleanup
state. Apply/remove commands print their receipt ID.

System captures write plain/ANSI output beneath
`build/test-artifacts/03_system/app/debug/simple_unified_debugging_evidence_spec/`.
