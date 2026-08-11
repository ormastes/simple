# Office CLI and Calc TUI UI Access NFRs

Selected profile: **N1 — Balanced Local Tooling**.

## NFR-OFFICE-CLI-UI-001 — Runtime provenance

The product under test shall be `OFFICE_BINARY`, a native standalone Office
artifact built by a Phase-3 self-host compiler. `SIMPLE_TEST_DRIVER` may execute
SSpec/check orchestration and a separately cached UI client may speak
`simple.access/v1`; neither is part of the Office application closure. Raw-source,
Rust-seed, and full-Simple-CLI launch fallbacks are prohibited for product
acceptance.

## NFR-OFFICE-CLI-UI-002 — Startup

Warm deployed Calc launch shall expose a ready semantic surface within
2 seconds on the checked-in realistic fixture and primary development host.

## NFR-OFFICE-CLI-UI-003 — Query latency

On the same fixture:

- warm `windows`/`snapshot` p95 shall be at most 100 ms;
- warm `find` p95 shall be at most 25 ms.

## NFR-OFFICE-CLI-UI-004 — Action latency

A semantic edit action plus independently observed post-state shall complete at
p95 within 250 ms.

## NFR-OFFICE-CLI-UI-005 — Bounded resources

Access history shall be bounded to 64 events per active surface/session. The
access-layer RSS delta shall be at most 20 MiB on the measurement fixture.
Hot request paths shall contain no retry sleeps, subprocess calls, or repeated
full-tree scans.

RSS is measured from the launched `OFFICE_BINARY`. Building that artifact may
use an existing Phase-3 compiler; it does not require producing or deploying a
full Simple CLI.

## NFR-OFFICE-CLI-UI-006 — Deterministic evidence

The retained TUI text capture shall preserve Calc's established 20-column by
30-row sheet viewport in a fixed 124-column by 37-row terminal frame.
Protocol artifacts shall use deterministic `simple.access/v1` envelopes and
stable canonical IDs.

## NFR-OFFICE-CLI-UI-007 — Safety and restoration

Terminal mode shall be restored after normal exit and error exit. Operator
actions shall use structured argv/value fields rather than shell-string
construction. Stale revisions, missing targets, unsupported actions, and
malformed formulas shall fail closed.

## NFR-OFFICE-CLI-UI-008 — Architecture hygiene

The production Calc closure shall contain no compiler, unified CLI,
SGTTI/test-only import, or new dependency cycle. New imports shall use narrow
owner modules rather than broad re-export hubs.

## NFR-OFFICE-CLI-UI-009 — Verification quality

Focused formula, CLI, semantic access, and system specs shall use real
assertions and execute once after convergence. The UI evidence audit,
runtime-facade audits, CLI help checks, generated-manual checks, and generated
spec layout check shall pass without placeholders.

## NFR-OFFICE-CLI-UI-010 — Manual quality

Docgen shall report zero stubs. The mirrored manual shall be usable without
opening source code, and `doc/06_spec` shall contain no executable `.spl` file.
