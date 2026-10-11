# Exercise the actual bounded worktree provider

Authored manual companion to traceability_provider_spec.spl, not generated or
renderer-qualified output. Source-stage details: doc/09_report/traceability_cli_tdd_2026-10-11.md.

1. Capture oversized configuration before resolving a missing selector; require
   incomplete typed SDN with infrastructure exit2.
2. Enumerate a directory with an actual symbolic file; require refusal.
3. Read an actual malformed UTF-8 file; require refusal.
4. Select an actual Unicode/newline/marker-like filename; preserve the selector
   and completed structural scope, qualification=incomplete.
5. Capture unchanged inputs twice; compare exact stdout. Change same-path content
   at the same cwd; require a changed captured-input identity.
6. Check fixed SHA256 empty/abc vectors and chunked a+bc digest.

Actual native results: old command6/5; current command6/0. Harness uses exclusively
owned Linux fixtures and GNU env for child cwd. File setup/type/hash artifacts
remain part of evidence; broad error codes alone do not prove precise failure
cause. Direct Unicode selection does not establish find's Unicode transport.
Full20/40 acceptance, historical source admission and broad runtime remain open.
