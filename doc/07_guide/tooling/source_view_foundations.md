# Bounded source-view route

The authored `source_open` handler supports explicit `mode: raw`, a workspace-relative `path`, optional `start_byte`, `max_bytes` (default 4096, maximum 8192) and `snapshot_id`. It reads a regular UTF-8 disk file of at most 1 MiB. Successful output carries original source text, selected/omitted byte ranges, full-content snapshot identity and the next whole-line byte offset. Send the returned identity with every continuation; changed content yields `stale`.

Default outline mode currently returns `unsupported`. A large single line produces `source_line_exceeds_budget`; increase the budget within the ceiling. If escaped output exceeds the 16 KiB complete-response ceiling, reduce the source budget. Raw content is encoded as JSON data; do not recover source by stripping decorations from displayed output.

This route does not run diagnostics or compiler processes. It does not read unsaved editor overlays, provide authenticated agent sessions, retain historical snapshots, guarantee race-proof path confinement, or supply language semantics. These limits are included in successful responses. Existing `simple_read` remains a separate legacy diagnostic route.

Deployment status: source authored on the release lane, but no admitted pure-Simple full CLI was available for runtime verification on 2026-11-06. Do not claim the installed MCP binary exposes this capability until rebuilt admission and real protocol smoke pass. The unit session-transition library is not an authenticated production session host.

Full requirements remain in the selected plan. See `doc/08_tracking/bug/source_view_foundation_admission_2026-11-06.md` for the outstanding gates.
