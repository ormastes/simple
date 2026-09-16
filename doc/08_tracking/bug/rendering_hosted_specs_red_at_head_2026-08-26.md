# Rendering/hosted specs red at HEAD on the test-runner interpreter lane

- Date: 2026-08-26
- Found via: sspec modernization dual-check sampling of bulk TRC-003 comment edits.

## Specs
- `test/02_integration/os/hosted/hosted_external_web_frame_spec.spl` — `Results: 4 total, 1 passed, 3 failed`
- `test/02_integration/rendering/browser_session_dom_input_spec.spl` — `Results: 25 total, 1 passed, 24 failed`

## Proof pre-existing
`hosted_external_web_frame_spec` restored to its `HEAD` version in place reproduces the
identical `1 passed, 3 failed` — failures are not caused by the sspec modernization
comment-only edits (`# @req` binding comments).

## Status
Left RED per testing rules (correct specs failing document real defects). Same family as
`scv_spec_interpreter_file_rename_recursion_2026-08-26.md` — interpreter test-lane
divergence vs the JIT path. Unblock: investigate the interpreter failures for these two
spec families.
