# Feature: markdown-utilities-smf-no-source

## Raw Request
fix all remain bug and feature request and abandon plans.. and in mind pure simple is main rust is just seed. use skill $sp_dev

Tracker: doc/08_tracking/bug/markdown_utilities_smf_no_spl_source_2026-05-30.md

## Task Type
bug

## Refined Goal
Restore Simple source modules for `std.common.markdown.*` so interpreter-mode tests can resolve markdown utilities without relying on SMF-only artifacts.

## Acceptance Criteria
- AC-1: `std.common.markdown.utilities` resolves from `.spl` source in interpreter/test mode.
- AC-2: `test/03_system/editor_markdown_document_decor_spec.spl` no longer fails with `Cannot resolve module: std.common.markdown.utilities`.
- AC-3: Missing markdown source modules are implemented or restored under `src/lib/common/markdown/**`, not handled by skipping tests.
- AC-4: The bug tracker is updated to resolved with focused verification evidence.

## Scope Exclusions
Full Markdown parser CommonMark parity is outside this slice unless required by the affected system test.

## Phase
verified

## Log
- dev: Created state file with 4 acceptance criteria (type: bug).
- implement: Added `.spl` source modules for the `std.common.markdown` compatibility surface.
- verify: `SIMPLE_LIB=/tmp/simple-macro-intro-sync/src /home/ormastes/dev/pub/simple/src/compiler_rust/target/debug/simple check src/lib/common/markdown/utilities.spl src/lib/common/markdown/inline.spl src/lib/common/markdown/block.spl src/lib/common/markdown/parse.spl src/lib/common/markdown/types.spl src/lib/common/markdown/render.spl test/03_system/editor_markdown_document_decor_spec.spl` passed.
- verify: `SIMPLE_LIB=/tmp/simple-macro-intro-sync/src /home/ormastes/dev/pub/simple/src/compiler_rust/target/debug/simple run test/03_system/editor_markdown_document_decor_spec.spl` passed 6 examples.
