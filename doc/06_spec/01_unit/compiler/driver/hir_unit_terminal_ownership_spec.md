# HIR unit terminal ownership

Status: native before/after regression PASS; integration and SSpec gates pending.
This is a hand-written evidence record, not canonical SSpec/docgen output.

Requirements: REQ-HIR-UNIT-001 (unit post-load receipt ownership),
REQ-HIR-UNIT-002 (strict normal-shard ownership).

Executable specifications:
`test/01_unit/compiler/driver/hir_unit_terminal_ownership_spec.spl` (five cases)
and `test/fixtures/compiler/hir_unit_terminal/main.spl` (17 native assertions).
The SSpec runner has not executed these cases yet.

The native fixture uses real files and the production claim/terminal publisher.
It establishes actual owned claims, compares exact terminal bytes, checks the
absence of fabricated dependency receipts, and exercises identical and
conflicting completion. Failure of claim setup invalidates an ownership proof.

Pinned diagnostic producer:
`ffe83fd87c69573a1ca93e24134e46bbe754be7dff2de2f0eeefc4cf60c9037a`.
Its normal per-file Cranelift Hello build and execution passed. It remains an
unadmitted producer, and this fixture uses the explicit whole-program diagnostic
route to avoid the per-file orchestration defect under investigation.

Before: `build/hir-unit-terminal/before-mirgen2/results.sdn` records build exit0,
fixture exit3, all17 assertions executed, and exactly the three predicted unit
post-load failures. All14 controls passed; both guarded processes quiesced.

After: `build/hir-unit-terminal/after-mirgen2/results.sdn` records build exit0,
fixture exit0, 17 assertions and zero failures. All14 controls remain passing.
Build peak RSS was 2,895,044KiB; run peak RSS 9,040KiB; both guards quiesced.
Native artifact SHA256:
`6a21d02ed3ec650ebb1ca64999ed316fd5f03350a64cd59b745512e9f9c2f5eb`.

Pending: full streaming CLI integration; compiler/lib/MCP/
LSP checks and native smokes; canonical SSpec runner and documentation generation.
No Phase3 or release admission is claimed.
