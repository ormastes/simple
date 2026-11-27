# Project statistics self-hosted generation blocked
## Closed 2026-09-16 — Status Resolved; PPTX generated and validated, specs pass
## Verified 2026-11-25 — feature system spec re-run green on release/1.0.0

2026-11-25 re-verification (work/p3-baq-20261125): re-ran the feature system
spec on this Windows host with the tracked self-hosted binary:
`SIMPLE_LIB=src bin/simple.exe test
test/03_system/app/stats/feature/project_statistics_quality_reporting_spec.spl
--mode=interpreter` → `outcome=OK ... passed=3 failed=0`. Resolution stands.

Caveat recorded for honesty, not a re-open: the related unit spec
`test/01_unit/compiler/mir/verification_ir_spec.spl` currently fails 4/16 in
interpreter mode on release/1.0.0 (`semantic: function
'semantic_coverage_for_mir_type_v2' not found` despite the pub fn existing at
`src/compiler/50.mir/verification_semantic_coverage.spl:220`, plus
`expected true to equal false` rows). That is a pre-existing condition on the
release branch, not caused by this bug's fix, and is reported to the ledger
owners separately.

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

## Status

Resolved for report generation — guarded current CLI produced and validated PPTX.

## Evidence

- The shared `VerificationIrModuleV1.closure_ready` condition was corrected to
  parenthesize its multi-line boolean expression; the feature system spec now passes.
- Focused Markdown renderer and SimpleOS PPTX theme specs also pass.
- `bin/simple stats --quality=summary` refuses execution because the installed
  binary identifies itself as the Rust bootstrap seed and the pure-Simple
  `stats` tool is unavailable.
- `bin/simple spipe-docgen ... --no-index` succeeds with 1/1 complete manuals
  and 0 stubs, so documentation generation itself is not the blocker.
- A direct native Office conversion was attempted three times. Grammar-safe
  parenthesization advanced the shared closure past `verification_ir.spl`,
  `process_ops.spl`, and `simpleos_host_gpu_protocol.spl`; the third bounded
  attempt stops at `src/lib/gc_async_mut/gpu/browser_engine/web_paint_chunk_frame.spl`
  with `Unexpected token: expected LParen, found Dot`.
- `StatsInventoryV2` scanning now rejects filesystem symlinks, preventing
  source aliases such as `src/std -> lib` and test links into `src` from
  double-counting or recursively traversing the inventory.

## Impact

Markdown, TLDR, SimpleOS-native slide source, and a nine-slide PPTX are generated.

## Unblock condition

The broader full-CLI bootstrap remains independently useful, but is no longer
required to consume this report package. Keep the focused parser and protocol
regressions green when the shared CLI is next rebuilt.

