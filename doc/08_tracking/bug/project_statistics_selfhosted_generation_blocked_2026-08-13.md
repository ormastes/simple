# Project statistics self-hosted generation blocked

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

## Re-verification 2026-08-17 (app-rest lane) — closeable as a deploy blocker

This doc's own Status already reads "Resolved for report generation". The only
residual is that `bin/simple stats` refuses because the deployed binary
self-identifies as the Rust seed. That is a DEPLOY blocker, not a code defect
in `src/app/stats/db_aggregator.spl` — no defect text was found in that file.
Verdict: not a silent-wrong-result bug; reclassify as blocked-on-deploy.
