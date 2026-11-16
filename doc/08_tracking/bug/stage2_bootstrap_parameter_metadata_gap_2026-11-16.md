# c32-generation stage2 candidate requires "bootstrap parameter metadata" on named calls — 248 sites fail in the mcp closure alone (2026-11-16)

**Status:** OPEN (systematic candidate requirement; the lanes that introduced
the metadata check must fill it tree-wide or relax the gate)
**Area:** stage2 candidate MIR lowering, named-call bootstrap metadata
**Evidence:** cycle-32 stage2 admission at 9ec110323b4 built clean (FreeBytes
struct fix #9847 unblocked the seed). Rebuilding the mcp tool with the c32
candidate against the pinned tree fails with, per the build log:

- 248 x `MIR lowering error: named call lacks bootstrap parameter metadata: app.*` (195) / `lib.*` (53)
- 2 x `missing native trait implementation: compiler.*`
- 2 x `enum construction: unregistered declaration`
- plus the pre-existing `app.mcp.ctx_postings` ptr-to-double AOT failure
  persists (6 mentions; #9813 fixed the multi-field VARIANT payload class,
  not this list-of-struct iteration shape — see the 6-experiment matrix in
  frozen_phase2_parity_instances_round2_2026-11-16.md).

## Why this is filed as systematic, not per-site

The c29-generation candidate (pinned-c189f67185e1) built the same closure
with ZERO metadata errors after #9735/#9770/#9803; the c32 generation adds a
named-call bootstrap-parameter-metadata gate that hundreds of call sites do
not yet satisfy. Whack-a-mole per site is not viable at this scale; the gate
needs either (a) a tree-wide metadata fill from the lane that introduced the
requirement, or (b) a relaxation/transition mode for closures built from
pre-metadata sources.

## Impact

- The stage2-built mcp server binary is gated on both this metadata fill and
  the ctx_postings AOT fix.
- The phase-3 full-run matrix at c32-generation tips will hit the same wall
  in every tool row (the CLI closure will carry hundreds more instances), so
  the receipt-authorized full run is also gated.
- The deployed bin/release set (test_runner, simple_lsp_mcp_server,
  simple_plugin — all c29-generation, lineage-recorded) is unaffected.

## Owner asks

1. Identify the commit range that introduced the named-call
   bootstrap-parameter-metadata requirement and either fill the metadata
   tree-wide (codemod) or gate it behind an opt-in for frozen closures.
2. Extend #9813's ptr<->float coverage to the ctx_postings iteration shape
   (residual construct set recorded in the round-2 parity doc).
