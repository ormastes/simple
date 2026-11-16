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

## Addendum 2026-11-17 — root cause + fix (verification-pending)

**Status:** verification-pending (fixed in source; needs a Stage 2 rebuild of
`test_runner_build` / the mcp closure to confirm all 248 sites clear).

Root cause: `bootstrap_fn_param_defaults_register`
(`src/compiler/50.mir/mir_data.spl`, the `if not any_default: ... return`
branch, ~L2971-2993 before the fix) recorded a callee's `[HirParam]` only when
at least one param had a default. 47562a7feaf made `named_call_slots_v1`
(`_MirLowering/named_call_arguments_v1.spl:33-50`) require that row for EVERY
named call in bootstrap mode. So a named argument to a callee with no defaults
(`_config_file_read_text(path: path)`, `env_set(key:, value:)`,
`parse_dotenv(content:)`, `run_tests_parallel_mode(...)`) always missed. No
codemod is needed.

Fix: register params for every function. Ambiguity and owner checks are
unchanged. The trailing-default pad (`switch_operators_calls.spl`) already
refuses to pad a missing non-default param, so a row for a no-default fn adds
no padding. The 47562a7feaf gate and misbind fix stay as they are. Binding by
position on a miss was rejected because named args may be reordered
(`f(value: v, key: k)`).

Spec: `test/01_unit/compiler/mir/named_call_bootstrap_metadata_spec.spl`
(fails 0/2 before the fix with the exact production error, passes 2/2 after);
`call_argument_slots_v1_spec.spl` 4/4.
