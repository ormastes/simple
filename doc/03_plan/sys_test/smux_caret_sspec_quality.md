# System Test Plan — smux and LLM Caret SSpec Quality

**Date:** 2026-08-16
**Lane:** smux + LLM Caret SSpec quality
**Executable spec:** `test/03_system/tools/smux_caret_sspec_quality_system_spec.spl`
**Manual:** `doc/06_spec/03_system/tools/smux_caret_sspec_quality_system_spec.md`
**Status:** spec complete and fail-closed; admitted execution `TEST_BLOCKED`
(seed-observed 13/13, not acceptance evidence)

## Problem

A legacy `fn test_*` + `print("PASS: ...")` spec executes zero examples. The
fail-closed zero-examples gate holds it permanently RED while its own prints
claim success, and a `FAIL` print never fails the process — so the checks were
never oracles. Two smux specs were in exactly that state (recorded in
`doc/08_tracking/bug/smux_legacy_specs_zero_examples_red_2026-08-16.md`, now
resolved); the LLM Caret lane was already converted upstream.

Nothing prevented a regression back to the print-based pattern, and nothing
asserted the two duplicate test trees stay identical. This plan adds that
system-level guard.

## Scope

In scope — asserted from committed sources:

- smux unit specs (`test/01_unit/os/smux_spec.spl`,
  `test/01_unit/os/smux/smux_dashboard_spec.spl`) are Modern SSpec.
- Their `test/unit/` mirrors are byte-identical **and** independently modern.
- An LLM Caret unit spec carries oracles, not prints.
- The classifier is proven to discriminate before it is trusted.

Out of scope:

- Converting `test/03_system/tools/smux_system_spec.spl` (858 lines, 56
  `fn test_*`), which is still legacy. Tracked separately; this plan does not
  claim it.
- Any runtime behaviour of smux itself. This lane is about spec quality.

## Requirements

| ID | Statement | Verified by |
|---|---|---|
| REQ-SSQ-001 | The classifier distinguishes Modern SSpec from legacy print-based sources. | SSQ-CLS-001 |
| REQ-SSQ-002 | The classifier rejects empty, oracle-free and missing sources rather than passing vacuously. | SSQ-CLS-002 |
| REQ-SSQ-003 | smux and LLM Caret unit specs are Modern SSpec with no surviving legacy construct. | SSQ-SMUX-001, SSQ-CARET-001 |
| REQ-SSQ-004 | The smux dashboard unit spec is Modern SSpec with no surviving legacy construct. | SSQ-SMUX-002 |
| REQ-SSQ-005 | Duplicate test trees stay byte-identical. | SSQ-MIRROR-001 |
| NFR-SSQ-001 | Neither duplicate tree may regress alone. | SSQ-MIRROR-001 |

## Fail-closed design

The spec must fail, not skip, on absent evidence:

1. **Missing file is a failure.** `classify_spec_file` returns `present=false`
   for an absent path, and `is_modern()` returns `false` whenever `present` is
   false. The assertion then fails.
2. **Non-vacuous oracle.** The classifier is exercised against a synthetic
   legacy source (must classify legacy), a synthetic modern source (must
   classify modern), an empty source and an oracle-free source (both must be
   rejected) *before* any real file is judged. A classifier that returned
   `true` unconditionally would fail SSQ-CLS-001.
3. **No placeholder passes.** No example asserts a tautology, and no scenario is
   marked pass on the basis of unavailable evidence.

## Execution

```
bin/simple test test/03_system/tools/smux_caret_sspec_quality_system_spec.spl
```

Expected once a qualified runner is admitted:
`declared>=13 executed=13 passed=13 failed=0 dropped=0` — which is exactly what
the non-admitted seed runner already reports.

## TEST_BLOCKED

`TEST_BLOCKED` for admitted evidence. The spec **does execute and pass** —
observed `declared>=13 executed=13 passed=13 failed=0 dropped=0` — but that run
came from `bin/release/x86_64-unknown-linux-gnu/simple`, which self-identifies
as the Rust bootstrap seed and is **not an admitted pure-Simple runner**. The
run is recorded as a development observation, not as acceptance evidence, and
the lane is not marked green on it.

Why no admitted runner exists here:

- the tracked self-hosted `release/x86_64-unknown-linux-gnu/simple` segfaults in
  its `test` subcommand (exit 139, no output)
- `bootstrap/stage1|2|3/simple` expose no `test` subcommand, and cannot lower the
  SSpec DSL (`unresolved name: describe / it / expect`)
- `build bootstrap` terminates inside Stage 1 without a verdict, so the
  documented recovery path is itself blocked

Upstream record:
`doc/08_tracking/bug/deployed_selfhost_test_subcommand_segv_blocks_bootstrap_2026-08-16.md`.
`spipe-docgen` and `sspec-maintain scan` were likewise not run. No placeholder
pass is recorded anywhere in this lane.

**Resume condition:** admit a pure-Simple CLI, then re-run the command above plus
`simple spipe-docgen` (to regenerate the manual) and `simple sspec-maintain scan`
(to score the spec). Replace this section with the resulting verdict lines; do
not mark it green from any seed-produced run.
