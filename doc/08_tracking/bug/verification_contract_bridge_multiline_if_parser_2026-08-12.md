# Pure-Simple parser rejects multiline if-expressions in FV2 contract bridge

**Status:** OPEN (unverified 2026-09-12)

Date: 2026-08-12

## Reproduction

The FV2 bridge used a multiline expression-bodied conditional:

```simple
val outcome = if retained.outcome == HirContractOutcome.Result:
    VerificationContractOutcomeV1.Result
else:
    VerificationContractOutcomeV1.Plain
```

The same grammar shape occurs in the adjacent region-effect owner (`val
candidate = if effect.access == ...:`). When the compiler import graph reaches
these owners through the mailbox/transfer verification specs, the Rust seed
reports `Unexpected token: expected pattern, found Else`; the self-hosted
parser has the same grammar restriction. This is parser syntax debt, not a
contract semantic failure.

## Fix

`verification_contract_bridge.spl` now uses a mutable local plus an explicit
`if` statement for `outcome`. This preserves the exact result mapping while
avoiding the unsupported multiline conditional expression form.

The adjacent `verification_region_effects.spl` occurrence remains a separate
owner and should receive the same normalization before claiming an end-to-end
mailbox/transfer verification pass.

## Focused evidence

`bin/simple check src/compiler/50.mir/verification_contract_bridge.spl` parses
the bridge after the normalization. A mailbox spec currently reaches the
adjacent pre-existing blocker in `verification_region_effects.spl` first:
`Unexpected token: expected pattern, found Else`.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule D: filed after 2026-07-29, no runnable repro in the record); left open with a status line added since none existed. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification.
