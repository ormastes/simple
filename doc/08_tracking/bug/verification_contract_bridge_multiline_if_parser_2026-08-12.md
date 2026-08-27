# Pure-Simple parser rejects multiline if-expressions in FV2 contract bridge

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
