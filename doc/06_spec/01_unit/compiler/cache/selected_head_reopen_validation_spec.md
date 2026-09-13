# Selected-head reopen validation

Source: `test/01_unit/compiler/cache/selected_head_reopen_validation_spec.spl`.

Status: executable unit contract; branch coverage is unmeasured until the
successor runtime is admitted. No physical host authority is fabricated.

The suite covers canonical envelope round trips and refusal boundaries,
including missing delimiters, bad magic, negative/noncanonical/oversized
lengths, nested selected-head decode failure, invalid expected/live writers,
rejected-before-replacement precedence, operation/closure/verifier identity,
short or digest-mismatched prefixes, ActionRootJournal recovery failure, torn
suffix handling, and confirmed-but-unsynced indeterminacy.

Review guide: verify `Selected`, `RejectedBeforeHeadReplacement`,
`MalformedInput`, `InvalidSelectedPrefix`, `StaleWriter`, `StaleDescriptor`,
`OperationMismatch`, `ClosureMismatch`, `InvalidDurabilityTrace`, and
`Indeterminate` are asserted from production APIs. Do not count source scans,
coverage tags, or unavailable physical-provider rows as execution evidence.
